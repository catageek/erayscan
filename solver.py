from pathfinder import PathFinder
from indirectaddressconstraintbuilder import IndirectAddressConstraintBuilder
from expressions import *
from constraints import *
from opcodes import fake_ops, mem_write_ops
from z3 import *
import z3 as z3lib
import sys



class Block():
    def __init__(self):
        self.timestamp = BitVec('TIMESTAMP', 256)

class Message():
    def __init__(self):
        self.sender = BitVecVal(0xca11a, 256)
        self.value = BitVec('VALUE', 256)
        self.gas = BitVecVal(3000000, 256)

class TargetSolver(PathFinder):
    def __init__(self, binary):
        self.vars = self.__initvars()
        PathFinder.__init__(self, binary)
        self.solver = Solver()
        print("============== Solver ===============")
        for func in self.get_all_functions():
            self.__iterate_targets(func)

    def __initvars(self):
        vars = {}
        vars['self'] = self
        vars['bool_opcodes'] = {
                "LT",
                "GT",
                "SLT",
                "SGT",
                "EQ",
                "ISZERO",
                "NONZERO",
                "CALL"
        } | fake_ops.viewkeys()

        vars['equivalent_opcodes'] = {
                "ASSERT":   ("NONZERO", MonoOpExpression)
        }

        vars['msg'] = Message()
        vars['block'] = Block()
        vars['BALANCE'] = BitVec('BALANCE', 256)
        vars['AD_MASK'] = BitVecVal(0xffffffffffffffffffffffffffffffffffffffff, 256)
        vars['this'] = BitVecVal(0xca11ab1e, 256)
        vars['calldatasize'] = BitVec('CALLDATASIZE', 256)
        vars['target_value'] = 0xca11a
        vars['SHA3'] = Function('SHA3', BitVecSort(512), BitVecSort(256))

        return vars

    def __iterate_targets(self, func):
        for target in self.paths_to_targets[func.signature]:
            print("target %s" % target.expression)
            target.set_target_value_constraint(self.vars['target_value'])
            dominators = target.constraints
            self.rewrite_opcodes(dominators)
            self.static_single_assignment(dominators)
            self.declare_variables(dominators)
            self.constraints = list()
            self.__convert_expressions(dominators)
            for dominator in dominators:
                print("dominator %s" % dominator)
            self.__indirect_address_constraints = IndirectAddressConstraintBuilder(self.constraints, self.vars)
            self.__solve(target)

    def __convert_expressions(self, expressions):
        for expression in expressions:
            constraint = self.__convert_expression(expression)
            self.constraints.append(constraint)

    def __convert_expression(self, expression):
        if isinstance(expression, BinOpExpression):
            new_constraint = BinOpConstraint(expression)
        elif isinstance(expression, MloadExpression):
            new_constraint = MloadConstraint(expression)
        elif isinstance(expression, SstoreExpression):
            new_constraint = SstoreConstraint(expression)
        elif isinstance(expression, MoveExpression):
            new_constraint = MoveConstraint(expression)
        else:
            new_constraint = Constraint(expression)
        for i, read in enumerate(expression.reads):
            if i in expression.dependencies:
                dependency = self.__convert_expression(expression.dependencies[i])
                new_constraint.set_dependency(i, dependency)
        print "%s %s" % (new_constraint, new_constraint.__class__)
        return new_constraint

    def rewrite_opcodes(self, expressions):
        for i, expression in enumerate(expressions):
            opcode = expression.opcode
            if expression.opcode in self.vars['equivalent_opcodes']:
                expressions[i].__class__ = self.vars['equivalent_opcodes'][opcode][1]
                expressions[i].opcode = self.vars['equivalent_opcodes'][opcode][0]

    def static_single_assignment(self, expressions):
        self.__current_names = dict()
        for i, expression in enumerate(expressions):
            self.__static_single_assignment(expression, i)

    def __static_single_assignment(self, expression, index):
        writes = expression.writes
        self.__rename_write_registers(expression)
        for register in writes:
            prefix = register.split("_")[0]
            new_name = "%s_%s_%s" % (prefix, index, hex(expression.address))
            self.__current_names[prefix] = new_name
            print "  old name %s new name %s" % (register,new_name)
        self.__rename_read_registers(expression)
        # unroll MLOAD, CALLDATALOAD or Bool opcodes
        for i, read in enumerate(expression.reads):
            if i in expression.dependencies:
                dependency = expression.dependencies[i]
                if expression.contains_operations({"MLOAD", "CALLDATALOAD"})\
                        or expression.contains_operations(self.vars['bool_opcodes']):
                    self.__static_single_assignment(dependency, index)
                if len(dependency.writes) > 0:
                    expression.reads[i] = dependency.writes[0]

    def __rename_write_registers(self, expression):
        writes = expression.writes
        for index, write in enumerate(writes):
            if write in self.__current_names:
                writes[index] = self.__current_names[write]

    def __rename_read_registers(self, expression):
        reads = expression.reads
        for index, register in enumerate(reads):
            if index in expression.dependencies:
                if not expression.contains_operations({"MLOAD", "CALLDATALOAD"})\
                        and not expression.contains_operations(self.vars['bool_opcodes']):
                    self.__rename_read_registers(expression.dependencies[index])
            else:
                if register in self.__current_names:
                    reads[index] = self.__current_names[register]
                # if we have an immediate value and the operation involves Bool
                if not isinstance(register, str) and self.__has_bool_arguments(expression.reads):
                    # immediate values are converted to True or False
                    reads[index] = (register != 0)

    def __has_bool_arguments(self, reads):
        ret = False
        for read in reads:
            ret |= isinstance(read, BoolRef)
        return ret

    def declare_variables(self, expressions):
        self.__types = dict()
        for expression in reversed(expressions):
            self.__declare_variables(expression)
        for expression in expressions:
            self.__convert_read_bool(expression)
        for key in self.__types:
            keytype = self.__types[key]
            if keytype == "Bool":
                self.vars[key] = eval("Bool('%s')" % key, z3lib.__dict__)
            elif keytype == "BitVec":
                self.vars[key] = eval("BitVec('%s', 256)" % key, z3lib.__dict__)
            #elif keytype == "BitVecVal":
            #    self.vars[key] = eval("BitVecVal(%s, 256)" % key)

    def __declare_variables(self, expression):
        self.__declare_read_variables(expression)
        self.__declare_write_variables(expression)
        for i, read in enumerate(expression.reads):
            if i in expression.dependencies:
                dependency = expression.dependencies[i]
                if expression.contains_operations({"MLOAD", "CALLDATALOAD", "SLOAD", "SHA3"})\
                        or expression.contains_operations(self.vars['bool_opcodes']):
                    self.__declare_variables(dependency)

    def __declare_read_variables(self, expression):
        for index, register in enumerate(expression.reads):
            if index not in expression.dependencies:
                print "Trying to declare %s in expression %s" % (register, expression)
                if isinstance(register, str):
                    self.__declare_variable(expression.format_dependency(index))
                #else:
                #    self.__declare_constant(register)

    def __declare_write_variables(self, expression):
        for write in expression.writes:
            if self.is_bool_opcode(expression):
                self.__declare_bool(write)
                return
            print "expression %s is not bool" % expression
            if expression.opcode == "MOVE" and isinstance(expression.reads[0], str):
                self.__declare_same(write, expression.format_dependency(0))
            elif isinstance(write, str):
                self.__declare_variable(write)


    def __convert_read_bool(self, expression):
        for i, register in enumerate(expression.reads):
            if i not in expression.dependencies:
                if expression.opcode not in self.vars['bool_opcodes'] and isinstance(register, str):
                    if len(expression.writes) != 0:
                        self.__declare_same(expression.format_dependency(i), expression.writes[0], True)
            else:
                dependency = expression.dependencies[i]
                if expression.contains_operations({"MLOAD", "CALLDATALOAD"})\
                        or expression.contains_operations(self.vars['bool_opcodes']):
                    self.__convert_read_bool(expression.dependencies[i])

    def is_bool_opcode(self, expression):
        return expression.opcode in self.vars['bool_opcodes'] and len(expression.writes) != 0

    def __declare_variable(self, name, force = False):
        if name not in self.__types or force:
            print("Creating %s = BitVec('%s', 256)" % (name, name))
            self.__types[name] = "BitVec"
        else:
            print "Failed to create BitVec('%s', 256) : already existing" % name

    def __declare_bool(self, name, force = False):
        if name not in self.__types or force:
            print("Creating %s = Bool('%s')" % (name, name))
            self.__types[name] = "Bool"
        else:
            print "Failed to create Bool('%s') : already existing" % name

    #def __declare_constant(self, value):
    #    key = hex(value)
    #    if key not in self.__types:
    #        print("Creating constant %s" % key)
    #        self.__types[key] = "BitVecVal"

    def __declare_same(self, name, origin, force = False):
        if name not in self.__types or force:
            if self.__types[origin]== "Bool":
                self.__declare_bool(name, force)
            else:
                self.__declare_variable(name, force)

    def __solve(self, target):
        self.solver.push()
        target.debug_target()
        for i in self.__indirect_address_constraints.mem_constraints:
            #print "memory constraints %s" % (self.__indirect_address_constraints.mem_constraints[i])
            pass

        calldata_constraints = self.__indirect_address_constraints.reference_constraints["CALLDATALOAD"]
        for i in calldata_constraints:
            for c in calldata_constraints[i]:
                #print "calldata constraints %s" % (c)
                eval("self.solver.add({})".format(c), z3lib.__dict__, self.vars)

        for constraint in reversed(self.constraints):
            self.__apply_constraints(constraint)

        print("\nAssertions:")
        for c in self.solver.assertions():
            if isinstance(c, BoolRef):
                print c
            else:
                print hex(c.as_long())

        print(self.solver.check())
        if self.solver.check() == sat:
            m = self.solver.model()
            self.vars['m'] = m
            calldata_args = self.__indirect_address_constraints.reference_args["CALLDATALOAD"]
            print "calldata_args %s" % calldata_args
            references = dict()
            for opcode in self.__indirect_address_constraints.reference_args:
                references[opcode] = dict() # TODO: use default value for dict()
            for d in m.decls():
                if isinstance(m[d], BoolRef):
                    print "%s = %s" % (d.name(), m[d])
                else:
                    for opcode in self.__indirect_address_constraints.reference_args:
                        ref_args = self.__indirect_address_constraints.reference_args[opcode]
                        if d.name() in ref_args:
                            value = d.name()
                            # offset = hex(eval("%s" % eval(ref_args[value])))
                            if "SHA3" in ref_args[d.name()].opcode:
                                offset = ("%s" % (ref_args[value]))
                            else:
                                print "%s" % ref_args[value].format_dependencies(True, True)
                                print self.vars
                                print "%s" % self.vars[m["MLOA_0_752_0"]].__class__
                                offset = hex(eval("%s" % eval(ref_args[value].format_dependencies(False,True), self.vars), z3lib.__dict__, self.vars))
                                print "add in calldata %s: %s = %s" % (value, "C[%s]" % offset, hex(m[d].as_long()))
                            references[opcode][offset] = value
                        elif d.name() not in ["SHA3"]:
                            print "%s = %s" % (d.name(), hex(m[d].as_long()))
            for opcode in references:
                print "%s values" % opcode
                for offset in references[opcode]:
                    var = eval(references[opcode][offset], z3lib.__dict__, self.vars)
                    print "%s[%s] = %s" % (opcode[:4], offset, hex(eval("m[var].as_long()")))

        self.solver.pop()
        print("\n")
        for i, c in reversed(list(enumerate(target.constraints))):
            print "%s: %s" % (i,c.format_dependencies(True, False, False))
        print("\n")

    def __apply_constraints(self, expression):
        opcode = expression.opcode
        memory_constraints = self.__indirect_address_constraints.mem_constraints
        storage_constraints = self.__indirect_address_constraints.store_constraints
        indirect_constraints = dict(memory_constraints, **storage_constraints)
        if expression.contains_operations({"MLOAD", "SLOAD", "SHA3"}):
            for i in expression.dependencies:
                self.__apply_constraints(expression.dependencies[i])
            address = expression.address
            if address in indirect_constraints:
                for indirect_constraint in indirect_constraints[address] :
                    print("indirect_constraints self.solver.add(%s)" % indirect_constraint)
                    eval("self.solver.add(%s)" % indirect_constraint, z3lib.__dict__, self.vars)
            elif expression.opcode not in mem_write_ops:
                expression_copy = deepcopy(expression)
                if 0 in expression_copy.dependencies:
                    print("%s reads before %s" % (opcode, expression_copy.reads[0]))
                    print("%s deps before %s" % (opcode, expression_copy.dependencies[0]))
                expression_copy.dependencies = dict()
                print"%s self.solver.add(%s) class %s" % (opcode, expression, expression.__class__)
                eval("self.solver.add(%s)" % expression, z3lib.__dict__, self.vars)
        else:
            address = expression.address
            if address in indirect_constraints:
                for indirect_constraint in indirect_constraints[address]:
                    #print("indirect_constraints self.solver.add(%s)" % indirect_constraint)
                    eval("self.solver.add(%s)" % indirect_constraint, z3lib.__dict__, self.vars)
            elif opcode not in mem_write_ops:
                print("normal self.solver.add(%s)" % (expression.__class__))
                print("normal self.solver.add(%s)" % (expression))
                eval("self.solver.add(%s)" % expression, z3lib.__dict__, self.vars)

if __name__ == "__main__":
    input_file = open(sys.argv[1])
    line = input_file.readline().strip()
    if " " in line:
            line = line.split(" ")[1]
    input_file.close()
    a = TargetSolver(line)
