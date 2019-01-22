from pathfinder import PathFinder
from expressions import *
from opcodes import fake_ops, mem_write_ops
from z3 import *

import sys

bool_opcodes = {
        "LT",
        "GT",
        "SLT",
        "SGT",
        "EQ",
        "ISZERO",
        "NONZERO",
        "CALL"
} | fake_ops.viewkeys()

equivalent_opcodes = {
        "ASSERT":   ("NONZERO", MonoOpExpression)
}

class Message():
    def __init__(self):
        self.sender = BitVecVal(0xca11a, 256)
        self.value = BitVec('VALUE', 256)
        self.gas = BitVecVal(3000000, 256)

msg = Message()
BALANCE = BitVec('BALANCE', 256)
AD_MASK = BitVecVal(0xffffffffffffffffffffffffffffffffffffffff, 256)
this = BitVecVal(0xca11ab1e, 256)
target_value = 0xacce551b1e

class IndirectAddressConstraintBuilder():
    def __init__(self, expressions):
        self.__expressions = expressions
        self.__mstores = self.get_ops_list(mem_write_ops)
        self.__sstores = self.get_ops_list({"SSTORE"})
        self.__store_opcodes = dict()
        self.reference_constraints = dict()
        self.reference_args = dict()
        self.reference_original_args = dict()
        self.store_constraints = dict()
        self.mem_constraints = dict()
        references = {"CALLDATALOAD"}
        for opcode in references:
            self.build_reference_constraints(opcode)
        self.reference_to_move(references)
        self.build_storage_constraints()
        self.build_memory_constraints()

    def build_reference_constraints(self, opcode):
        print "==== Build %s constraints ====" % opcode
        self.reference_constraints[opcode] = dict()
        self.reference_args[opcode] = dict()
        self.reference_original_args[opcode] = dict()
        ref_ops = self.get_ops_list({opcode})
        self.__store_opcodes[opcode] = ref_ops
        for i, expression in enumerate(self.__expressions):
            self.__build_reference_constraints(i, expression, opcode)

    def __build_reference_constraints(self, index, expression, opcode):
        if expression.opcode == opcode:
            #print "Evaluating %s expression %s #%s" % (expression.opcode, expression, index)
            equals = list()
            values = list()
            ref_constraints = list()

            varname, oldname = self.__create_reference_register(expression, index, 0, opcode)
            ref_constraint = "%s == %s" % (varname, expression.writes[0])
            ref_constraints.append(ref_constraint)
            #print "    Appending %s in __ref_constraints at index %s " % (ref_constraint, index)

            for ref_index, ref_op in self.__store_opcodes[opcode]:
                #print "   looking for calldata op in expression %s #%s" % (calldata_op, calldata_index)
                if ref_index <= index:
                    continue
                if ref_op.opcode == opcode:
                    for byte in range(32):
                        mask = BitVecVal(-1, 256)
                        mask = mask.as_long() >> (8 * byte)
                        #print("    append in equals: %s + %s == %s" % (ref_op.format_dependency(0), byte, oldname))
                        equals.append(eval("%s + %s == %s" % (ref_op.format_dependency(0), byte, oldname)))
                        #print("    append in values: %s & %s == LShR(%s, %s)" % (ref_op.writes[0], mask, expression.writes[0], 8 * byte))
                        values.append(eval("%s & %s == LShR(%s, %s)" % (ref_op.writes[0], mask, expression.writes[0], 8 * byte)))

            if len(equals) > 0:
                ref_constraint = [ Implies(equals[j], values[j]) for j in range(len(equals))]
                ref_constraints.append(ref_constraint)
                #print "    Appending %s in __ref_constraints at index %s " % (calldata_constraint, index)

            if len(ref_constraints) > 0:
                self.reference_constraints[opcode][expression.address] = ref_constraints

        for j, read in enumerate(expression.reads):
            if j in expression.dependencies:
                self.__build_reference_constraints(index, expression.dependencies[j], opcode)

    def __create_reference_register(self, expression, index, dependency, opcode, offset = None):
        key = "%s_%s_%s" % (index, expression.address, dependency)
        oldexpression = expression
        if key not in self.reference_original_args.setdefault(opcode, dict()):
            self.reference_original_args[opcode][key] = deepcopy(expression)
        else:
            oldexpression = self.reference_original_args[opcode][key]
        oldname = oldexpression.format_dependency(dependency)
        if offset is not None:
            varname = "%s_%s_%s" % (opcode[:4], key, offset)
            self.reference_args.setdefault(opcode, dict())[varname] = "%s + m[%s].as_long()" % (oldexpression.format_dependency(dependency, True, True), offset)
            print "create variable %s to replace %s + %s" % (varname, oldname, offset)
        else:
            varname = "%s_%s" % (opcode[:4], key)
            self.reference_args.setdefault(opcode, dict())[varname] = oldexpression.format_dependency(dependency, True, True)
            print "create variable %s to replace %s" % (varname, oldname)
        expression.reads[dependency] = varname
        globals()[varname] = eval("BitVec('%s', 256)" % varname)
        return varname, oldname

    def reference_to_move(self, opcodes):
        for i, expression in enumerate(self.__expressions):
            self.__expressions[i] = self.__reference_to_move(expression, opcodes)

    def __reference_to_move(self, expression, opcodes):
        for i, read in enumerate(expression.reads):
            if i in expression.dependencies:
                expression.dependencies[i] =  self.__reference_to_move(expression.dependencies[i], opcodes)
        if expression.opcode in opcodes:
            expression.__class__ = MoveExpression
            expression.opcode = "MOVE"
        return expression

    def build_storage_constraints(self):
        print "==== Build storage constraints ===="
        for i, constraint in enumerate(self.__expressions):
            self.__build_storage_constraints(i, constraint)

    def __build_storage_constraints(self, index, expression):
        if expression.opcode in {"SLOAD"}:
            print "Evaluating %s expression %s #%s" % (expression.opcode, expression, index)
            equals = list()
            values = list()
            at_least_one = list()
            store_constraints = list()

            varname, oldname = self.__create_reference_register(expression.dependencies[0], index, 0, expression.opcode)
            #varname, oldname = self.__create_reference_register(expression, index, 0, expression.opcode)
            store_constraint = "%s == %s" % (varname, expression.writes[0])
            print "new constraint %s == %s" % (varname, expression.writes[0])
            store_constraints.append(store_constraint)
            #print "    Appending %s in __ref_constraints at index %s " % (calldata_constraint, index)

            for store_index, store in self.__sstores:
                print "   looking for sstore in expression #%s %s" % (store_index, store)
                if store_index <= index:
                    continue
                if store.opcode == "SSTORE":
                    #print("    append in equals: %s == %s" % (store.format_dependency(0), oldname))
                    equals.append(eval("%s == %s" % (store.format_dependency(0), oldname)))
                    #print("    append in values: %s == %s" % (store.format_dependency(1), expression.writes[0]))
                    values.append(eval("%s == %s" % (store.format_dependency(1), expression.writes[0])))

            if len(equals) > 0:
                nots = [ Not(equals[j]) for j in range(len(equals))]
                keys = [equals[0]]
                keys.extend([And(equals[n], And(nots[:n])) for n in range(1, len(equals))])
                store_constraint = [ Implies(keys[j], values[j]) for j in range(len(keys))]
                store_constraints.append(store_constraint)
                at_least_one.extend(keys)
                store_constraint = Or(at_least_one) == True
                store_constraints.append(store_constraint)

            if len(store_constraints) > 0:
                self.store_constraints[expression.address] = store_constraints

        for j in expression.dependencies:
            self.__build_storage_constraints(index, expression.dependencies[j])

    def build_memory_constraints(self):
        print "==== Build memory constraints ===="
        for i, constraint in enumerate(self.__expressions):
            self.__build_memory_constraints(i, constraint)

    def __build_memory_constraints(self, index, expression):
        if expression.opcode in {"MLOAD", "SHA3"}:
            print "Evaluating %s expression %s #%s" % (expression.opcode, expression, index)
            equals = list()
            values = list()
            at_least_one = list()
            mem_constraints = list()

            for mstore in self.__mstores:
                print "   looking for mstore in expression #%s %s" % (mstore[0], mstore[1])
                if mstore[0] <= index:
                    continue
                if mstore[1].opcode == "MSTORE":
                    print("    append in equals: %s == %s" % (mstore[1].format_dependency(0), expression.format_dependency(0)))
                    equals.append(eval("%s == %s" % (mstore[1].format_dependency(0), expression.format_dependency(0))))
                    print("    append in values: %s == %s" % (mstore[1].format_dependency(1), expression.writes[0]))
                    values.append(eval("%s == %s" % (mstore[1].format_dependency(1), expression.writes[0])))
                elif mstore[1].opcode == "CALLDATACOPY":
                    destination = mstore[1].format_dependency(0)
                    #source = mstore[1].format_dependency(1)
                    size = mstore[1].format_dependency(2)
                    offset = "calldatacopy_%s_%s_offset" % (mstore[1].address, expression.address)
                    source, oldsource = self.__create_reference_register(mstore[1], mstore[0], 1, "CALLDATALOAD", offset)
                    #self.calldata_args[source] += " + m[%s].as_long()" % offset
                #        if 1 in expression.dependencies:
                #            del expression.dependencies[1]
                    equals_calldatacopy_str = "And(%s + %s == %s, %s < %s)" \
                            % (destination, offset, expression.format_dependency(0), offset, size)
                    constraint = "Implies(%s, %s == %s)" \
                            % (equals_calldatacopy_str, expression.writes[0], source)
                    mem_constraints.append(constraint)
                    print "Appending constraints %s for mstore %s" % (constraint, mstore[1])
                    globals()[offset] = eval("BitVec('%s', 256)" % offset)
                    at_least_one.append(eval(equals_calldatacopy_str))

            if len(equals) > 0:
                nots = [ Not(equals[j]) for j in range(len(equals))]
                keys = [equals[0]]
                keys.extend([And(equals[n], And(nots[:n])) for n in range(1, len(equals))])
                mem_constraint = [ Implies(keys[j], values[j]) for j in range(len(keys))]
                mem_constraints.append(mem_constraint)
                at_least_one.extend(keys)
                mem_constraint = Or(at_least_one) == True
                mem_constraints.append(mem_constraint)
                #print "Appending %s in __mem_constraints at index %s " % (mem_constraint, index)

            if len(mem_constraints) > 0:
                self.mem_constraints[expression.address] = mem_constraints

        for j in expression.dependencies:
            self.__build_memory_constraints(index, expression.dependencies[j])
 
    def get_ops_list(self, ops):
        oplist = list()
        for i, expression in enumerate(self.__expressions):
            self.__get_ops_list(expression, ops, oplist, i)
        return oplist

    def __get_ops_list(self, expression, ops, oplist, index):
        if expression.opcode in ops:
            oplist.append((index, deepcopy(expression)))
        for i in expression.dependencies:
            self.__get_ops_list(expression.dependencies[i], ops, oplist, index)

class TargetSolver(PathFinder):
    def __init__(self, binary):
        PathFinder.__init__(self, binary)
        self.solver = Solver()
        print("============== Solver ===============")
        for func in self.get_all_functions():
            self.__iterate_targets(func)

    def __iterate_targets(self, func):
        for target in self.paths_to_targets[func.signature]:
            print("target %s" % target.expression)
            target.set_target_value_constraint(target_value)
            constraints = target.constraints
            self.rewrite_opcodes(constraints)
            self.static_single_assignment(constraints)
            self.declare_variables(constraints)
            self.__indirect_address_constraints = IndirectAddressConstraintBuilder(constraints)
            self.__solve(target)

    def rewrite_opcodes(self, expressions):
        for i, expression in enumerate(expressions):
            opcode = expression.opcode
            if expression.opcode in equivalent_opcodes:
                expressions[i].__class__ = equivalent_opcodes[opcode][1]
                expressions[i].opcode = equivalent_opcodes[opcode][0]

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
                        or expression.contains_operations(bool_opcodes):
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
                        and not expression.contains_operations(bool_opcodes):
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
                globals()[key] = eval("Bool('%s')" % key)
            elif keytype == "BitVec":
                globals()[key] = eval("BitVec('%s', 256)" % key)
            #elif keytype == "BitVecVal":
            #    globals()[key] = eval("BitVecVal(%s, 256)" % key)

    def __declare_variables(self, expression):
        self.__declare_read_variables(expression)
        self.__declare_write_variables(expression)
        for i, read in enumerate(expression.reads):
            if i in expression.dependencies:
                dependency = expression.dependencies[i]
                if expression.contains_operations({"MLOAD", "CALLDATALOAD"})\
                        or expression.contains_operations(bool_opcodes):
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
                if expression.opcode not in bool_opcodes and isinstance(register, str):
                    if len(expression.writes) != 0:
                        self.__declare_same(expression.format_dependency(i), expression.writes[0], True)
            else:
                dependency = expression.dependencies[i]
                if expression.contains_operations({"MLOAD", "CALLDATALOAD"})\
                        or expression.contains_operations(bool_opcodes):
                    self.__convert_read_bool(expression.dependencies[i])

    def is_bool_opcode(self, expression):
        return expression.opcode in bool_opcodes and len(expression.writes) != 0

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
        #target.debug_target()
        for i in self.__indirect_address_constraints.mem_constraints:
            #print "memory constraints %s" % (self.__indirect_address_constraints.mem_constraints[i])
            pass

        calldata_constraints = self.__indirect_address_constraints.reference_constraints["CALLDATALOAD"]
        for i in calldata_constraints:
            for c in calldata_constraints[i]:
                #print "calldata constraints %s" % (c)
                eval("self.solver.add(%s)" % c)

        for constraint in reversed(target.constraints):
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
                            offset = hex(eval("%s" % eval(ref_args[value])))
                            #print "add in calldata %s: %s = %s" % (value, "C[%s]" % offset, hex(m[d].as_long()))
                            references[opcode][offset] = value
                        else:
                            print "%s = %s" % (d.name(), hex(m[d].as_long()))
            for opcode in references:
                print "%s values" % opcode
                for offset in references[opcode]:
                    var = eval(references[opcode][offset])
                    print "%s[%s] = %s" % (opcode[:4], offset, hex(eval("m[var].as_long()")))

        self.solver.pop()
        print("\n")
        for i, c in reversed(list(enumerate(target.constraints))):
            print "%s: %s" % (i,c.format_dependencies(True, False, True))
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
                    #print("indirect_constraints self.solver.add(%s)" % indirect_constraint)
                    eval("self.solver.add(%s)" % indirect_constraint)
            else:
                expression_copy = deepcopy(expression)
                if 1 in expression_copy.dependencies:
                    print("%s reads before %s" % (opcode, expression_copy.reads[1]))
                    print("%s deps before %s" % (opcode, expression_copy.dependencies[1]))
                expression_copy.dependencies = dict()
                format_constraint = expression_copy.format_constraint()
                print"%s self.solver.add(%s)" % (opcode, format_constraint)
                eval("self.solver.add(%s)" % format_constraint)
        else:
            address = expression.address
            if address in indirect_constraints:
                for indirect_constraint in indirect_constraints[address]:
                    #print("indirect_constraints self.solver.add(%s)" % indirect_constraint)
                    eval("self.solver.add(%s)" % indirect_constraint)
            elif expression.opcode not in mem_write_ops:
                format_constraint = expression.format_constraint()
                print("normal self.solver.add(%s)" % (format_constraint))
                eval("self.solver.add(%s)" % format_constraint)

if __name__ == "__main__":
    input_file = open(sys.argv[1])
    line = input_file.readline().strip()
    if " " in line:
            line = line.split(" ")[1]
    input_file.close()
    a = TargetSolver(line)

