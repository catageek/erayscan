from expressions import *
from constraints import *
from opcodes import fake_ops, mem_write_ops
from z3 import *
import z3 as z3lib
import sys

class IndirectAddressConstraintBuilder():
    def __init__(self, constraints, _vars):
        self.vars = _vars
        self.__constraints = constraints
        self.__store_opcodes = dict()
        self.reference_constraints = dict()
        self.reference_args = dict()
        self.reference_original_args = dict()
        self.store_constraints = dict()
        self.mem_constraints = dict()
        references = {"CALLDATALOAD", "MLOAD"}
        for opcode in references:
            self.build_reference_constraints(opcode)
        self.reference_to_move(references)
        self.__sstores = self.get_ops_list({"SSTORE"})
        self.build_storage_constraints()
        self.__mstores = self.get_ops_list(mem_write_ops)
        self.build_memory_constraints()

    def build_reference_constraints(self, opcode):
        print "==== Build %s constraints ====" % opcode
        self.reference_constraints[opcode] = dict()
        self.reference_args[opcode] = dict()
        self.reference_original_args[opcode] = dict()
        ref_ops = self.get_ops_list({opcode})
        self.__store_opcodes[opcode] = ref_ops
        for i, constraint in enumerate(self.__constraints):
            self.__build_reference_constraints(i, constraint, opcode)

    def __build_reference_constraints(self, index, constraint, opcode):
        for j, read in enumerate(constraint.reads):
            if j in constraint.dependencies:
                self.__build_reference_constraints(index, constraint.dependencies[j], opcode)

        if constraint.opcode == opcode:
            print "Evaluating %s expression %s #%s of class %s" % (constraint.opcode, constraint.get_expression(), index, constraint.__class__)
            equals = list()
            values = list()
            ref_constraints = list()

            varname, oldname = self.__create_reference_register(constraint, index, 0, opcode)
            ref_constraint = "%s == %s" % (varname, constraint.writes[0])
            ref_constraints.append(ref_constraint)
            #print "    Appending %s in __ref_constraints at index %s " % (ref_constraint, index)

            if opcode == "CALLDATALOAD":
                for ref_index, ref_op in self.__store_opcodes[opcode]:
                    #print "   looking for calldata op in expression %s #%s" % (calldata_op, calldata_index)
                    if ref_index <= index:
                        continue
                    if ref_op.opcode == opcode:
                        for byte in range(32):
                            mask = BitVecVal(-1, 256)
                            mask = mask.as_long() >> (8 * byte)
                            #print("    append in equals: %s + %s == %s" % (ref_op.format_dependency(0), byte, oldname))
                            equals.append(eval("%s + %s == %s" % (ref_op.format_constraint(0), byte, oldname), z3lib.__dict__))
                            #print("    append in values: %s & %s == LShR(%s, %s)" % (ref_op.writes[0], mask, expression.writes[0], 8 * byte))
                            values.append(eval("%s & %s == LShR(%s, %s)" % (ref_op.writes[0], mask, constraint.writes[0], 8 * byte), z3lib.__dict__))

                if len(equals) > 0:
                    ref_constraint = [ Implies(equals[j], values[j]) for j in range(len(equals))]
                    ref_constraints.append(ref_constraint)
                    #print "    Appending %s in __ref_constraints at index %s " % (calldata_constraint, index)

            if len(ref_constraints) > 0:
                self.reference_constraints[opcode][constraint.address] = ref_constraints

    def __create_reference_register(self, constraint, index, dependency, opcode, offset = None):
        key = "%s_%s_%s" % (index, constraint.address, dependency)
        oldname = constraint.format_dependency(dependency)
        if offset is not None:
            varname = "%s_%s_%s" % (opcode[:4], key, offset)
            reads = dict()
            writes = dict()
            reads[0] = offset
            reads[1] = constraint.writes[0]
            writes[0] = constraint.writes[0]
            expression = BinOpExpression("ADD", reads, writes, constraint.address)
            expression.set_dependency(reads[1], constraint)
            self.reference_args.setdefault(opcode, dict())[varname] = Constraint(expression)
            print "create variable %s to replace %s" % (varname, expression)
        else:
            varname = "%s_%s" % (opcode[:4], key)
            self.reference_args.setdefault(opcode, dict())[varname] = deepcopy(constraint)
            print "create variable %s to replace %s" % (varname, constraint.get_expression())
        constraint.reads[dependency] = varname
        if dependency in constraint.dependencies:
            del constraint.dependencies[dependency]
        self.vars[varname] = eval("BitVec('%s', 256)" % varname, z3lib.__dict__)
        return varname, oldname

    def reference_to_move(self, opcodes):
        for i, constraint in enumerate(self.__constraints):
            self.__constraints[i] = self.__reference_to_move(constraint, opcodes)

    def __reference_to_move(self, constraint, opcodes):
        for i, read in enumerate(constraint.reads):
            if i in constraint.dependencies:
                constraint.dependencies[i] =  self.__reference_to_move(constraint.dependencies[i], opcodes)
        if constraint.opcode in opcodes:
            constraint.__class__ = MoveConstraint
            constraint.opcode = "MOVE"
        return constraint

    def build_storage_constraints(self):
        print "==== Build storage constraints ===="
        for i, constraint in enumerate(self.__constraints):
            self.__build_storage_constraints(i, constraint)

    def __build_storage_constraints(self, index, expression):
        if expression.opcode in {"SHA3"}:
            print "Evaluating %s expression %s #%s" % (expression.opcode, expression, index)
            equals = list()
            values = list()
            at_least_one = list()
            store_constraints = list()

            # varname, oldname = self.__create_reference_register(expression.dependencies[0], index, 0, expression.opcode)
            # varname, oldname = self.__create_reference_register(expression, index, 0, expression.opcode)
            store_constraint = "SHA3(Concat(BitVecVal(%s,256),BitVecVal(%s,256))) == %s" % (expression.reads[0], expression.reads[1], expression.writes[0])
            print "new constraint SHA3(Concat(BitVecVal(%s,256),BitVecVal(%s,256))) == %s" % (expression.reads[0], expression.reads[1], expression.writes[0])
            store_constraints.append(store_constraint)
            #print "    Appending %s in __ref_constraints at index %s " % (calldata_constraint, index)

            for store_index, store in self.__sstores:
                print "   looking for sstore in expression #%s %s" % (store_index, store)
                if store_index <= index:
                    continue
                if store.opcode == "SSTORE":
                    #print("    append in equals: %s == %s" % (store.format_dependency(0), oldname))
                    equals.append(eval("%s == %s" % (store.format_dependency(0), oldname), z3lib.__dict__))
                    #print("    append in values: %s == %s" % (store.format_dependency(1), expression.writes[0]))
                    values.append(eval("%s == %s" % (store.format_dependency(1), expression.writes[0]), z3lib.__dict__))

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
        if expression.opcode in {"SLOAD"}:
            print "Evaluating %s expression %s #%s" % (expression.opcode, expression, index)
            equals = list()
            values = list()
            at_least_one = list()
            store_constraints = list()

            # varname, oldname = self.__create_reference_register(expression.dependencies[0], index, 0, expression.opcode)
            varname, oldname = self.__create_reference_register(expression, index, 0, expression.opcode)
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
                    equals.append(eval("%s == %s" % (store.format_dependency(0), oldname), z3lib.__dict__))
                    #print("    append in values: %s == %s" % (store.format_dependency(1), expression.writes[0]))
                    values.append(eval("%s == %s" % (store.format_dependency(1), expression.writes[0]), z3lib.__dict__))

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
        for i, constraint in enumerate(self.__constraints):
            self.__build_memory_constraints(i, constraint)

    def __build_memory_constraints(self, index, constraint):
        for j in constraint.dependencies:
            self.__build_memory_constraints(index, constraint.dependencies[j])

        if constraint.opcode in {"MLOAD"}:
            print "Evaluating %s expression %s #%s" % (constraint.opcode, constraint, index)
            equals = list()
            values = list()
            at_least_one = list()
            mem_constraints = list()

            for mstore in self.__mstores:
                #print "   looking for mstore in expression #%s %s" % (mstore[0], mstore[1])
                if mstore[0] <= index:
                    continue
                if mstore[1].opcode == "MSTORE":
                    #print("    append in equals: %s == %s" % (mstore[1].format_dependency(0), expression.format_dependency(0, True, False, True)))
                    equals.append(eval("%s == %s" % (mstore[1].format_constraint(0), constraint.format_constraint(0, True)), z3lib.__dict__, self.vars))
                    print("    append in values: %s == %s" % (mstore[1].format_constraint(1, True), constraint.writes[0]))
                    values.append(eval("%s == %s" % (mstore[1].format_constraint(1, True), constraint.writes[0]),z3lib.__dict__, self.vars))
                elif mstore[1].opcode == "CALLDATACOPY":
                    destination = mstore[1].format_constraint(0)
                    #source = mstore[1].format_dependency(1)
                    size = mstore[1].format_constraint(2)
                    offset = "calldatacopy_%s_%s_offset" % (mstore[1].address, constraint.address)
                    source, oldsource = self.__create_reference_register(mstore[1], mstore[0], 1, "CALLDATALOAD", offset)
                    #self.calldata_args[source] += " + m[%s].as_long()" % offset
                #        if 1 in expression.dependencies:
                #            del expression.dependencies[1]
                    equals_calldatacopy_str = "And(%s + %s == %s, %s < %s)" \
                            % (destination, offset, constraint.format_dependency(0), offset, size)
                    new_constraint = "Implies(%s, %s == %s)" \
                            % (equals_calldatacopy_str, constraint.writes[0], source)
                    mem_constraints.append(new_constraint)
                    #print "Appending constraints %s for mstore %s" % (constraint, mstore[1])
                    self.vars[offset] = eval("BitVec('%s', 256)" % offset, z3lib.__dict__)
                    at_least_one.append(eval(equals_calldatacopy_str, z3lib.__dict__))

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

    def get_ops_list(self, ops):
        oplist = list()
        for i, constraint in enumerate(self.__constraints):
            self.__get_ops_list(constraint, ops, oplist, i)
        return oplist

    def __get_ops_list(self, constraint, ops, oplist, index):
        if constraint.opcode in ops:
            oplist.append((index, deepcopy(constraint)))
        for i in constraint.dependencies:
            self.__get_ops_list(constraint.dependencies[i], ops, oplist, index)
