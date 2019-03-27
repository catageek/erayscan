from structurer import Structurer
from expressionblock import ExpressionBlock
from expressions import BinOpExpression
from copy import deepcopy

import sys


class TargetIdentifier(Structurer):
    def __init__(self, binary):
        Structurer.__init__(self, binary)
        self.paths_to_targets = dict()
        for func in self.get_all_functions():
            self.retrieve_targets(func, 'SSTORE', 1)

    def retrieve_targets(self, func, opcode, arg_index):
        graph = func.graph
        self.__targets = list()
        for block in graph:
            self.__retrieve_targets(block, opcode, arg_index)
        self.paths_to_targets[func.signature] = self.__targets
        for target in self.__targets:
            print("function: " + str(hex(func.signature)))
            print("block: " + str(target.traversed_blocks[-1]))
            print("target instruction: " + str(target.expression))
            print("target register: " + str(target.live))


    def __retrieve_targets(self, block, opcode, arg_index):
            if isinstance(block, ExpressionBlock):
                self.__iterate_expressions(block.get_items(), opcode, arg_index, block.get_id())
            else:
                for elem in block.get_blocks():
                    self.__retrieve_targets(elem, opcode, arg_index)

    def __iterate_expressions(self, expressions, opcode, arg_index, block_id, index = -1):
        for i, expression in enumerate(expressions):
            if expression.opcode == opcode and isinstance(expression.reads[arg_index], str):
                self.__targets.append(PathToTarget(expression, block_id, arg_index, i if index == -1 else index))
            self.__iterate_expressions(expression.dependencies.values(), opcode, arg_index, block_id, i)



class PathToTarget():
    def __init__(self, expression, block_id, arg_index, exp_index):
        self.enabled = True
        self.expression = deepcopy(expression)
        self.constraints = list()
        self.traversed_blocks = [ block_id ]
        self.has_reached_target = False
        self.index = exp_index
        self.arg_index = arg_index
        self.live = set()
        if arg_index in expression.dependencies:
            self.live |= expression.dependencies[arg_index].get_read_registers()
        else:
            self.live |= expression.reads[arg_index]

    def debug_target(self):
        print("Constraints for target %s" % self.expression)
        for constraint in self.constraints:
            print(constraint)
        print("End of constraints for target %s" % self.expression)

    def set_target_value_constraint(self, value):
        if self.arg_index in self.expression.dependencies:
            write = self.expression.dependencies[self.arg_index].writes[0]
            reads = [write, value]
            expression = BinOpExpression("EQ", reads, list(), -1)
            expression.set_dependency(write, self.expression.get_dependency(self.arg_index))
        else:
            expression = BinOpExpression("EQ", [self.expression.reads[self.arg_index], value], list(), -1)
        self.constraints.insert(0, expression)

if __name__ == "__main__":
    input_file = open(sys.argv[1])
    line = input_file.readline().strip()
    if " " in line:
            line = line.split(" ")[1]
    input_file.close()
    a = TargetIdentifier(line)
