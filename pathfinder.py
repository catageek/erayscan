from targetidentifier import TargetIdentifier
from expressionblock import ExpressionBlock
from expressions import MonoOpExpression
from structures import IfThen, IfThenElse
from opcodes import mem_write_ops
from copy import deepcopy

import sys


class PathFinder(TargetIdentifier):
    def __init__(self, binary):
        TargetIdentifier.__init__(self, binary)
        for func in self.get_all_functions():
            self.iterate_blocks(func)

    def target_generator(self, func):
        index = 0
        while index < len(self.paths_to_targets[func.signature]):
            current = index
            index += 1
            yield self.paths_to_targets[func.signature][current]

    def iterate_blocks(self, func):
        graph = func.graph
        target_generator = self.target_generator(func)
        for target in target_generator:
            graph = func.graph
            print("============ Looking for target " + str(target.live) + "  from instruction " + str(target.expression) + " of block id " + str(target.traversed_blocks[-1]) + " in function " + str(hex(func.signature)))
            self.debug_tab = ''
            target.debug_target()
            for block in graph:
                print(self.debug_tab + "entering __iterate_blocks() of block id: " + str(block.get_id()))
                self.__iterate_blocks(func, block, target, target.index)
                print(self.debug_tab + "exiting __iterate_blocks() of block id: " + str(block.get_id()))
        self.paths_to_targets[func.signature] = [ target for target in self.paths_to_targets[func.signature] if target.enabled ]
                

    def __iterate_blocks(self, func, graph, path_to_target, end = None):
        self.debug_tab += '  '
        print self.debug_tab + "In block %s" % (graph.get_id())
        graph.debug_block(len(self.debug_tab))
        print self.debug_tab + "looking for block %s, target reached ? %s" % (path_to_target.traversed_blocks[-1], path_to_target.has_reached_target)

        if graph.get_id() == path_to_target.traversed_blocks[-1]:
            print self.debug_tab + "Target reached"
            path_to_target.has_reached_target = True
            if isinstance(graph, ExpressionBlock):
                self.__build_reverse_path(graph, path_to_target, end)
                return

        if isinstance(graph, ExpressionBlock):
            self.__build_reverse_path(graph, path_to_target)
            return

        elif isinstance(graph, IfThen) or isinstance(graph, IfThenElse):
            if graph.get_id() in path_to_target.traversed_blocks:

                # IF/THEN/(ELSE) block already parsed
                if_block = graph.get_blocks()[0]
                if if_block.get_id() not in path_to_target.traversed_blocks:
                    # parsing IF block if not yet parsed
                    self.__iterate_blocks(func, if_block, path_to_target, end)
                
            else:
                print(self.debug_tab + "Entering IfThen(Else) id " + str(graph.get_id()))

                # Get THEN block constraints in new target, if any
                then_path = deepcopy(path_to_target)
                print self.debug_tab + "process 'Then' block"
                then_has_constraints, is_target_reached_in_then = self.__parse_block(then_path, func, graph.get_blocks()[1], end)

                if isinstance(graph, IfThenElse):
                    # Get ELSE block constraints in current target, if any
                    print self.debug_tab + "process 'Else' block"
                    else_has_constraints, is_target_reached_in_else = self.__parse_block(path_to_target, func, graph.get_blocks()[2], end)
                else:
                    else_has_constraints, is_target_reached_in_else = (False, False)

                # keep new target only if there are new constraints or target is reached
                if (then_has_constraints and not is_target_reached_in_else) or is_target_reached_in_then:
                    # push new target in storage. The target generator will yield it later
                    self.__append_inverted_if_constraint(then_path, graph)
                    self.paths_to_targets[func.signature].append(then_path)
                    # mark block as traversed in new target
                    then_path.traversed_blocks.append(graph.get_id())
                    print "traversed %s" % then_path.traversed_blocks
                    # next path block is ahead, reset flag
                    then_path.has_reached_target = False

                if then_has_constraints | else_has_constraints\
                        | is_target_reached_in_else | is_target_reached_in_then:
                    self.__append_if_constraint(path_to_target, graph)

                if is_target_reached_in_then:
                    # Drop current path if target found in THEN block
                    print self.debug_tab + "target reached in then block, drop original target"
                    print self.debug_tab + "len target %s" % len(self.paths_to_targets[func.signature])
                    path_to_target.enabled = False
                else:
                    # process 'If' block using original target and continue
                    print self.debug_tab + "process 'If' block using original target and continue"
                    self.__iterate_blocks(func, graph.get_blocks()[0], path_to_target, end)
        else:
            for block in reversed(graph.get_blocks()):
                self.__iterate_blocks(func, block, path_to_target, end)
        self.debug_tab = self.debug_tab[:len(self.debug_tab) - 2]

            
    def __parse_block(self, new_path, func, block, end):
        #target.debug_target()
        size = len(new_path.constraints)
        target_reached = new_path.has_reached_target
        self.__iterate_blocks(func, block, new_path, end)
        new_size = len(new_path.constraints)
        target_reached ^= new_path.has_reached_target
        return new_size > size, target_reached

    def __append_inverted_if_constraint(self, path, graph):
        # Get the 'If' condition
        jumpi = graph.get_blocks()[0].get_items()[-1]
        # add 'If' condition reads to live state of new target
        path.live |= jumpi.get_read_registers()

        # add inverted 'If' condition constraint to new target
        condition2 = MonoOpExpression("ISZERO", [ jumpi.reads[1] ], list(), jumpi.address)
        if 1 in jumpi.dependencies:
            dependency = deepcopy(jumpi.dependencies[1])
            condition2.set_dependency(jumpi.reads[1], dependency)
            print(self.debug_tab + "add Then condition1 (must be true): " + str(condition2))
        else:
            print(self.debug_tab + "add Then condition2 (must be true): " + str(condition2))
        path.constraints.append(condition2)

    def __append_if_constraint(self, path, graph):
        # Get the 'If' condition
        jumpi = graph.get_blocks()[0].get_items()[-1]
        # add 'If' condition reads to live state of original target
        path.live |= jumpi.get_read_registers()

        # add 'If' condition constraint to original target
        condition1 = MonoOpExpression("ISZERO", [ jumpi.reads[1] ], [ jumpi.reads[1] ], jumpi.address)
        condition2 = MonoOpExpression("ISZERO", [ jumpi.reads[1] ], list(), jumpi.address)
        if 1 in jumpi.dependencies:
            dependency = deepcopy(jumpi.dependencies[1])
            condition1.set_dependency(jumpi.reads[1], dependency)
            print(self.debug_tab + "add If condition1 (must be false): " + str(condition2) + " in block " + str(graph.get_id()))
        else:
            print(self.debug_tab + "add If condition2 (must be false): " + str(condition2) + " in block " + str(graph.get_id()))
        condition2.set_dependency(jumpi.reads[1], condition1)
        path.constraints.append(condition2)

    def __build_reverse_path(self, block, path, end = None):
        expressions = block.get_items()
        index = get_backwards_write(end, expressions, path.live)
        while index != -1:
            expression = deepcopy(expressions[index])
            path.live -= expression.get_write_registers()
            path.live |= expression.get_read_registers()
            path.constraints.append(expression)
            print(self.debug_tab + "found modifying instruction: " + str(expression) + " at index " + str(index) + " in block " + str(block.get_id()) + " live after " + str(path.live))
            path.traversed_blocks.append(block.get_id())
            index = get_backwards_write(None, expressions, path.live, index)

def get_backwards_write(target_index, expressions, live, current_index = None):
    for i, expression in reversed(list(enumerate(expressions))):

        if current_index is not None and i >= current_index:
            # This expression was already parsed
            continue

        if expression.opcode == "ASSERT":
            return i
        
        if target_index is not None and i >= target_index:
            # target is not reached
            continue

        if expression.contains_operations(mem_write_ops):
            return i

        if len(live & expression.get_write_registers()) != 0:
            return i
    return -1

if __name__ == "__main__":
    input_file = open(sys.argv[1])
    line = input_file.readline().strip()
    if " " in line:
            line = line.split(" ")[1]
    input_file.close()
    a = PathFinder(line)
