#!/usr/bin/env python3

import collections
import re
import contextlib
import os
import sys
import typing
from datetime import datetime, timedelta

from common import (isEndingProofCmd, isFinishingProofCmd,
                    isVernacCmd, isGoalPunctuation, isCancel,
                    isFailed, isAdd, isObserve, getAddBody,
                    getCancelDest, get_id, sublist_contained,
                    lemma_name_from_statement, preprocess_the_works,
                    eprint, ppCommand, possiblyStartingProofCmd,
                    get_stem, get_time)
from data_format import (get_users, get_sessions, get_commands)

from sexpdata import loads, dumps
from dataclasses import dataclass

logdir = "logs"

@dataclass
class ProofMetadata:
    total_num_proofs : int
    total_num_tactics : int
    total_num_cancellations : int
    total_num_failures : int
    all_tactics : typing.Counter[str]
    cancelled_tactics : typing.Counter[str]
    failed_tactics : typing.Counter[str]

class Timestat:
    total_time : timedelta
    num_times : int
    max_time : timedelta
    def __init__(self):
        self.total_time = timedelta()
        self.num_times = 0
        self.max_time = timedelta()
    def add_time(self, d: timedelta):
        self.total_time += d
        if d > self.max_time:
            self.max_time = d
        self.num_times += 1
    @property
    def avg_time(self):
        return self.total_time / self.num_times
    def pp(self, name: str):
        print(f"{name}: avg is {self.avg_time}, max is {self.max_time}")

def main():
    total_stats = ProofMetadata(0, 0, 0, 0,
                                collections.Counter(),
                                collections.Counter(),
                                collections.Counter())
    num_backtracked_proofs = 0
    num_other_noninteractive_proofs = 0
    num_changes_add_semi = 0
    add_semi_times = Timestat()
    num_changes_remove_semi = 0
    remove_semi_times = Timestat()
    num_changes_change_args = 0
    change_args_times = Timestat()
    num_changes_lookup_args = 0
    lookup_args_times = Timestat()
    num_changes_change_tactic = 0
    change_tactic_times = Timestat()
    user_proof_session_counts = collections.Counter()
    with open("users.txt", 'r') as usersfile:
        profiles = loads(usersfile.read())
    for user in get_users(logdir):
        for session in get_sessions(logdir, user):
            cmds = get_commands(logdir, user, session)
            is_interactive_session = \
                sublist_contained(cmds, [isCancel, lambda entry: not isCancel(entry)])
            if not is_interactive_session:
                continue
            preprocessed_cmds = preprocess_the_works(profiles, cmds)

            while len(preprocessed_cmds) > 0:
                lemma_cmd = pop_to_next_proof(preprocessed_cmds)
                if lemma_cmd == None:
                    break
                proof_cmds = pop_proof(preprocessed_cmds)
                if not is_interactive_proof(proof_cmds):
                    num_other_noninteractive_proofs += 1
                    continue
                user_proof_session_counts[user] += 1
                if is_backtracked_proof(proof_cmds):
                    num_backtracked_proofs += 1
                    continue
                # if not isFinishingProofCmd(getAddBody(getLastNonObserve(proof_cmds))):
                #     continue
                graph = build_graph(lemma_cmd, proof_cmds)
                for node in graph.nodes:
                    if len(node.children) > 1:
                        if any([child.command.strip() != node.children[0].command.strip()
                                for child in node.children]):
                            solution = node.children[-1].command
                            for attempt in node.children[:-1]:
                                if attempt.command.strip() == solution.strip():
                                    continue
                                if re.fullmatch("\s*[*+-{}]\s*", attempt.command):
                                    continue
                                attempt_time = node.children[-1].timestamp - attempt.timestamp
                                period_match = \
                                    re.match("(.*)\.", attempt.command, re.DOTALL)
                                attempt_minus_period = period_match.group(1) if period_match else attempt.command
                                solution_period_match = \
                                    re.match("(.*)\.", solution, re.DOTALL)
                                solution_minus_period = solution_period_match.group(1)\
                                    if solution_period_match else solution
                                if re.match(f"{escape_as_re(attempt_minus_period)}\s*;.*", solution):
                                    num_changes_add_semi += 1
                                    print(f"Added semicolon: {attempt.command} -> {solution}")
                                    print(f"Took {attempt_time}")
                                    add_semi_times.add_time(attempt_time)
                                elif re.match(f"{escape_as_re(solution_minus_period)}\s*;.*",
                                              attempt.command):
                                    num_changes_remove_semi += 1
                                    print(f"Removed semicolon: {attempt.command} -> {solution}")
                                    print(f"Took {attempt_time}")
                                    remove_semi_times.add_time(attempt_time)
                                elif re.match(f"{get_stem(attempt.command)}[^;]*\.",
                                            solution):
                                    num_changes_change_args += 1
                                    print(f"Change args: {attempt.command} -> {solution}")
                                    print(f"Took {attempt_time}")
                                    change_args_times.add_time(attempt_time)
                                elif re.match(f"\s*(Search|Check).*", solution) and \
                                     re.match(f"{get_stem(attempt.command)}[^;]*\.",
                                              node.children[-1].children[-1].command):
                                    num_changes_lookup_args += 1
                                    print(f"Lookup, then change args: {attempt.command} -> {solution} {node.children[-1].children[-1].command}")
                                    print(f"Took {attempt_time}")
                                    lookup_args_times.add_time(attempt_time)
                                else:
                                    print(f"Other change: {attempt.command} -> {solution}")
                                    print(f"Took {attempt_time}")
                                    num_changes_change_tactic += 1
                                    change_tactic_times.add_time(attempt_time)
                            # print(lemma_name_from_statement(getAddBody(lemma_cmd)),
                            #       [node.command for node in node.children])
                proof_stats = get_stats(proof_cmds)
                total_stats = add_stats(total_stats, proof_stats)
    add_semi_times.pp("add semi")
    remove_semi_times.pp("remove semi")
    change_args_times.pp("change args")
    lookup_args_times.pp("lookup args")
    change_tactic_times.pp("change tactic")

    print(f"Number of changes which add a semicolon after: {num_changes_add_semi}")
    print(f"Number of changes which remove a semicolon clause after: "
          f"{num_changes_remove_semi}")
    print(f"Number of changes which change the arguments to a tactic: "
          f"{num_changes_change_args}")
    print(f"Number of changes which change the arguments to a tactic, after lookup: "
          f"{num_changes_lookup_args}")
    print(f"Number of other changes: {num_changes_change_tactic}")
    print(f"{num_backtracked_proofs} backtracked proofs")
    print(f"{num_other_noninteractive_proofs} other non-interactive proofs")
    print(f"User interactive proof sessions count: {user_proof_session_counts}")
    print_proof_metadata(total_stats)

def print_proof_metadata(metadata):
    print(f"Total interactive, successful proof sessions: {metadata.total_num_proofs}")
    print(f"Total tactics invoked: {metadata.total_num_tactics}")
    print("Tactics invoked:")
    for tactic, count in metadata.all_tactics.most_common(25):
        num_cancelled = metadata.cancelled_tactics[tactic]
        num_failed = metadata.failed_tactics[tactic]
        # print(f"{tactic}: {count} "
        #       f"(Cancelled {num_cancelled} {100 * num_cancelled / count:3.2f}%, "
        #       f"failed {num_failed} {100 * num_failed / count:3.2f}%))")
        print(f"{tactic}& {count}& "
              f"{num_failed}& {num_cancelled-num_failed}\\\\")
    print(f"Total tactics cancelled: {metadata.total_num_cancellations}")
    print(f"Total tactics failed: {metadata.total_num_failures}")
    pass
def add_stats(t, p):
    return ProofMetadata(p.total_num_proofs + t.total_num_proofs,
                         p.total_num_tactics + t.total_num_tactics,
                         p.total_num_cancellations + t.total_num_cancellations,
                         p.total_num_failures + t.total_num_failures,
                         p.all_tactics + t.all_tactics,
                         p.cancelled_tactics + t.cancelled_tactics,
                         p.failed_tactics + t.failed_tactics)
def get_stats(proof_cmds):
    all_tactics = collections.Counter()
    cancelled_tactics = collections.Counter()
    failed_tactics = collections.Counter()
    num_tactics = 0
    num_cancellations = 0
    num_failures = 0
    history_stack = []
    for cmd in proof_cmds:
        if isAdd(cmd):
            tactic = getAddBody(cmd)
            history_stack.append((get_id(cmd), tactic))
            if isVernacCmd(tactic):
                continue
            if isGoalPunctuation(tactic):
                continue
            num_tactics += 1
            stem = get_stem(tactic)
            all_tactics[stem] += 1
        if isCancel(cmd):
            cancel_dest = getCancelDest(cmd)
            cancellation_size = 0
            while len(history_stack) > 0 and history_stack[-1][0] != cancel_dest:
                state_num, tactic = history_stack.pop()
                if isVernacCmd(tactic):
                    continue
                if isGoalPunctuation(tactic):
                    continue
                if isFailed(cmd):
                    failed_tactics[get_stem(tactic)] += 1
                cancelled_tactics[get_stem(tactic)] += 1
                cancellation_size += 1
            if isFailed(cmd):
                num_failures += cancellation_size
            num_cancellations += cancellation_size
            assert len(history_stack) > 0

    return ProofMetadata(1,
                         num_tactics, num_cancellations, num_failures,
                         all_tactics, cancelled_tactics, failed_tactics)
def is_interactive_proof(proof_cmds):
    return sublist_contained(proof_cmds, [isCancel])
def is_backtracked_proof(proof_cmds):
    if isCancel(proof_cmds[-1]):
        return True
    return False
def pop_proof(cmds):
    states = []
    proof_cmds = []
    while len(cmds) > 0:
        cmd = cmds.pop(0)
        proof_cmds.append(cmd)
        if isAdd(cmd):
            states.append(get_id(cmd))
            if isEndingProofCmd(getAddBody(cmd)):
                return proof_cmds
        if isCancel(cmd):
            cancel_dest = getCancelDest(cmd)
            while len(states) > 0 and states[-1] != cancel_dest:
                state_num = states.pop()
            if len(states) == 0:
                return proof_cmds
    return proof_cmds
def pop_to_next_proof(cmds):
    lemma_cmd = None
    while len(cmds) > 1:
        cmd = cmds.pop(0)
        if isAdd(cmd) and possiblyStartingProofCmd(getAddBody(cmd)):
            lemma_cmd = cmd
        if isAdd(cmds[0]) and \
           (not isVernacCmd(getAddBody(cmds[0])) or
            re.match("\s*Proof",getAddBody(cmds[0]))):
            return lemma_cmd
    return None

class DummyFile:
    def write(self, x): pass
    def flush(self): pass
@contextlib.contextmanager
def nostderr():
    save_stderr = sys.stderr
    sys.stderr = DummyFile()
    yield
    sys.stderr = save_stderr

import pygraphviz as pgv

@dataclass(init=True)
class LabeledNode:
    command : str
    node_id : int
    timestamp : datetime
    children : typing.List["LabeledNode"]
    parent : typing.Optional["LabeledNode"]
class ProofGraph:
    __graph : pgv.AGraph
    __next_node_id : int
    start_node : LabeledNode
    nodes : typing.List[LabeledNode]
    def __init__(self, lemma_label : str) -> None:
        self.__graph = pgv.AGraph(directed=True)
        self.__next_node_id = 0
        self.nodes = []
        self.start_node = self.mkNode(lemma_label, datetime.fromtimestamp(0), None)

    def mkNode(self, command : str, time : datetime, parent :
               typing.Optional[LabeledNode]) -> LabeledNode:
        self.__graph.add_node(self.__next_node_id, label=command)
        self.__next_node_id += 1
        newNode = LabeledNode(command, self.__next_node_id-1, time, [], parent)
        if parent:
            self.__graph.add_edge(parent.node_id, newNode.node_id)
            parent.children.append(newNode)
        self.nodes.append(newNode)
        return newNode
    def setNodeColor(self, node : LabeledNode, color : str) -> None:
        node_handle = self.__graph.get_node(node.node_id)
        node_handle.attr["fillcolor"] = color
        node_handle.attr["style"] = "filled"
    def draw(self, filename : str) -> None:
        self.__graph.draw(filename, prog="dot")

def build_graph(lemma_cmd, proof_cmds):
    lemma_name = lemma_name_from_statement(getAddBody(lemma_cmd))
    graph = ProofGraph(getAddBody(lemma_cmd))
    next_node_id = 1
    states = [(get_id(lemma_cmd), graph.start_node)]
    state_map = {}
    for cmd in proof_cmds:
        if isAdd(cmd):
            most_recent_state, most_recent_node = states[-1]
            if shouldFilterCommand(cmd):
                state_map[get_id(cmd)] = most_recent_state
                continue
            states.append((get_id(cmd),
                           graph.mkNode(sanitizeTactic(getAddBody(cmd)),
                                        datetime.fromtimestamp(get_time(cmd)),
                                        most_recent_node)))
            next_node_id += 1
            if isFinishingProofCmd(getAddBody(cmd)):
                for statenum, node in states:
                    graph.setNodeColor(node, "blue")
        if isFailed(cmd):
            most_recent_state, most_recent_node = states[-1]
            graph.setNodeColor(most_recent_node, "red")
        if isCancel(cmd):
            cancel_dest = getCancelDest(cmd)
            cancel_dest = state_map.get(cancel_dest, cancel_dest)
            while len(states) > 0 and states[-1][0] != cancel_dest:
                states.pop()
            assert len(states) > 0
    if not os.path.exists("graphs"):
       os.mkdir("graphs")
    graph_filename = "graphs/" + lemma_name + ".svg"
    graph.draw(graph_filename)
    return graph

def sanitizeTactic(tac):
    all_parens_match = re.match("\((.*)\)\.", tac)
    if all_parens_match:
        return all_parens_match.group(1) + "."
    return tac

def escape_as_re(s):
    return s.replace("+", "\\+")\
        .replace("(", "\(")\
        .replace(")", "\)")\
        .replace("[", "\[")\
        .replace("]", "\]")

def shouldFilterCommand(cmd):
    return any([re.match(pat, getAddBody(cmd), re.DOTALL)
                for pat in ["\s*Show.*\.\s*", "\s*(S|Uns)et.*\.\s*",
                            "\s*Add.*\.\s*", "\s*Remove.*\.\s*",
                            "\s*Redirect.*\.\s*", "\s*Timeout.*\.\s*"]])

def getLastNonObserve(cmds):
    for i in range(1, len(cmds)):
        if not isObserve(cmds[-i]):
            return cmds[-i]

if __name__ == "__main__":
    main()
