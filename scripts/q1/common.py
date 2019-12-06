#!/usr/bin/env python3

from sexpdata import Symbol, loads, dumps
from typing import Any, Tuple, TypeVar, Callable, List
import re
import functools

def assoc(key, sexp):
    if not isinstance(sexp, list):
        return None
    for entry in sexp:
        if isinstance(entry, list) and entry[0] == Symbol(key):
            return entry[1]
    return None

def get_body(entry):
    return entry[-1]
def lens_set_body(entry, newbody):
    return entry[:-1]+[newbody]

get_user = functools.partial(assoc, "user")
get_time = functools.partial(assoc, "time")
get_session = functools.partial(assoc, "session")
get_session_module = functools.partial(assoc, "session-module")
get_id = functools.partial(assoc, "id")

def isObserve(entry):
    return get_cmd_type(entry) == Symbol("StmObserve")
def isCancel(entry):
    return get_cmd_type(entry) == Symbol("StmCancel") or \
        get_cmd_type(entry) == Symbol("Failed")
def isFailed(entry):
    return get_cmd_type(entry) == Symbol("Failed")
def isAdd(entry):
    return get_cmd_type(entry) == Symbol("StmAdd")
def getAddBody(entry):
    return get_body(entry)[1][2]
def getCancelDest(entry):
    return get_body(entry)[1][1][0]

def mkEntry(time : float, user : int, module : str, session : float, body : Any):
    return [[Symbol('time'), time], [Symbol('user'), user],
            [Symbol('session-module'), module],
            [Symbol('session'), session], body]

def get_cmd_type(entry):
    body = get_body(entry)
    assert body[0] == Symbol("Control")
    assert isinstance(body[1], list)
    return body[1][0]

def try_loads(sexp):
    entry = loads(sexp)
    try:
        entry = loads(sexp)
        assert get_user(entry) != None
        assert get_time(entry)
        assert get_session(entry)
        return entry
    except:
        return None

def preprocess_failures(profiles, commands):
    return sublist_replace(
        sublist_replace(
            commands,
            [hoAnd(isCancel, functools.partial(userUsesIDE, profiles, "Proof General")),
             lambda entry: (not isCancel(entry)) and (not isUnsetSilent(entry))],
            lambda msgs: [mkEntry(get_time(msgs[0]),
                                  get_user(msgs[0]),
                                  get_session_module(msgs[0]),
                                  get_session(msgs[0]),
                                  [Symbol("Control"),
                                   [Symbol("Failed"),
                                    [getCancelDest(msgs[0])]]]),
                          msgs[1]]),
        [hoAnd(isCancel, functools.partial(userUsesIDE, profiles, "CoqIDE")),
         isObserve, isObserve, isObserve],
        lambda msgs: [mkEntry(get_time(msgs[0]),
                              get_user(msgs[0]),
                              get_session_module(msgs[0]),
                              get_session(msgs[0]),
                              [Symbol("Control"),
                               [Symbol("Failed"),
                                [getCancelDest(msgs[0])]]])])

def preprocess_vernac_backtrack(commands):
    commands = sublist_replace(
        commands,
        [isAdd, lambda msg: isAdd(msg) and re.match("Back\.", getAddBody(msg))],
        lambda msgs: [msgs[0],
                      lens_set_body(msgs[1],
                                    [Symbol("Control"),
                                     [Symbol("StmCancel"),
                                      [get_id(msgs[0])]]])])
    commands = sublist_replace(
        commands,
        [lambda msg: isAdd(msg) and re.match("BackTo\s*\d+\s*\.", getAddBody(msg))],
        lambda msgs: [lens_set_body(msgs[0],
                                    [Symbol("Control"),
                                     [Symbol("StmCancel"),
                                      [int(re.match("BackTo\s+(\d+)\s*\.",
                                                    getAddBody(msgs[0])).group(1))]]])])
    commands = sublist_replace(
        commands,
        [lambda msg: isAdd(msg) and re.match("Backtrack\s+\d+\s+\d+\s+\d+\s*\.", getAddBody(msg))],
        lambda msgs: [lens_set_body(msgs[0],
                                    [Symbol("Control"),
                                     [Symbol("StmCancel"),
                                      [int(re.match("Backtrack\s+(\d+)\s+\d+\s+\d+\s*\.",
                                                    getAddBody(msgs[0])).group(1))]]])])
    return commands

def preprocess_remove_formatting_commands(commands):
    return [command for command in commands
            if isAdd(command) and
            any([re.match(pat, getAddBody(command)) for
                 pat in ["Unset Silent."]])]

def preprocess_the_works(profiles, commands):
    # return preprocess_remove_formatting_commands(preprocess_vernac_backtrack(preprocess_failures(profiles, commands)))
    return preprocess_vernac_backtrack(preprocess_failures(profiles, commands))
T = TypeVar('T')
def sublist_replace(lst : List[T], sublst : List[Callable[[T], bool]],
                    replace : Callable[[List[T]], List[T]]) -> List[T]:
    for i in range(0, len(lst) - (len(sublst) - 1)):
        if all([f(item) for f, item in zip(sublst, lst[i:i+len(sublst)])]):
            return lst[:i] + replace(lst[i:i+len(sublst)]) + \
                sublist_replace(lst[i+len(sublst):], sublst, replace)
    return lst

def sublist_contained(lst : List[T], sublst : List[Callable[[T], bool]]) -> bool:
    for i in range(0, len(lst) - (len(sublst) - 1)):
        if all([f(item) for f, item in zip(sublst, lst[i:i+len(sublst)])]):
            return True

def isUnsetSilent(entry):
    return get_cmd_type(entry) == Symbol("StmAdd") and \
        get_body(entry) == [Symbol("Control"), [Symbol("StmAdd"), [], "Unset Silent. "]]
ides = ["coqtop", "coqc", "CoqIDE", "Proof General", "other"]
def userUsesIDE(profiles, ide : str, entry) -> bool:
    return ides[assoc("answers", profiles[get_user(entry)])[4]] == ide

def hoAnd(*fs):
    if len(fs) == 1:
        return fs[0]
    else:
        return lambda *args: fs[0](*args) and hoAnd(*fs[1:])(*args)

import sys
def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def get_stem(tactic : str) -> str:
    return split_tactic(tactic)[0]

def split_tactic(tactic : str) -> Tuple[str, str]:
    tactic = kill_comments(tactic).strip()
    goal_selector_match = re.match("\d+:\s*(.*)", tactic, re.DOTALL)
    paren_surrounded_match = re.fullmatch("\s*\((.*)\)\.", tactic, re.DOTALL)
    plugin_modifier_match = re.match("^<.*(?<!=)>(.*)", tactic, re.DOTALL)
    if paren_surrounded_match:
        return split_tactic(paren_surrounded_match.group(1) + ".")
    if goal_selector_match:
        return split_tactic(goal_selector_match.group(1))
    if plugin_modifier_match:
        return split_tactic(plugin_modifier_match.group(1))
    if re.match("[-+*\{\}]", tactic):
        stripped = tactic.strip()
        return stripped[:-1], stripped[-1]
    if re.match(".*;.*", tactic):
        return tactic, ""
    for prefix in ["try", "now", "repeat", "decide"]:
        prefix_match = re.match("{}\s+(.*)".format(prefix), tactic)
        if prefix_match:
            rest_stem, rest_rest = split_tactic(prefix_match.group(1))
            return prefix + " " + rest_stem, rest_rest
    for special_stem in ["rewrite <-", "rewrite !", "intros until", "simpl in"]:
        special_match = re.match("{}\s*(.*)".format(special_stem), tactic)
        if special_match:
            return special_stem, special_match.group(1)
    match = re.match("^\(?(\w+)(?:\s+(.*))?", tactic)
    assert match, "tactic \"{}\" doesn't match!".format(tactic)
    stem, rest = match.group(1, 2)
    if not rest:
        rest = ""
    return stem, rest

def kill_comments(string: str) -> str:
    result = ""
    depth = 0
    in_quote = False
    for i in range(len(string)):
        if in_quote:
            if depth == 0:
                result += string[i]
            if string[i] == '"' and string[i-1] != '\\':
                in_quote = False
        else:
            if string[i:i+2] == '(*':
                depth += 1
            if depth == 0:
                result += string[i]
            if string[i-1:i+1] == '*)' and depth > 0:
                depth -= 1
            if string[i] == '"' and string[i-1] != '\\':
               in_quote = True
    return result

def isVernacCmd(cmd : str) -> bool:
    assert isinstance(cmd, str)
    if isGoalPunctuation(cmd):
        return False
    keyword = re.match("(#\[.*?\])?\s*(\S+)(\s+.*)?\.", cmd, re.DOTALL).group(2)
    return isVernacKeyword(keyword)

def isGoalPunctuation(cmd : str) -> bool:
    assert isinstance(cmd, str)
    return bool(re.match("(\d+:)?\s*[-*+\{\}]", cmd.strip()))

def isVernacKeyword(cmd : str) -> bool:
    assert isinstance(cmd, str)
    if cmd in ["Show", "Timeout", "Unset",
               "Qed", "Require", "Set", "From",
               "Definition", "Fixpoint", "Theorem",
               "Function", "Check", "Lemma", "Search",
               "Hint", "Proof", "Backtrack", "Add",
               "Inductive", "Open", "Coercion", "Instance",
               "Ltac", "Notation", "Generalizable", "Anomaly",
               "Redirect", "Import", "Defined", "Admitted",
               "Remove", "Fact", "BackTo", "Abort", "Module",
               "Parameter", "Notation", "End", "Recursive",
               "Create", "Print", "Variable", "Record", "Transparent",
               "Axiom", "Focus", "Locate", "Arguments", "Variant",
               "Declare", "Delimit", "Reserved", "Derive", "CoFixpoint"]:
        return True
    return False

def isAbortingProofCmd(cmd : str) -> bool:
    assert isinstance(cmd, str)
    return ("Admitted" in cmd or
            "Abort" in cmd)
def isEndingProofCmd(cmd : str) -> bool:
    assert isinstance(cmd, str)
    return isAbortingProofCmd(cmd) or isFinishingProofCmd(cmd)
def isFinishingProofCmd(cmd : str) -> bool:
    assert isinstance(cmd, str)
    return ("Qed" in cmd or
            "Defined" in cmd)
def possiblyStartingProofCmd(command : str) -> bool:
    stripped_command = kill_comments(command).strip()
    return (re.match("Lemma\s", stripped_command) != None or
            re.match("Theorem\s", stripped_command) != None or
            re.match("Remark\s", stripped_command) != None or
            re.match("Proposition\s", stripped_command) != None or
            re.match("Definition\s", stripped_command) != None or
            re.match("Example\s", stripped_command) != None or
            re.match("Fixpoint\s", stripped_command) != None or
            re.match("Corollary\s", stripped_command) != None or
            re.match("Let\s", stripped_command) != None or
            ("Instance" in stripped_command and
             "Declare" not in stripped_command) or
            re.match("Function\s", stripped_command) != None or
            re.match("Next Obligation", stripped_command) != None or
            re.match("Property\s", stripped_command) != None or
            re.match("Add Morphism\s", stripped_command) != None)
def lemma_name_from_statement(stmt : str) -> str:
    lemma_match = re.match("\s*\S+\s+([\w']+)", stmt)
    assert lemma_match, stmt
    lemma_name = lemma_match.group(1)
    assert ":" not in lemma_name, stmt
    return lemma_name

def ppCommand(cmd) -> str:
    if get_cmd_type(cmd) == Symbol("StmAdd"):
        return "(*{}:*) {}".format(get_id(cmd), getAddBody(cmd))
    elif get_cmd_type(cmd) == Symbol("StmCancel"):
        return "(*CANCEL {}*)".format(getCancelDest(cmd))
    elif get_cmd_type(cmd) == Symbol("Failed"):
        return "(*FAILED {}*)".format(getCancelDest(cmd))
    else:
        assert get_cmd_type(cmd) == Symbol("StmObserve")
        return ""
