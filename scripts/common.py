#!/usr/bin/env python3

from sexpdata import Symbol, loads
from typing import Any, Tuple
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

get_user = functools.partial(assoc, "user")
get_time = functools.partial(assoc, "time")
get_session = functools.partial(assoc, "session")
get_session_module = functools.partial(assoc, "session-module")
get_id = functools.partial(assoc, "id")

def isObserve(entry):
    return get_cmd_type(entry) == Symbol("StmObserve")
def isCancel(entry):
    return get_cmd_type(entry) == Symbol("StmCancel")
def isAdd(entry):
    return get_cmd_type(entry) == Symbol("StmAdd")
def getAddBody(entry):
    return get_body(entry)[1][2]

def mkEntry(time : float, user : int, module : str, session : float, body : Any):
    return [['time', time], ['user', user], ['session-module', module],
            ['session', session], body]

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

import sys
def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def get_stem(tactic : str) -> str:
    return split_tactic(tactic)[0]

def split_tactic(tactic : str) -> Tuple[str, str]:
    tactic = kill_comments(tactic).strip()
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
