#!/usr/bin/env python3

from sexpdata import Symbol, loads
from typing import Any
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

def mkEntry(time : float, user : int, module : str, session : float, body : Any):
    return [[Symbol('time'), time], [Symbol('user'), user], [Symbol('session-module'), module],
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
