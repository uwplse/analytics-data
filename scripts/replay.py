#!/usr/bin/env python3

from sexpdata import loads, dumps, Symbol
import functools
from datetime import datetime
from tqdm import tqdm
import argparse
from os import listdir, stat
from os.path import isfile, join, exists

from common import *
from typing import List, TypeVar, Callable

from split_sessions import split_sessions

logdir = "../raw/logs"

class More:
    def __init__(self, num_lines):
        self.num_lines = num_lines
    def __ror__(self, other):
        s = str(other).split("\n")
        for i in range(0, len(s), self.num_lines):
            eprint(*s[i: i + self.num_lines], sep="\n")
            input("Press <Enter> for more")

def multipartition(items, f):
    categories = {}
    for item in items:
        key = f(item)
        if key not in categories:
            categories[key] = []
        categories[key].append(item)
    return list(categories.values())

def parseDate(s):
    return datetime.strptime(s, "%Y-%m-%d")

def inDateRange(args, entry):
    session_time = datetime.fromtimestamp(get_session(entry))
    return (not args.before or session_time < args.before) and \
        (not args.after or session_time > args.after)

def get_sessions(user):
    user_sessions_dir = f"{logdir}/{user}-sessions"
    if not exists(user_sessions_dir) or \
       stat(user_sessions_dir).st_ctime < \
       stat(join(logdir, str(user))).st_mtime:
        eprint(f"Refreshing sessions for user {user} from logfile")
        split_sessions(str(user))
    return [f for f in listdir(user_sessions_dir)]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--user", type=int, default=-2)
    parser.add_argument("--paginate", dest="paginate", action='store_true')
    parser.add_argument("--mode", choices=["raw", "human"], default="human")
    parser.add_argument("--before", type=parseDate)
    parser.add_argument("--after", type=parseDate)
    args = parser.parse_args()

    #### User selection
    selected_user = args.user
    users = sorted([f for f in listdir(logdir) if isfile(join(logdir, f))])
    while selected_user == -2:
        eprint("Select user (-1 for all):")
        eprint(users)
        try:
            eprint("User #: ", end="")
            sys.stderr.flush()
            i = input()
            selected_user = int(i)
            if str(selected_user) not in users and selected_user != -1:
                eprint(f"{selected_user} is not a valid user!")
                selected_use = -2
        except:
            selected_user = -2

    with open("../raw/users.txt", 'r') as usersfile:
        profiles = loads(usersfile.read())

    if selected_user == -1:
        sessions = []
        for user in users:
            sessions += [(user, session) for session in get_sessions(user)]
        sessions = sorted(sessions)
    else:
        sessions = sorted([(selected_user, session) for session in
                           get_sessions(selected_user)])
    more = More(num_lines=30)
    if selected_user == -1:
        lines = [f"{idx}: User {user}, Start time: {timestamp}"
                   for idx, (user, timestamp) in enumerate(sessions)]
    else:
        lines = [f"{idx}: Start time: {timestamp}"
                   for idx, (user, timestamp) in enumerate(sessions)]
    if not args.paginate:
        eprint("\n".join(lines))
    else:
        "\n".join(lines) | more

    session_idx = -1
    while session_idx == -1:
        try:
            eprint("Session#: ", end="")
            sys.stderr.flush()
            session_idx = int(input())
            if session_idx > len(sessions):
                print("Not a valid session!")
                session_idx = -1
        except ValueError:
            print("Not an integer!")
            raise
    selected_session = sessions[session_idx]

    #### Print

    user, session_label = selected_session
    eprint(f"Selected session {session_label}")

    with open(f"{logdir}/{user}-sessions/{session_label}", 'r') as session_file:
        sorted_cmds = sorted(
            [loads(line) for line in session_file.readlines()],
            key=lambda cmd: get_time(cmd))

    if args.mode == "raw":
        for cmd in sorted_cmds:
            print(dumps(cmd))
        return

    processed_cmds = sublist_replace(
        sorted_cmds,
        [hoAnd(isCancel, functools.partial(userUsesIDE, profiles, "CoqIDE")),
         isObserve, isObserve, isObserve],
        lambda msgs: [mkEntry(get_time(msgs[0]),
                              get_user(msgs[0]),
                              get_session_module(msgs[0]),
                              get_session(msgs[0]),
                              [Symbol("Control"),
                               [Symbol("Failed"),
                                get_body(msgs[0])[1][1][0]]])])

    # if sublist_contained(sorted_cmds, [isCancel, isUnsetSilent]):
    processed_cmds = sublist_replace(
        sorted_cmds,
        [hoAnd(isCancel, functools.partial(userUsesIDE, profiles, "Proof General")),
         lambda entry: (not isCancel(entry)) and (not isUnsetSilent(entry))],
        lambda msgs: [mkEntry(get_time(msgs[0]),
                              get_user(msgs[0]),
                              get_session_module(msgs[0]),
                              get_session(msgs[0]),
                              [Symbol("Control"),
                               [Symbol("Failed"),
                                get_body(msgs[0])[1][1][0]]]),
                      msgs[1]])

    for cmd in processed_cmds:
        if get_cmd_type(cmd) == Symbol("StmAdd"):
            print("(*{}:*) {}".format(get_id(cmd), get_body(cmd)[1][2]))
        elif get_cmd_type(cmd) == Symbol("StmCancel"):
            print("(*CANCEL {}*)".format(get_body(cmd)[1][1][0]))
        elif get_cmd_type(cmd) == Symbol("Failed"):
            print("(*FAILED {}*)".format(get_body(cmd)[1][1]))
        else:
            assert get_cmd_type(cmd) == Symbol("StmObserve")
            # print("OBSERVE {}".format(get_body(cmd)[1][1]))

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

if __name__ == "__main__":
    main()
