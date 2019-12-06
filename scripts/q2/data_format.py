#!/usr/bin/env python3

from typing import List, Tuple, Iterable, Callable
from os import listdir, stat
from os.path import isfile, join, exists
from tqdm import tqdm
from common import try_loads, get_time, eprint
from split_sessions import split_sessions
from sexpdata import loads

DataEntry = List[Tuple[str, str]]

DataFilter = Callable[[DataEntry], bool]

NO_FILTER = lambda entry: True

def get_all_data(logdir : str, f : DataFilter) -> Iterable[DataEntry]:
    users = sorted([f for f in listdir(logdir) if isfile(join(logdir, f))])
    for user in users:
        with open(join(logdir, str(user)), 'r') as logfile:
            for line in tqdm(logfile):
                entry = try_loads(line)
                if entry and f(entry):
                    yield entry

def get_users(logdir):
    return sorted([f for f in listdir(logdir) if isfile(join(logdir, f))])

def get_sessions(logdir, user):
    user_sessions_dir = f"{logdir}/{user}-sessions"
    if not exists(user_sessions_dir) or \
       stat(user_sessions_dir).st_ctime < \
       stat(join(logdir, str(user))).st_mtime:
        eprint(f"Refreshing sessions for user {user} from logfile")
        split_sessions(str(user))
    return [f for f in listdir(user_sessions_dir)]

def get_commands(logdir, user, session_label):
    with open(f"{logdir}/{user}-sessions/{session_label}", 'r') as session_file:
        return sorted(
            [loads(line) for line in session_file.readlines()],
            key=lambda cmd: get_time(cmd))
