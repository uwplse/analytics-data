#!/usr/bin/env python3

from tqdm import tqdm
from datetime import datetime
import argparse
import os
import shutil

from common import *

logdir = "../raw/logs"

def split_sessions(user):
    user_sessions_dir = f"{logdir}/{user}-sessions"
    shutil.rmtree(user_sessions_dir, ignore_errors=True)
    os.mkdir(user_sessions_dir)

    with open(os.path.join(logdir, user), 'r') as logfile:
        for line in tqdm(logfile):
            entry = try_loads(line)
            session_stamp = get_session(entry)
            session_label = datetime.fromtimestamp(float(session_stamp)).isoformat()
            session_path = f"{user_sessions_dir}/{session_label}"
            with open(session_path, 'a') as session_file:
                session_file.write(line)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--user", type=str, default="0")
    args = parser.parse_args()
    users = sorted([f for f in os.listdir(logdir)
                    if os.path.isfile(os.path.join(logdir, f))])
    assert args.user in users, f"User {args.user} does not exist!"
    split_sessions(args.user)


if __name__ == "__main__":
    main()
