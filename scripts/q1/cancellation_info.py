#!/usr/bin/env python3

import collections
import re
from data_format import get_users, get_sessions, get_commands
from common import (isCancel, isAdd, get_stem, getAddBody,
                    isVernacCmd, isVernacKeyword, isGoalPunctuation,
                    preprocess_failures, preprocess_vernac_backtrack,
                    isFailed, eprint, get_user, sublist_contained,
                    get_id, getCancelDest)
from sexpdata import loads, dumps

logdir = "logs"

def main():
    def addToTacPairCount(table, tac1, tac2):
        if re.match("[-+*\{\}]", tac1) or re.match("[-+*\{\}]", tac2):
            return
        if isVernacCmd(tac1) or isVernacCmd(tac2):
            return
        stem1 = get_stem(tac1)
        stem2 = get_stem(tac2)
        table[(stem1, stem2)] += 1

    def addToTacticCount(table, tactic):
        if re.match("[-+*\{\}]", tactic):
            return
        if isVernacCmd(tactic):
            return
        stem = get_stem(tactic)
        table[stem] += 1

    with open("users.txt", 'r') as usersfile:
        profiles = loads(usersfile.read())

    all_tactics_count = collections.Counter()
    prev_count = collections.Counter()
    failed_prevs_count = collections.Counter()
    next_count = collections.Counter()
    cancelled_replaced_pairs = collections.Counter()
    cancel_lengths = collections.Counter()
    previous_tactic = ''
    just_cancelled = False
    just_failed = False
    total_cancels = 0
    total_failures = 0
    full_matching_cancels = 0
    matching_stem_cancels = 0
    for user in get_users(logdir):
        for session in get_sessions(logdir, user):
            cmds = get_commands(logdir, user, session)
            is_interactive = sublist_contained(cmds, [isCancel, lambda entry: not isCancel(entry)])
            if not is_interactive:
                continue
            preprocessed_cmds = preprocess_vernac_backtrack(
                preprocess_failures(profiles, cmds))
            cancel_lengths += get_cancel_lengths(preprocessed_cmds)

            history = []
            for dat in preprocessed_cmds:
                if isAdd(dat):
                    added_tactic = getAddBody(dat)
                    if not isVernacCmd(added_tactic) and \
                       not isGoalPunctuation(added_tactic):
                        stem = get_stem(added_tactic)
                        assert not isVernacKeyword(stem), added_tactic
                        assert stem.strip() != "", added_tactic
                        all_tactics_count[stem] += 1
                    if just_cancelled:
                        addToTacticCount(next_count, added_tactic)
                        addToTacPairCount(cancelled_replaced_pairs,
                                          previous_tactic, added_tactic)
                        if previous_tactic.strip() == added_tactic.strip():
                            full_matching_cancels += 1
                        try:
                            if get_stem(previous_tactic) == get_stem(added_tactic):
                                matching_stem_cancels += 1
                        except:
                            pass
                        just_cancelled = False
                    previous_tactic = added_tactic
                    history.append((get_id(dat)-1, added_tactic))
                if isCancel(dat):
                    total_cancels += 1
                    just_cancelled = True

                    cancel_dest = getCancelDest(dat)
                    while len(history) > 0 and history[-1][0] != cancel_dest:
                        state_num, tactic = history.pop()
                        addToTacticCount(prev_count, tactic)

                if isFailed(dat):
                    total_failures += 1
                    addToTacticCount(failed_prevs_count, previous_tactic)
    print(cancel_lengths)
    print(f"Of {total_cancels} cancels, {total_failures} were failures ({100 * total_failures / total_cancels:3.2f}%)")
    print(f"Of those cancels, {full_matching_cancels} "
          f"({100 * full_matching_cancels / total_cancels:3.2f}%) "
          f"were replaced with the exact same tactic, "
          f"and {matching_stem_cancels} "
          f"({100 * matching_stem_cancels / total_cancels:3.2f}%) "
          f"were replaced by a tactic with the same stem")
    print("All tactics:")
    for tactic, count in all_tactics_count.most_common(50):
        print(f"{tactic}: {count} occurances")
    print("Tactics before cancel:")
    for tactic, count in prev_count.most_common(25):
        print(f"{tactic}: {count} cancels, {failed_prevs_count[tactic]} failures ({100 * failed_prevs_count[tactic] / count:3.2f}%)")
    print("Tactics after cancel:")
    for tactic, count in next_count.most_common(25):
        print(f"{tactic}: {count} run after cancel")
    print(cancelled_replaced_pairs.most_common(25))

def get_cancel_lengths(cmds):
    states = []
    cancel_lengths = collections.Counter()
    for dat in cmds:
        if isAdd(dat):
            states.append(get_id(dat)-1)
        if isCancel(dat):
            cancel_length = 0
            cancel_dest = getCancelDest(dat)
            if len(states) == 0:
                return collections.Counter()
            while states[-1] != cancel_dest:
                cancel_length += 1
                states.pop()
                if len(states) == 0:
                    return collections.Counter()
            cancel_lengths[cancel_length] += 1
    return cancel_lengths


if __name__ == "__main__":
    main()
