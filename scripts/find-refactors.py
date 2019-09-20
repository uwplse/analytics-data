#!/usr/bin/env python

import sys
import os
import os.path
import re

# Make sure we pass the file name
if len(sys.argv) < 3:
    print("Usage: python3 find-refactors.py <input-filename> <output-dir>")
    exit(1)

# Get the file, failing if it does not exist
fpath = sys.argv[1]
if not os.path.exists(fpath):
    print("Error: " + fpath + " does not exist")
    exit(1)

# Get the output directory, failing if it does not exist
outdir = sys.argv[2]
if not os.path.exists(outdir):
    print("Error: " + outdir + " does not exist")
    exit(1)

# Group by failures and cancellations; for now, don't differentiate between these
group_ends = []
group_starts = []
group_cancels = []
group_lines = []
failure_or_cancellation = "(\(\*(CANCEL|FAILED|BACKTO).*([0-9]+)\*\)\s+)"
with open(fpath, 'r') as f:
    groups = re.split(failure_or_cancellation, f.read())
    for group_num, group in enumerate(groups, start = 0):
        cancel_match = re.match(failure_or_cancellation, group)
        if cancel_match is None:
            _, *lines = re.split("\s*\(\*", group)
            for line_num, line in enumerate(lines, start = 0):
                line = "(*" + line.strip()
                state_num = int(re.search("\(\*(\d+):\*\)", line).group(1))
                if line_num == 0:
                    group_starts.append(state_num)
                if line_num == len(lines) - 1:
                    group_ends.append(state_num)
                line = re.sub("\(\*(\d+):\*\)\s+", "", line)
                lines[line_num] = line
            if (len(lines) > 0):
                group_lines.append(lines)
        else:
            state_num = int(re.search("([0-9]+)\*\)", group).group(1))
            if (len(group_cancels) > 0 and len(group_cancels) == len(group_starts)):
                group_cancels.pop()
            group_cancels.append(state_num)

# Now go through the cancellations and find diffs
if len(group_lines) > 0:
    old_cumulative = group_lines[0]

    for i in range(group_starts[0]):
        old_cumulative.insert(0, "")
else:
	exit(0) # Comment below and uncomment this line when we don't include compiles
    #old_cumulative = [] # Comment above and uncomment this line when we include compiles

if len(group_lines) == 1:
	exit(0) # Comment this out/remove this condition if we include compiles

# Dump initial version to file
(fname, fext) = os.path.splitext(os.path.basename(fpath))
with open(outdir + "/" + fname + "-" + str(0) + fext, 'w') as f:
     for curr_index in range(len(old_cumulative)):
        if old_cumulative[curr_index] != "":
            old = old_cumulative[curr_index]
            f.write(old + "\n")

for i in range(len(group_ends) - 1):
    j = i + 1

    # Where is the first cancellation?
    cancel_index = group_cancels[i]

    # Up to the cancellation, no changes
    new_cumulative = []
    curr_index = 0
    while (curr_index <= cancel_index):
        new_cumulative.append(old_cumulative[curr_index])
        curr_index = curr_index + 1

    # Write in the changed state
    new_cumulative.append(group_lines[j][0])
    curr_index = curr_index + 1

    # Write in the remaining lines, if applicable
    if len(group_lines[j]) > 0:
        final_state = group_ends[j]
        next_state = final_state - len(group_lines[j]) + 1

        # Write in the offset lines
        while curr_index <= next_state:
            new_cumulative.append("")
            curr_index = curr_index + 1

        # Write in the post-offset lines
        while curr_index <= final_state:
            new_cumulative.append(group_lines[j][curr_index - next_state])
            curr_index = curr_index + 1

    # Dump new version to file
    with open(outdir + "/" + fname + "-" + str(j) + fext, 'w') as f:
        for curr_index in range(len(new_cumulative)):
            if new_cumulative[curr_index] != "":
                new = new_cumulative[curr_index]
                f.write(new + "\n")

    # Now switch to use the new cumulative file
    old_cumulative = new_cumulative

# If we end with a cancellation, take that into account
if (len(group_cancels) > 0 and len(group_cancels) == len(group_starts)):
    cancel_index = group_cancels[-1]

    # Up to the cancellation, no changes
    new_cumulative = []
    curr_index = 0
    while (curr_index <= cancel_index):
        new_cumulative.append(old_cumulative[curr_index])
        curr_index = curr_index + 1

    # Dump new version to file
    with open(outdir + "/" + fname + "-" + str(j + 1) + fext, 'w') as f:
        for curr_index in range(len(new_cumulative)):
            if new_cumulative[curr_index] != "":
                new = new_cumulative[curr_index]
                f.write(new + "\n")

