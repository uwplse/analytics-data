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

# Group by cancellations
group_ends = []
group_starts = []
group_lines = []
with open(fpath, 'r') as f:
    groups = re.split("\(\*CANCEL.*\*\)\s+", f.read())
    for group in groups:
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

# Now go through the cancellations and find diffs
old_cumulative = group_lines[0]
for i in range(group_starts[0]):
    old_cumulative.insert(0, "")

# Dump initial version to file
(fname, fext) = os.path.splitext(os.path.basename(fpath))
fdir = os.path.dirname(outdir)
with open(outdir + "/" + fname + "-" + str(0) + fext, 'w') as f:
     for curr_index in range(len(old_cumulative)):
        if old_cumulative[curr_index] != "":
            old = old_cumulative[curr_index]
            f.write(old + "\n")

for i in range(len(group_ends) - 1):
    j = i + 1

    # Where is the first cancellation?
    post_cancel_index = group_starts[j]

    # Up to the cancellation, no changes
    new_cumulative = []
    curr_index = 0
    while (curr_index < post_cancel_index):
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
    with open(fdir + "/" fname + "-" + str(j) + fext, 'w') as f:
        for curr_index in range(len(new_cumulative)):
            if new_cumulative[curr_index] != "":
                new = new_cumulative[curr_index]
                f.write(new + "\n")

    # Now switch to use the new cumulative file
    old_cumulative = new_cumulative


