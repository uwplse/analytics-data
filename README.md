This public repository hosts the data for the [REPLICA](https://github.com/uwplse/coq-change-analytics) study, the paper for which will be published soon.

# Data

The raw data is in the [raw](/raw) directory.

Processed data for Q2 is in the [diffs-annotated-fixed-2](/diffs-annotated-fixed-2)
directory. Processed data for Q2 _including timestamps_ is in the
[diffs-annotated-with-times](/diffs-annotated-with-times) directory.
You can use the Git history to look back at the sessions referenced 
within the paper.

# Analysis

Please contact us if you have any issues running our scripts.

## Q1

To reproduce the numbers reported for Q1:

1. `cd raw`
2. `tar xzf logs.tar.gz`
3. `python3 ../scripts/q1/cancellation_info.py`
(You'll need to wait a while after this command, while the raw logs are split into sessions.)
4. Read the output for information about raw cancellation
5. `python3 ../scripts/q1/proof_graphs.py`
6. Read the output for information about cancellations and their replacement commands
7. In the `graphs/` directory, you'll find svgs of proof flow graphs.

## Q2

To reproduce the Git commits for the Q2 analysis, first create a new directory
within the project, and then modify this line:

```
diffpath="${path}/../../diffs-annotated-fixed-2/${userid}"
```

in [commit-diffs.sh](/scripts/q2/commit-diffs.sh) to point to it
(or [commit-diffs-timestamps](/scripts/q2/commit-diffs-timestamps) if you
would like annotatations for timestamps).
Also add subdirectories in your new directory for each user, with the names
0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, and 11.
Then, just run [commit-all-diffs.sh](/scripts/q2/commit-all-diffs.sh)
(or [commit-all-diffs-timestamps.sh](/scripts/q2/commit-all-diffs-timestamps.sh)
if you would like annotations for timestamps)
from within its directory. You can then look at the Git history
to see the processed data.

To find out what the name of the module a particular session corresponds to, 
you can modify the [/scripts/q2/replay.py](replay) script to

The [changes](/changes) directory contains a complete
[list of all of the changes](/changes/all-changes.md)
that we found in the manual analysis of this processed data, as well as
[benchmarks from the paper](/changes/benchmarks.md), with links to the relevant diffs.

# Important Notes

Please do reuse our data if it helps you!
But before you do, please read the paper, especially the discussion section, 
for information about the data before you interpret it.
And please read the notes below.

For example, as we note in the paper, we could not automatically 
distinguish failures from user backtracking for User 5.
So even though processed data is annotated with "success" and "failure," 
for User 5, it will always appear as "success," and you must manually inspect the
data in question to determine whether this is actually a success.

Likewise, due to a bug in CoqIDE and Proof General that we have reported and that
is fixed in the latest Coq version, we could not always determine the name of the
module that corresponds to a given session. For impacted users, the module will
always appear as "Top." This means that manual analysis is needed in order to determine
if two sessions refer to the same file.

Finally, the timestamp data for User 1 is corrupt for some files.
It seems like this is true for User 11 sometimes, too.
And the final commit for all users often does not have a timestamp.
The processed data lists timestamps, but the list of changes says "Unknown"
when this happens. In general, timestamp data in the analysis is 
_very experimental_ and was added only for the camera-ready in response
to reviewer feedback; we make claims about it in the paper only when
we are absolutely certain that those claims are correct, and are not sure
why the analysis sometimes does not return the right number of timestamps for 
Users 1 and 11.

