This public repository hosts the data for the REPLICA study ([paper](http://tlringer.github.io/pdf/analytics.pdf), [tool](https://github.com/uwplse/coq-change-analytics)), a user study of Coq proof engineers.

# Data

The raw data is in the [raw](/raw) directory.

Processed data for Q2 is in the [diffs-annotated-fixed-2](/diffs-annotated-fixed-2)
directory.
You can use the Git history to look back at the sessions referenced 
within the paper.

# Analysis

Before running our scripts, be sure to unzip the raw data:

1. `cd raw`
2. `tar xzf logs.tar.gz`

Please contact us if you have any issues running our scripts.

## Q1

To reproduce the numbers reported for Q1:

1. `cd raw`
2. `python3 ../scripts/q1/cancellation_info.py`
(You'll need to wait a while after this command, while the raw logs are split into sessions.)
3. Read the output for information about raw cancellation
4. `python3 ../scripts/q1/proof_graphs.py`
5. Read the output for information about cancellations and their replacement commands
6. In the `graphs/` directory, you'll find svgs of proof flow graphs.

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
if you would like experimental annotations for timestamps---but see the important
note below about these)
from within its directory. You can then look at the Git history
to see the processed data.

The [changes](/changes) directory contains a complete
[list of all of the changes](/changes/all-changes.md)
that we found in the manual analysis of this processed data, as well as
[benchmarks from the paper](/changes/benchmarks.md), with links to the relevant diffs.

# Important Notes

Please do reuse our data if it helps you!
But before you do, please read the paper, especially the discussion section, 
for information about the data before you interpret it.
And please read the notes below.

**Timestamps**:
Please
do not rely on processed data for timestamps until further notice.
They are correct in the raw data.
We attempted to add these to our analyses in response to reviewer
feedback, but did not do so perfectly the first time around.
The analysis script is flawed in how it treats timestamps for now. 
Intermediate timestamps are in general not yet correct in 
the processed data you see in the linked commits. The start and end timestamps of every session in the benchmarks
are taken from the raw data and are accurate.
Intermediate times, when discussed in the paper and in the benchmark file,
are also taken from the raw data.
I will run a reanalysis at some point after the camera-ready
and update the commits to point to the data with the correct
intermediate timestamps. Sorry for the confusion!

**Failures for User 5**: As we note in the paper, we could not automatically 
distinguish failures from user backtracking for User 5.
So even though processed data is annotated with "success" and "failure," 
for User 5, it will always appear as "success," and you must manually inspect the
data in question to determine whether this is actually a success.

**Module Names**: Due to a bug in CoqIDE and Proof General that we have reported and that
is fixed in the latest Coq version, we could not always determine the name of the
module that corresponds to a given session. For impacted users, the module will
always appear as "Top." This means that manual analysis is needed in order to determine
if two sessions refer to the same file.

**Classification**:
If you are an anonymous user and see any of your data very clearly
misclassified (this can happen, as I am not the author of the code and classification
is hard), feel free to let me know by email, and I will add an errata
and address it here.

