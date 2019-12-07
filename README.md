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

Instructions for reproducing Q1 are a work in progress.

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

Soon, I will include a file that contains a complete list of all of the changes
that we found in the manual analysis of this processed data,
with links to benchmarks mentioned in the paper.
I will also describe how we determined when changes occurred across the same file.
