This public repository hosts the data for the [REPLICA](https://github.com/uwplse/coq-change-analytics) study, the paper for which will be published soon.

# Data

The raw data is in the [raw](/raw) directory.

Processed data for Q2 is in the [diffs-annotated-fixed-2](/diffs-annotated-fixed-2)
directory. You can use the Git history to look back at the sessions referenced 
within the paper.

# Analysis

Please contact us if you have any issues running our scripts.

## Q1

Instructions for reproducing Q1 are a work in progress.

## Q2

To reproduce the Git commits for the Q2 analysis, first create a new directory
within the project, and then modify this line:

```
diffpath="${path}/../../diffs-annotated-fixed-2/${userid}"
```

in [commit-diffs.sh](/scripts/q2/commit-diffs.sh) to point to it.
Also add subdirectories in your new directory for each user, with the names
0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, and 11.
Then, just run [commit-all-diffs.sh](/scripts/q2/commit-all-diffs.sh)
from within its directory. You can then look at the Git history
to see the processed data.

Soon, I will include a file that contains a complete list of all of the changes
that we found in the manual analysis of this processed data,
with links to benchmarks mentioned in the paper.
