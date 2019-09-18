#!/bin/bash

# All done with failures. Without failure version not done yet.

# User 0 (w/ failures version is done forever)
for i in {0..5}
do
    ./commit-diffs.sh 0 ${i}
done

# User 1 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..41}
do
    ./commit-diffs.sh 1 ${i}
done

# User 2 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..6}
do
    ./commit-diffs.sh 2 ${i}
done

# User 3 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..11494}
do
    ./commit-diffs.sh 3 ${i}
done

# User 4 (w/ failures version is done forever)
for i in {0..0}
do
    ./commit-diffs.sh 4 ${i}
done

# User 5 (w/ failures version is done forever)
for i in {0..40}
do
    ./commit-diffs.sh 5 ${i}
done

# User 6 (w/ failures version is done forever)
for i in {0..0}
do
    ./commit-diffs.sh 6 ${i}
done

# User 7 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..228}
do
    ./commit-diffs.sh 7 ${i}
done

# User 8 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..161}
do
    ./commit-diffs.sh 8 ${i}
done

# User 9 (w/ failures version is done forever)
for i in {0..4}
do
    ./commit-diffs.sh 9 ${i}
done

# User 10 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..22}
do
    ./commit-diffs.sh 10 ${i}
done

# User 11 (w/ failures version is done; extra unset silents kind of unpleasant though)
for i in {0..16}
do
    ./commit-diffs.sh 11 ${i}
done


