#!/bin/bash

# User 0
for i in {0..5}
do
    ./commit-diffs.sh 0 ${i}
done

# User 1
for i in {0..41}
do
    ./commit-diffs.sh 1 ${i}
done

# User 2
for i in {0..6}
do
    ./commit-diffs.sh 2 ${i}
done

# User 3
for i in {0..11494}
do
    ./commit-diffs.sh 3 ${i}
done

# User 4
for i in {0..0}
do
    ./commit-diffs.sh 4 ${i}
done

# User 5
for i in {0..40}
do
    ./commit-diffs.sh 5 ${i}
done

# User 6
for i in {0..0}
do
    ./commit-diffs.sh 6 ${i}
done

# User 7
for i in {0..228}
do
    ./commit-diffs.sh 7 ${i}
done

# User 8
for i in {0..161}
do
    ./commit-diffs.sh 8 ${i}
done

# User 9
for i in {0..4}
do
    ./commit-diffs.sh 9 ${i}
done

# User 10
for i in {0..22}
do
    ./commit-diffs.sh 10 ${i}
done

# User 11
for i in {0..16}
do
    ./commit-diffs.sh 11 ${i}
done


