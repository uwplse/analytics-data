#!/bin/bash

userid=$1
sessionid=$2

if [ "$1" == "" ] || [ "$2" == "" ]; then
    echo "Usage: ./commit-diffs.sh {user-id} {session-id}"
    exit 0
fi

script=`realpath $0`
path=`dirname $script`
outfile="${path}/user-${userid}-session-${sessionid}.v"
diffpath="${path}/../diffs-annotated-fixed/${userid}"

# Spit the replay data to a file
printf "${userid}\n${sessionid}\n" | python3 replay.py > ${outfile}

# Convert BackTo and Backtrack to comments as well
sed -i -re 's/\(\*[0-9]+:\*\).*BackTo ([0-9]+)\./\(\*BACKTO \1\*\)/' ${outfile}
sed -i -re 's/\(\*[0-9]+:\*\).*Backtrack ([0-9]+) [0-9]+ [0-9]+\./\(\*BACKTO \1\*\)/' ${outfile}

# Now call find-refactors
python3 find-refactors.py ${outfile} ${diffpath}

# Remove the unsplit file
rm ${outfile}

# Commit each diff one at a time
numdiffs=$(find ${diffpath} -name "user-${userid}-session-${sessionid}*" | wc -l)
for (( i=0; i<${numdiffs}; i++ ))
do
    frompath="${diffpath}/user-${userid}-session-${sessionid}-${i}.v"
    topath="${diffpath}/user-${userid}-session-${sessionid}.v"
    mv ${frompath} ${topath}
    # Clean up extra output
    sed -i -re '/^Set Silent\./d' ${topath}
    sed -i -re '/^Unset Silent\./d' ${topath}
    sed -i -re '/^Set Diffs "off"\./d' ${topath}
    sed -i -re '/^Set Printing Width [0-9]+\./d' ${topath}
    sed -i -re '/^Show\./d' ${topath}
    sed -i -re '/^Locate .*\./d' ${topath}
    sed -i -re '/^Timeout [0-9]+ Check .*\./d' ${topath}
    sed -i -re '/^\(\* Auto-generated comment: Missing state\. \*\)/d' ${topath}
    # Add and commit
    git add ${topath}
    git commit -m "user ${userid}, session ${sessionid}, part ${i}"
done

