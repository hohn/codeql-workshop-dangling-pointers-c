#!/bin/sh

# This script copies Exercise#.c files to the appropriate sub-directories
[[ $(git rev-parse --show-toplevel) == $(pwd) ]] || {
    echo "This script must be run from the root of the workshop repository."
    exit 1
}

SRCDIR=$(pwd)/tests/common

target_dirs=(
    $(pwd)/tests/solutions
    $(pwd)/tests/exercises
)

for dir in "${target_dirs[@]}"; do
    for i in {1..4}; do
        cp $SRCDIR/test.c $dir/Exercise$i/test.c
    done
done

exit 0
