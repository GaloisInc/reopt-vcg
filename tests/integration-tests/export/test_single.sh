#!/usr/bin/env bash
if [[ $# -lt 1 || $# -gt 3 ]]; then
    echo "Usage: test_single.sh test-file [reopt-vcg-exe-path] [yes/no]?"
    exit 1
fi

ulimit -s 8192

if [ $# -lt 2 ]; then
    TEST_EXE=../../../build/bin/reopt-vcg
else
    TEST_EXE=$2
fi
if [ $# -ne 3 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$3
fi

f=$1
ff=$(bash ./readlinkf.sh "$f")
testname=$(basename "$ff")

if [[ "$OSTYPE" == "msys" ]]; then
    # Windows running MSYS2
    # Replace /c/ with c:, and / with \\
    ff=$(echo $ff  | sed 's|^/\([a-z]\)/|\1:/|' | sed 's|/|\\\\|g')
fi

DIFF=diff
if diff --color --help >/dev/null 2>&1; then
  DIFF="diff --color";
fi

echo "-- testing $f"
rm -fr "$f.produced.out"
mkdir -p "$f.produced.out"
$TEST_EXE --alt-backend "$testname" --export "$f.produced.out" 1> /dev/null
if test -d "$f.expected.out"; then
    if $DIFF -u --ignore-all-space -I "executing external script" "$f.expected.out" "$f.produced.out"; then
        echo "-- checked"
        exit 0
    else
        echo "ERROR: file $f.produced.out does not match $f.expected.out"
        if [ $INTERACTIVE == "yes" ]; then
            meld "$f.produced.out" "$f.expected.out"
            if diff -I "executing external script" "$f.expected.out" "$f.produced.out"; then
                echo "-- mismatch was fixed"
            fi
        fi
        exit 1
    fi
else
    echo "ERROR: directory $f.expected.out does not exist"
    if [ $INTERACTIVE == "yes" ]; then
        read -p "copy $f.produced.out (y/n)? "
        if [ $REPLY == "y" ]; then
            cp -r -- "$f.produced.out" "$f.expected.out"
            echo "-- copied $f.produced.out --> $f.expected.out"
        fi
    fi
    exit 1
fi
