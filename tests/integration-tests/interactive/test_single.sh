#!/usr/bin/env bash
if [ $# -ne 3 -a $# -ne 2 ]; then
    echo "Usage: test_single.sh test-file [reopt-vcg-exe-path] [yes/no]?"
    exit 1
fi


CVC4_PATH=$(which cvc4)
if [[ ! ( -x $CVC4_PATH || -h $CVC4_PATH) ]]; then
    CVC4_PATH="$PWD/../../../deps/cvc4-2020-09-16-x86_64-linux-opt --lang=smt2 --arrays-exp --no-fmf-bound --incremental"
else
    CVC4_PATH="$CVC4_PATH --lang=smt2 --arrays-exp --no-fmf-bound --incremental"
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
$TEST_EXE "-v" --alt-backend "$testname" --solver "$CVC4_PATH" 2>&1 | sed 's|does\\not\\exist|does/not/exist|' | sed "/warning: imported file uses 'sorry'/d" | sed "/warning: using 'sorry'/d" | sed "/failed to elaborate theorem/d" | sed "s|^$ff|$f|" > "$f.produced.out"
if test -f "$f.expected.out"; then
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
    echo "ERROR: file $f.expected.out does not exist"
    if [ $INTERACTIVE == "yes" ]; then
        read -p "copy $f.produced.out (y/n)? "
        if [ $REPLY == "y" ]; then
            cp -- "$f.produced.out" "$f.expected.out"
            echo "-- copied $f.produced.out --> $f.expected.out"
        fi
    fi
    exit 1
fi
