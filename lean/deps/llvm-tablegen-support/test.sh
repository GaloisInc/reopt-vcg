#!/bin/bash -e

BINARY=$1
START=`printf %d 0x$2`
LASTP1=`printf %d 0x$3`
NBYTES=$(($LASTP1 - $START))

# no mkstemp?
TMPBIN=`mktemp`
OBJCOPY=gobjcopy
OBJDUMP=gobjdump

SECSTART=`$OBJDUMP -w -h -j .text $BINARY | awk '$2 ~ ".text" { printf "0x%s", $4}'`

SKIP=$(( $START - $SECSTART ))

# echo "START = $START, SECSTART = $SECSTART"
# echo "SKIP = $SKIP"
$OBJCOPY --dump-section .text=$TMPBIN $BINARY
dd if=$TMPBIN bs=1 count=$NBYTES skip=$SKIP | ./llvm-tablegen-support $NBYTES
rm $TMPBIN

