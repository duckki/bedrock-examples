#!/bin/bash

#==============================================================================
# Configurations
#==============================================================================
BEDROCK=bedrock
OPTS="-R $BEDROCK/src Bedrock -I $BEDROCK/examples"
SRCS="myfactorial myfactorial-safe search-max"

#==============================================================================
# Implementation
#==============================================================================
function run_coq {
  coqtop $OPTS -batch -l $1 | head 2>&1
  return $PIPESTATUS
}

function check {
  echo -n "Checking $1 ..."
  OUTPUT=`run_coq $1`
  RVAL=$?
  if [ $RVAL == 0 ]; then
    echo " OK"
    return 0
  fi
  echo " Error[$RVAL]:"
  echo $OUTPUT
}

TIMEFORMAT='	%2R real	%2U user	%2S system'

if [ X$1 != 'X' ]; then
  time check $1
else
  for FILE in $SRCS; do
   time check $FILE
  done
fi
