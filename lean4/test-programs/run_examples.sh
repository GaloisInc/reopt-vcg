#!/bin/bash

totalAnnCount=$(ls -lR ./*.ann | wc -l)

echo "Running reopt-vcg on ${totalAnnCount} annotation files..."

for example in *.ann; do
  [ -f "$example" ] || break
  baseName="${example%.*}"
  expectedDir="${baseName}_output_original"
  actualDir="${baseName}_output_actual"

  printf "\n>> Running reopt-vcg for test case ${baseName}...\n"
  
  if [[ ! -d "$expectedDir" ]]
  then
    echo ">> ERROR! Missing expected directory ${expectedDir}"
    exit
  fi

  if [[ ! -d ${actualDir} ]]
  then
    mkdir ${actualDir}
  else
    rm -f ${actualDir}/*.smt2
  fi

  echo ">> Generating SMT queries..."
  ../build/reopt-vcg ${example} --export ${actualDir}
  actualSmtQueryCount=$(ls -lR ${actualDir} | wc -l)
  expectedSmtQueryCount=$(ls -lR ${actualDir} | wc -l)
  if [[ ${actualSmtQueryCount} == ${expectedSmtQueryCount} ]]
  then
    echo ">> Done generating all ${actualSmtQueryCount} SMT queries."
  else
    echo ">> Done generating ${actualSmtQueryCount} SMT queries."
    echo ">> (Warning: the expected folder contained ${expectedSmtQueryCount} SMT queries)"
  fi

  echo ">> Querying CVC4..."
  failCnt=0
  for q in ${actualDir}/*.smt2; do
    result=$(cvc4 ${q})
    if [[ $result != "unsat" ]]; then
      failFiles[$failCnt]=$q
      failResults[$failCnt]=$result
      ((failCnt++))
    fi
  done

  if [[ $failCnt -gt 0 ]]
  then
    echo ">> ${failCnt} queries out of ${actualSmtQueryCount} failed for ${example}:"
    for ((i = 0 ; i < failCnt ; i++ )); do
      echo ">> ${failFiles[0]} produced: "
      echo "${failResults[1]}"
    done
  fi

  echo ">> Done processing ${baseName} test case."
done
