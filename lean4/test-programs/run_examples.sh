#!/bin/bash

totalAnnCount=$(ls -lR ./*.ann | wc -l)

echo "Running reopt-vcg on ${totalAnnCount} annotation files..."

for i in *.ann; do
  [ -f "$i" ] || break
  baseName="${i%.*}"
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
  ../build/reopt-vcg ${i} --export ${actualDir}
  actualSmtQueryCount=$(ls -lR ${actualDir} | wc -l)
  expectedSmtQueryCount=$(ls -lR ${actualDir} | wc -l)
  if [[ ${actualSmtQueryCount} == ${expectedSmtQueryCount} ]]
  then
    echo ">> Done generating all ${actualSmtQueryCount} SMT queries."
  else
    echo ">> Done generating ${actualSmtQueryCount} SMT queries."
    echo ">> (Warning: the expected folder contained ${expectedSmtQueryCount} SMT queries)"
  fi


  echo ">> Done processing ${baseName} test case."
done
