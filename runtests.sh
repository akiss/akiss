#!/bin/sh

today=`date +%m%d`
dir="test_${today}_$1"

mkdir $dir || exit 1
cp *.ml Makefile $dir
chmod -w $dir/*

cp $2 $dir

cd $dir
make || exit 1

# Run tests in the same order as on the command line
for i in $2 ; do
  i=`basename $i`
  mkdir $i.test
  cd $i.test
  echo -n "Running test $i... "
  date > log
  OCAMLRUNPARAM=b time ../akiss -verbose -debug >> log 2> time < ../$i
  ret=$?
  echo Exit $ret >> log
  date >> log
  if [ $ret = 0 ] ; then
    echo OK
  else
    echo FAILURE
  fi
  cd ..
done
