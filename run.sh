#!/bin/sh
rundir=`dirname $0`
$rundir/dist/build/crystal/crystal "$@"
