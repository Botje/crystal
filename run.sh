#!/bin/sh
rundir=`dirname $0`
exec $rundir/dist/build/crystal/crystal "$@"
