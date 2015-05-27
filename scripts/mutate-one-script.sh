#!/bin/sh
seq=$1
input=$2
fname=out/`basename $input .chicken`.$seq

~/Development/CrystalHS/run.sh --mutate $input > ${fname}.mut 2> ${fname}.err
perl -0777 -pe 's/.*\Q<![CDATA[//s; s/\Q]]>\E.*//s; print "\n"; s/^/;  /gm' ${fname}.err >> ${fname}.mut
rm ${fname}.err
