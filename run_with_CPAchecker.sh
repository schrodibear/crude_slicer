#!/bin/bash

FILE=$1

frama-c -crude_slicer \
        -timeout 400 \
        -no-recognize_wrecked_container_of \
        -widening_threshold 2000 \
        -no-summaries \
        -no-assert_stratification \
        -oslice $FILE.slice \
        -print \
        -ocode $FILE.sliced.c \
        $FILE

CPADIR=$(dirname $(which cpa.sh))/..

cpa.sh -heap 8000m \
       -ldv-bam-svcomp \
       -setprop 'analysis.checkCounterexamples=TRUE' \
       -setprop 'counterexample.checker=CPACHECKER' \
       -setprop "counterexample.checker.config=$CPADIR/config/cex-checks/predicateAnalysis-as-bitprecise-cex-check.properties" \
       -setprop 'output.disable=TRUE' \
       -setprop 'cpa.arg.export=TRUE' \
       -setprop "cpa.arg.proofWitness=$FILE.correctness-witness.graphml" \
       -setprop 'counterexample.export.exportWitness=TRUE' \
       -setprop "counterexample.export.graphml=$FILE.violation-witness.graphml" \
       -setprop 'log.consoleLevel=INFO' \
       -setprop "cfa.slicePostfix=.slice" \
       -spec "$CPADIR/config/specification/sv-comp-reachability.spc" \
       $FILE
