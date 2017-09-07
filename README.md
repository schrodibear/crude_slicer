# Crude reachability slicer

This is an initial version of a dataflow analysis-based reachability slicer for
verification tasks prepared from Linux device drivers. The slicer is intended to be used with a reachability verifier e.g.
[CPAchecker](https://cpachecker.sosy-lab.org), [Ultimate Automizer](https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/?ui=tool&tool=automizer), [CBMC](http://www.cprover.org/cbmc) or any other one. The basic idea is to perform slicing *modulo termination*.
So the slicer works under assumption that all the code except for explicitly specified functions
necessary terminates and thus can be removed if it doesn't influence reachability throgh data flow.

Currently the slicer doesn't output any intermediate analysis artifacts e.g. inferred function effect (assigns-from) summaries used to obtain the sliced code. Other important missing features:
  - Separate dependencies for reachability of targets from current function and caller functions
  - Support for slicing targets other than reachability of error function calls (e.g. memory safety for particular types or functions)
  - Simultaneous support for multiple separate slicing targets and corresponding dependencies; splitting code into multiple sliced tasks, one per each slicing target
  - Inference and output of function effect summaries; inference of simple explicit-analysis-based summaries where current region analysis is able to fully resolve aliases (single target)
  - SSA-rewriting for variables in function bodies to further improve precision of the dataflow analysis (and region analysis).

Current results are quite promising: +200% correct verdicts, -58% unknown verdicts with [CPAchecker](https://cpachecker.sosy-lab.org) (```-ldv``` configuration) on ```linux-4.2-rc1``` subset (432 drivers) of ```DeviceDrivers64``` benchmarks from the [SV-COMP](https://sv-comp.sosy-lab.org) tasks.

The slicer is a [Frama-C](http://frama-c.com) plugin. It requires Frama-C ```Silicon-20161101```. After installing Frama-C, the plugin should be built and installed as follows (no OPAM package yet):
```bash
    make
    make install
```

Usage (tasks obtained from 64-bit Linux drivers, will print currently analyzed function names):
```bash
    frama-c -machdep gcc_x86_64 -debug 2 -crude_slicer -print -ocode <output file> <input file>
```

**WARNING**: This is still a *prototype*! The slicer is not yet released.
