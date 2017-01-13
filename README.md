# Crude reachability slicer

This is an initial version of a dataflow analysis-based reachability slicer for
verification tasks prepared from Linux device drivers. The slicer is intended to be used with a reachability verifier e.g.
[CPAchecker](https://cpachecker.sosy-lab.org), [Ultimate Automizer](https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/?ui=tool&tool=automizer), [CBMC](http://www.cprover.org/cbmc) or any other one. The basic idea is to perform slicing *modulo termination*.
So the slicer works under assumption that all the code except for explicitly specified functions
necessary terminates and thus can be removed if it doesn't influence reachability throgh data flow.

Currently the slicer is quite imprecise. The most important missing features (planned to be implemented *soon*):
  - Polymorphic region-based region (separation) analysis (for more precise handling of memory regions)
  - Special handling of forward gotos (and thus also returns)
  - Special handling of out-of-block (out of switch/loop) gotos
  - Special handling for loop-like goto-patterns:
    ```c
        goto l1;
        l:
        // ...loop body...
        l1:
        if (cond)
            goto l;
    ```
    Unfortunately they arise after instrumenting the code
    with the [C Instrumentation Framework](http://forge.ispras.ru/projects/cif).
  - SSA-rewriting for variables in function bodies to further improve precision of the dataflow analysis (and region analysis).

Nonetheless the current results are quite promising: +114% correct verdicts, -34% unknown verdicts with [CPAchecker](https://cpachecker.sosy-lab.org) (```-ldv``` configuration) on ```linux-4.2-rc1``` subset (425 drivers) of ```DeviceDrivers64``` benchmarks from the [SV-COMP](https://sv-comp.sosy-lab.org) tasks.

The slicer is a [Frama-C](http://frama-c.com) plugin. It requires Frama-C ```Silicon-20161101``` (may probably work with ```Aluminium 20160501``` as well). After installing Frama-C, the plugin should be built and installed as follows (no OPAM package yet):
```bash
    make
    make install
```

Usage (tasks obtained from 64-bit Linux drivers, will print currently analyzed function names):
```bash
    frama-c -machdep gcc_x86_64 -debug 2 -crude_slicer -print -ocode <output file> <input file>
```

**WARNING**: This is still a *prototype*! The slicer is not yet released.
