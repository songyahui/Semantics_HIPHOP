# TempAS: A Temporal Verification Tool for Mixed Async-Sync Concurrency

## Tool Overview

To make reactive programming more concise and flexible, it is promising to deploy a mixed concurrency paradigm that integrates Esterel's synchrony and preemption with JavaScript's asynchrony. Existing temporal verification techniques haven't been designed to handle such a blending of two concurrency models. We propose a novel solution via a compositional Hoare-style forward verifier and a term rewriting system (TRS) on Timed Synchronous Effects (TSE). Firstly, we introduce TSE, a new effects logic, that extends Kleene Algebra with value-dependent constraints, providing real-time bounds for logical-time synchronous traces. Secondly, we establish an (the first) abstract denotational semantics for HipHop.js, generalising the mixed paradigm. Thirdly, we present a purely algebraic TRS, to efficiently check language inclusions between expressive timed effects. To demonstrate the feasibility of our proposals, we prototype the verification system; prove its correctness; investigate how it can help to debug errors related to both synchronous and asynchronous programs.


## Online demo

The easiest way to try the code is to use the [Web UI](http://loris-5.d2.comp.nus.edu.sg/MixedSyncAsync/introduction.html) written
by [Yahui Song](https://www.comp.nus.edu.sg/~yahuis/).

## Getting started

This tool consists of i) <em> a Front End: Forward Verifier</em>; and ii) <em> a Back End: the term rewriting system</em>. 
Below, we provide guidance to build the tool on your local linux machine. 

### 1. Dependencies:

```
opam switch create 4.10.0
eval $(opam env)
sudo apt-get install menhir
sudo apt-get install libgmp-dev
opam install z3
opam install dune
```

### 2. To Compile:

```
git clone https://github.com/songyahui/Semantics_HIPHOP.git
cd Semantics_HIPHOP
cd sleek 
git submodule update --init 
cd ..
dune build
```




### 3. Test fro running:

- (Front End) Program Verification, test files in folder src/programs/*.hh

```
dune exec ./hip.exe src/programs/41_example1.hh
```

- (Back End) Entailments Checking, test files in folder src/effects/*.ee

```
dune exec ./trs.exe src/effects/0_Single_Instant.ee
```

More test files for the Front End are placed in ```src/programs/*.hh```; and more test files for the Back End are placed in ```src/effects/*.ee```.


### 4. To Clean:

``` 
dune clean
```


### Generate test cases and evaluation 

dune exec ./runTest.exe src/microbenchmark/validation_tests/       
dune exec ./Hip.exe src/microbenchmark/evaluation_tests/new_1_test.hh