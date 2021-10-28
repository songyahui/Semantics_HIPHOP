# TempAS: A Temporal Verification Tool for Mixed Async-Sync Concurrency

## Tool Overview

To make reactive programming more concise and flexible, it is promising to deploy a mixed concurrency paradigm that integrates Esterel's synchrony and preemption with JavaScript's asynchrony. Existing temporal verification techniques haven't been designed to handle such a blending of two concurrency models. We propose a novel solution via a compositional Hoare-style forward verifier and a term rewriting system (TRS) on Timed Synchronous Effects (TSE). Firstly, we introduce TSE, a new effects logic, that extends Kleene Algebra with value-dependent constraints, providing real-time bounds for logical-time synchronous traces. Secondly, we establish an (the first) abstract denotational semantics for HipHop.js, generalising the mixed paradigm. Thirdly, we present a purely algebraic TRS, to efficiently check language inclusions between expressive timed effects. To demonstrate the feasibility of our proposals, we prototype the verification system; prove its correctness; investigate how it can help to debug errors related to both synchronous and asynchronous programs.


## Online demo

The easiest way to try the code is to use the [Web UI](http://loris-5.d2.comp.nus.edu.sg/MixedSyncAsync/introduction.html) written
by [Yahui Song](https://www.comp.nus.edu.sg/~yahuis/).

### To Compile:

```
git clone https://github.com/songyahui/Semantics_HIPHOP.git
cd Semantics_HIPHOP
./compile
```

### Dependencies:

```
opam switch create 4.10.0
eval $(opam env)
sudo apt-get install menhir
sudo apt-get install libgmp-dev
opam install z3
```

### Examples:

Entailments Checking 

```
./trs src/effect/ex1.ee src/effect/output.txt 
```

Program Verification

```
./verify src/program/send.c src/program/output.txt
```

### To Clean:

``` 
./clean
```

### Benchmark:

We provide a [Miroc-Benchmark](http://loris-5.d2.comp.nus.edu.sg/Effect/BenchMark.zip) for experiemnts on checking inclusions among regular expressions.

[Arduino]https://create.arduino.cc/projecthub/projects/tags/control

