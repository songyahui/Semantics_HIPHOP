# TempAS: A Temporal Verification Tool for Mixed Async-Sync Concurrency

## Tool Overview

To make reactive programming more concise and flexible, it is promising to deploy a mixed concurrency paradigm that integrates Esterel's synchrony and preemption with JavaScript's asynchrony. Existing temporal verification techniques haven't been designed to handle such a blending of two concurrency models. We propose a novel solution via a compositional Hoare-style forward verifier and a term rewriting system (TRS) on Timed Synchronous Effects (TSE). Firstly, we introduce TSE, a new effects logic, that extends Kleene Algebra with value-dependent constraints, providing real-time bounds for logical-time synchronous traces. Secondly, we establish an (the first) abstract denotational semantics for HipHop.js, generalising the mixed paradigm. Thirdly, we present a purely algebraic TRS, to efficiently check language inclusions between expressive timed effects. To demonstrate the feasibility of our proposals, we prototype the verification system; prove its correctness; investigate how it can help to debug errors related to both synchronous and asynchronous programs.


## Online Demo 

Example programs (on the left panel) can be run ONLINE.


## The Front End: Forward Verifier

Targeting a core language \lambda_{HH}, we establish an abstract semantics model via a set of inductive transition rules, enabling a compositional verifier to infer the program's effects. The verifier triggers the back-end solver TRS.


## The Back End: A TRS


sudo -s -H

brew install gmp

brew link --overwrite gmp

sudo chown www-data:www-data trs


SLEEK_COLOR=off dune exec ./trs.exe src/effects/0_Single_Instant.ee

dune exec ./hip.exe src/programs/paper_example.hh





