# leanbv: Verified SAT Tactic for Bit-vector and Propositional Problems

`leanbv` is supporting the development of a verified SAT-based tactic
for bit-vector and propositional problems.

Please see the [LICENSE](./LICENSE) file for leanbv's licensing and
[CONTRIBUTING.md](./CONTRIBUTING.md) for external contribution
guidelines.

## Summary

Lean users will be able to prove propositional and bit-vector goals by
reduction to SAT, solving with local or cloud-based solvers, and
reconstructing the proof in Lean. Automation is needed to allow Lean
to scale to program verification problems. Existing tactics like
[lean-auto](https://github.com/leanprover-community/lean-auto) allow
Lean to appeal to SMT, but this trusts that the SMT solver is
correct. Validating SMT proofs is a research area, but SAT proofs are
well studied. Moreover, many program verification problems, like
correctness of block ciphers and hashes, need no theories beyond
bit-vectors, and are well suited to automation through SAT.

`leanbv` is a start at a tactic for Lean that can convert proof goals
into SAT problems, invoke a solver, and then soundly interpret SAT and
UNSAT results back into the Lean without the a trusted assumption.
Adding this capability to Lean will enable other projects to apply SAT
solving to their goals.


## LeanSatTactic Status

In `LeanSatTactic`, we have successfully demonstrated the ability to
discharge propositional/Booelan goals in Lean4 via SAT by using the
Lean kernel to encode propositional problems into CNF and also replay
the LRAT proof steps via the
[FromLRAT](https://github.com/leanprover-community/mathlib4/blob/30030d812739262fa821bf91010ecfe37c95ae46/Mathlib/Tactic/Sat/FromLRAT.lean)
library.  However, we suspect that this method will not scale for the
kind of problems users care about.  While improving the efficiency of
the Lean kernel to handle larger contexts and to process tactics is
certainly a possibility, this will require a large amount of effort on
development on Lean as a whole.  Instead, we should focus our efforts
on developing a SAT tactic that appeals to individual utilities that
are proven correct and internalized via reflection.

In order to move away from the Lean kernel, we need to create the
following tools that have associated proofs of correctness and
reflection into Lean.  Note that these tasks can be developed in
parallel depending on interest and support.  We will prioritize
developing a solution as quickly as possible, and then iterating on
that design to improve soundness and performance.

1. Verified Encoding to CNF for Propositional Logic and Bit-vectors
    1. We will initially develop an unverified encoding via conversion
       to AIG (And-Inverter Graphs) and then to CNF.
    2. Once this is completed, we can begin to prove soundness of our
       implementation
2. Verified LRAT Proof Checker.  See Josh Clune's
   [leansat](https://github.com/leanprover/leansat).
    1. Further develop LeanSAT (verified LRAT proof checker) into a
       standalone tactic that is capable of adding a negated CNF
       formula to the local context based on the formula and proof
       given to the checker.

There are several opportunities for collaboration with academic groups
and the Lean community.  We will use Zulip to coordinate our efforts.

## Prerequisites

1. Install [CaDiCaL](https://fmv.jku.at/cadical/),
   and make sure that it is in your path.

2. Install Lean4 and your preferred editor's plug-in on your machine
   by following [these instructions](https://leanprover-community.github.io/get_started.html).

## Build Instructions

Run `lake build` at the top-level of leanbv.

## Directory Overview

- `LeanSatTactic`: Demonstration of verified Lean SAT tactic using
  Lean kernel.
