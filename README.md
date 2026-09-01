# Formalized Latency Bounds for Stacked Proofs of Space

This repository formalizes in Lean 4 a static latency lower bound for a
15-layer stacked proof-of-space graph. The vertical wiring is one uniformly
sampled permutation of the `8n` ports `Fin 8 × Fin n`, reused between all
consecutive layers.

## Main result

[`chung8_pebbling_latency_15`](Challenge.lean) proves that, under explicit
within-layer depth-robustness, pebbling-budget, and security
conditions, there is an unpebbled directed path ending in a sufficiently large
red-free challenge set and having length at least

```text
(1/5)n + (1/5 - 74/625)n = (176/625)n = 0.2816n
```

with failure probability at most `2^(-lambda)`.

[`chung8_pebbling_latency_whp`](Challenge.lean) is the reusable probabilistic
form of the general, break-aware latency theorem. Its parameters are symbolic and
its conclusion is the explicit lower bound
`απ*n + (z_min(ℓ)-1)*(απ-σ)*n`, under the uniform interlayer law, with
failure probability at most `2^(-lambda)`.

The result concerns a static black/red pebbling snapshot. It does not formalize
a time-indexed cryptographic game, a reduction from path length to running time,
or an equivalence between Filecoin's deployed Feistel wiring and the uniform
port-permutation model.

## Repository layout

- [`Challenge.lean`](Challenge.lean) contains the public definitions and the two
  theorem statements, with proof bodies replaced by `sorry`.
- [`Solution.lean`](Solution.lean) proves those statements from the library.
- [`ProofOfSpace/`](ProofOfSpace/) contains the deterministic latency argument,
  the 15-layer specialization, and the expansion probability bound.
- [`ProofOfSpace.lean`](ProofOfSpace.lean) imports the complete development.

## Verification

```bash
lake build
./scripts/verify-comparator.sh
```

The comparator checks the registered theorem
`ProofOfSpaceStatement.chung8_pebbling_latency_15`, its permitted axioms, and
NanoDa replay using the pinned toolchain.

The development builds on Leonid Reyzin's *Proofs of Space with Maximal
Hardness* (FOCS 2024) and Ben Fisch's *Tight Proofs of Space and Replication*
(EUROCRYPT 2019). Licensed under Apache-2.0.
