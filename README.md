# Formalized Latency Bounds for Stacked Proofs of Space

This repository contains a Lean 4 formalization of latency lower bounds for stacked
proof-of-space graphs. The construction stores data across `ℓ` layers of `n` nodes.
Under explicit expansion, depth-robustness, pebbling-budget, and scalar hypotheses, the
formalization constructs an unpebbled directed path of length `Ω(ℓ n)` in every
sufficiently large red-free challenge footprint. This is the static combinatorial core
of the statement that a cheating prover must perform non-parallelizable work growing
linearly with the number of layers.

All constants are explicit. The quantitative objective is to make the leading constant
as tight as possible, not merely to prove that it is positive. For the unconditional
finite-size degree-eight Filecoin-shaped profile, the potential-ledger analysis proves
that the asymptotic coefficient lies strictly between `0.02135` and `0.02136`.

## The theorem and its scope

The general theorem assumes:

- a concave, strictly increasing expansion profile with the stated reversal and gain
  properties;
- uniform intra-layer depth robustness;
- inter-layer expansion for the predecessor map;
- a global black-pebble budget and a per-layer red-pebble budget;
- a sufficiently large red-free challenge set; and
- the scalar entry conditions collected in `GeneralRegime`.

It returns a nonempty directed path whose nodes carry neither black nor red pebbles,
together with an explicit lower bound on its length. The proof concerns a static
pebbling snapshot. It does not formalize a time-indexed cryptographic game or the final
reduction from path length to sequential running time. Expansion and depth robustness
are hypotheses, not universal construction theorems.

## Palomar submission surface

The Palomar statement of record is
[`ProofOfSpaceStatement.latency_general`](Challenge.lean). `Challenge.lean` imports
only allowlisted Mathlib modules and contains the one deliberate `sorry` permitted in a
challenge statement. [`Solution.lean`](Solution.lean) proves that statement using
[`ProofOfSpace.latency_general`](ProofOfSpace/Latency.lean).
[`comparator.json`](comparator.json) checks that the statements agree and permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The general theorem statement exposes every conditional hypothesis through `Setting`.
The Chung-8 Filecoin specialization is a concrete `Setting` and depends on no global
analytic axiom.

Submission metadata is in [`formalization.yaml`](formalization.yaml), and the project is
licensed under Apache-2.0. A public submission should use the full 40-character commit
SHA at the [Palomar submission form](https://submit.palomar-registry.org/).

## Proof architecture

- `Chung.lean`, `ChungCurve.lean`, `ChungShifted.lean`, and `Expansion.lean` define the
  expansion exponent, construct its zero-level and finite-size roots, and define the
  abstract expansion interface.
- `ChungFilecoinCurve.lean`, `ChungChord.lean`, and `ChungRegion.lean` define the
  rational degree-eight profile used by the Filecoin specialization, prove its shape
  laws, and certify it inside the finite-size Chung region.
- `UnionBound.lean` proves the interlayer expansion claim by the union bound, and
  `ChungExpansion.lean` evaluates its certificate for the degree-eight profile.
- `Footprint.lean` develops normalized pebble budgets and the footprint recurrence.
- `Tracking.lean`, `Search.lean`, and `Continuation.lean` construct fertile and
  expandable searches through the layers.
- `Growth.lean` bounds the cost of growth windows.
- `Potential.lean` defines a piecewise-linear potential along a certified reference
  trajectory.
- `PotentialLedger.lean` prices search steps with that potential and derives the global
  link count.
- `Chain.lean` and `Ledger.lean` organize continuation links and global budget
  accounting.
- `Concrete.lean` instantiates the abstract analysis for finite layered graphs and
  splices the links into a directed path.
- `Latency.lean` states the public latency theorems.
- `ChungNumerics.lean` and `ChungFilecoin.lean` prove the degree-eight numerical
  certificates and the optimized asymptotic coefficient.
- `Constructions.lean` states the bounded-indegree graph certificates required by the
  concrete specialization.
- `Witness.lean` gives an unconditional model of the abstract scalar hypothesis stack;
  it is not claimed as a deployed graph profile.

`ProofOfSpace.lean` imports the complete public development.

## Indexing convention

The published layered construction labels the challenge layer `V_ℓ` and the top layer
`V₁`. Lean counts forward from the challenge: `layer 0` corresponds to `V_ℓ`,
`layer (ℓ - 1)` corresponds to `V₁`, and edges from `layer (d + 1)` to `layer d` move
toward the challenge.

## Filecoin construction and open graph hypotheses

The specialization targets the deployed Filecoin SDR graph — the degree-eight
Chung/Feistel predecessor graph — at Reyzin's Appendix C level `ε_chung = 2⁻²²`. It
requires two graph conditions, both of which occur in theorem types rather than as
project axioms:

1. `LayeredGraph.expands`: the sampled permutation interlayers realize the required
   degree-eight expansion profile.
2. `LayeredGraph.DepthRobust`: each intra-layer graph has the required deletion-set
   depth robustness.

The expansion profile itself is fully proved: a conservative rational polygon, used
because the exact finite-size root cannot serve as a global `Setting.β`, certified over
`[2⁻²⁵, 1 - 2⁻²³]`, below which no profile at all is certifiable at this `ε`.

`UnionBound.lean` and `ChungExpansion.lean` go further and discharge condition 1 for the
development's own sampling model: `chung8_permutationExpansion_whp` states
unconditionally that a uniformly sampled eight-tuple of permutations of a twenty-element
layer realizes the polygon with probability at least `5/6`. That does not cover the
deployed wiring, which selects parents with a Feistel network rather than a uniform tuple
of permutations.

## Build and trust audit

With Lean 4 installed, run:

```bash
lake build
lake env lean scripts/AxiomAudit.lean
```

The first command builds the public dependency graph, Challenge, and Solution. The
second checks every declaration in the `ProofOfSpace` namespace and rejects dependencies
other than `propext`, `Classical.choice`, and `Quot.sound`, including `sorryAx`. Both
checks run in `.github/workflows/lean_action_ci.yml`.

## Published literature

- Leonid Reyzin. *Proofs of Space with Maximal Hardness*. 65th IEEE Symposium on
  Foundations of Computer Science, 2024, 1159–1177.
  [ePrint](https://eprint.iacr.org/2023/1530).
- Ben Fisch. *Tight Proofs of Space and Replication*. Advances in Cryptology –
  EUROCRYPT 2019, Part II, LNCS 11477, 324–348.
  [ePrint](https://eprint.iacr.org/2018/702).
- Filecoin, [SDR protocol specification](https://spec.filecoin.io/algorithms/sdr/) and
  [`rust-fil-proofs` stacked graph implementation](https://github.com/filecoin-project/rust-fil-proofs/blob/master/storage-proofs-porep/src/stacked/vanilla/graph.rs).
