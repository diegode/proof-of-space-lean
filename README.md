# Formalized Latency Bounds for Stacked Proofs of Space

This repository contains a Lean 4 formalization of latency lower bounds for stacked
proof-of-space graphs. The construction stores data across `ℓ` layers of `n` nodes.
Under explicit expansion, depth-robustness, pebbling-budget, and scalar hypotheses, the
formalization constructs an unpebbled directed path of length `Ω(ℓ n)` in every
sufficiently large red-free challenge footprint. This is the static combinatorial core
of the statement that a cheating prover must perform non-parallelizable work growing
linearly with the number of layers.

All constants are explicit. The quantitative objective is to make the leading constant
as tight as possible, not merely to prove that it is positive. Under the explicit
analytic hypotheses of the degree-eight Filecoin-shaped specialization, the
potential-ledger analysis proves that the asymptotic coefficient lies strictly between
`0.02135` and `0.02136`.

The development builds on:

- Leonid Reyzin, [*Proofs of Space with Maximal Hardness*](https://dblp.org/rec/conf/focs/Reyzin24),
  FOCS 2024, pages 1159–1177.
- Ben Fisch, [*Tight Proofs of Space and Replication*](https://doi.org/10.1007/978-3-030-17656-3_12),
  EUROCRYPT 2019, pages 324–348.

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

The Chung curve itself is constructed for every real degree `d > 2`. The remaining
conditional analytic facts are bundled as `ChungAnalyticHypotheses d`: concavity of the
closed profile and uniqueness of the unadjusted-gain maximizer. Every declaration that
uses them has an explicit `[ChungAnalyticHypotheses d]` parameter. The Filecoin-shaped
numerical certificates specialize the generic curve to degree eight.

## Palomar submission surface

The Palomar statement of record is
[`ProofOfSpaceStatement.latency_general`](Challenge.lean). `Challenge.lean` imports
only allowlisted Mathlib modules and contains the one deliberate `sorry` permitted in a
challenge statement. [`Solution.lean`](Solution.lean) proves that statement using
[`ProofOfSpace.latency_general`](ProofOfSpace/Latency.lean).
[`comparator.json`](comparator.json) checks that the statements agree and permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The theorem statement exposes every conditional hypothesis. The Chung specialization
uses a bundled typeclass in each dependent declaration; there is no global instance or
axiom declaring the analytic hypotheses true.

Submission metadata is in [`formalization.yaml`](formalization.yaml), and the project is
licensed under Apache-2.0. A public submission should use the full 40-character commit
SHA at the [Palomar submission form](https://submit.palomar-registry.org/).

## Proof architecture

- `Chung.lean`, `ChungCurve.lean`, and `Expansion.lean` define the expansion exponent,
  construct the degree-parametric threshold curve, and establish its proved shape laws.
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

## Open hypotheses of the degree-eight specialization

The specialization requires:

1. `LayeredGraph.expands`: the sampled permutation interlayers realize the required
   degree-eight expansion profile.
2. `LayeredGraph.DepthRobust`: each intra-layer graph has the required deletion-set
   depth robustness.
3. `[ChungAnalyticHypotheses 8]`: the closed degree-eight profile is concave and its
   unadjusted gain has a unique maximizer.

Mapping, strict expansion, strict monotonicity, reversal, and the adjusted-gain roots
are proved for the defined curve. The three remaining conditions above occur in theorem
types and are not project axioms.

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
  [DBLP record](https://dblp.org/rec/conf/focs/Reyzin24).
- Ben Fisch. *Tight Proofs of Space and Replication*. Advances in Cryptology –
  EUROCRYPT 2019, Part II, LNCS 11477, 324–348.
  [DOI](https://doi.org/10.1007/978-3-030-17656-3_12).
