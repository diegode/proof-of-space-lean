# Formalized Latency Bounds for Stacked Proofs of Space

This repository contains a Lean 4 development of latency lower bounds for stacked
proof-of-space graphs. It formalizes and extends the footprint and pebbling framework
from two published works:

- Leonid Reyzin, [*Proofs of Space with Maximal Hardness*](https://dblp.org/rec/conf/focs/Reyzin24),
  FOCS 2024, pages 1159–1177.
- Ben Fisch, [*Tight Proofs of Space and Replication*](https://doi.org/10.1007/978-3-030-17656-3_12),
  EUROCRYPT 2019, pages 324–348.

The formalization uses Reyzin's expansion-profile and footprint analysis and Fisch's
stacked depth-robust graph setting. Its main result allows continuation chains to break
and restart: under explicit expansion, intra-layer depth-robustness, pebbling-budget,
and scalar hypotheses, it constructs a nonempty unpebbled directed path from a
challenge footprint with length at least

```text
απ n + (zMin(ℓ) - 1)(απ - σ)n.
```

## Palomar submission surface

The Palomar statement of record is
[`ProofOfSpaceStatement.latency_general`](Challenge.lean). `Challenge.lean` imports
only allowlisted Mathlib modules and contains the one deliberate `sorry`.
[`Solution.lean`](Solution.lean) proves the same statement by invoking the substantive
theorem [`ProofOfSpace.latency_general`](ProofOfSpace/Latency.lean).
[`comparator.json`](comparator.json) asks Palomar's Comparator to verify that the two
statements agree and permits only `propext`, `Classical.choice`, and `Quot.sound`.

The repository is a substantive proof development, not a thin wrapper. Its Palomar
metadata is in [`formalization.yaml`](formalization.yaml), and the root
[`LICENSE`](LICENSE) is Apache-2.0. To submit a public commit, use its full
40-character SHA at [the Palomar submission form](https://submit.palomar-registry.org/).

## Scope of the main theorem

The main theorem assumes:

- a concave, strictly increasing expansion profile with the stated reversal and gain
  properties;
- uniform intra-layer depth robustness;
- inter-layer expansion for the predecessor map;
- a global black-pebble budget and a per-layer red-pebble budget;
- a sufficiently large red-free challenge set; and
- the scalar entry conditions collected in `GeneralRegime`.

It concludes with a genuine directed path whose nodes carry neither black nor red
pebbles. The path length is explicit and grows with the number of layers through
`zMin`.

The proved model is a static pebbling snapshot. The theorem does not itself formalize
a time-indexed cryptographic game or the final reduction from path length to sequential
running time. Expansion and depth robustness are theorem hypotheses rather than
universal construction results.

## File map

The substantive dependency chain is:

- `Chung.lean` and `Expansion.lean`: expansion profiles, concavity, gain, and the
  reversal identity used by the tracking argument.
- `Footprint.lean`: normalized black-pebble budgets, footprint recurrences, accumulated
  bounds, and infertile-level capacity.
- `Tracking.lean`, `Search.lean`, and `Continuation.lean`: the tracking floor and the
  fertile/expandable search.
- `Growth.lean`: growth windows and the optimized two-piece growth potential.
- `Potential.lean`: an experimental reference-trajectory potential; proved, but not
  consumed by the main ledger.
- `Chain.lean` and `Ledger.lean`: chain links, break accounting, restart searches, and
  the global link-count lower bound.
- `Concrete.lean`: finite layered graphs, red/black pebbling snapshots, footprints,
  directed paths, and path splicing.
- `Latency.lean`: the public general latency theorem and its explicit constants.
- `ChungCurve.lean`, `ChungNumerics.lean`, and `ChungFilecoin.lean`: the degree-eight
  Chung-profile specialization and certified numerical bounds.
- `Constructions.lean`: bounded-indegree construction interfaces and precise statements
  of the graph certificates still required by the concrete specialization.
- `Witness.lean`: an unconditional Möbius-profile model showing consistency of the scalar
  hypothesis stack; it is not claimed as a deployed graph profile.

`ProofOfSpace.lean` imports the complete public development.

## Indexing convention

Following Reyzin, the published layered construction labels the challenge layer
`V_ℓ` and the top layer `V₁`. Lean instead counts forward from the challenge:
`layer 0` corresponds to `V_ℓ`, `layer (ℓ - 1)` corresponds to `V₁`, and edges from
`layer (d + 1)` to `layer d` move toward the challenge. This avoids repeated truncated
natural-number subtraction in inductions.

## Concrete specialization and open assumptions

`chung8_latency_21` is conditional on three groups of input:

1. `LayeredGraph.expands`: the sampled permutation interlayers realize the required
   degree-eight expansion profile.
2. `LayeredGraph.DepthRobust`: each intra-layer graph has the required deletion-set
   depth robustness. `Constructions.lean` records why the published DRSample
   certificate does not meet the deployed Filecoin-shaped target.
3. `Chung8AnalyticAssumptions`: concavity of `chungBeta8` and uniqueness of the
   unadjusted-gain maximizer. Mapping, strict expansion, monotonicity, reversal, and the
   adjusted-gain roots are proved for the defined curve.

These assumptions are exposed in theorem types and are not counted as axioms.

## Build and trust audit

With Lean 4 installed, run:

```bash
lake build
lake env lean scripts/AxiomAudit.lean
```

The first command builds the public dependency graph, Challenge, and Solution. The
second walks every declaration in the `ProofOfSpace` namespace and fails if any result
depends on an axiom other than `propext`, `Classical.choice`, or `Quot.sound`; this also
rejects `sorryAx`. Both checks run in
`.github/workflows/lean_action_ci.yml`.

## Published literature

- Leonid Reyzin. *Proofs of Space with Maximal Hardness*. 65th IEEE Symposium on
  Foundations of Computer Science, 2024, 1159–1177.
  [DBLP record](https://dblp.org/rec/conf/focs/Reyzin24).
- Ben Fisch. *Tight Proofs of Space and Replication*. Advances in Cryptology –
  EUROCRYPT 2019, Part II, LNCS 11477, 324–348.
  [DOI](https://doi.org/10.1007/978-3-030-17656-3_12).
