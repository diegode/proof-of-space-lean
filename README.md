# Formalized Latency Bounds for Stacked Proofs of Space

This repository contains a Lean 4 formalization of latency lower bounds for stacked
proof-of-space graphs. The construction stores data across `ℓ` layers of `n` nodes.
For a uniformly sampled degree-eight Chung interlayer, and under explicit
depth-robustness and pebbling-budget hypotheses, the Palomar theorem constructs with
quantified high probability an unpebbled directed path of length `Ω(ℓ n)` in every
sufficiently large red-free challenge footprint. This is the static combinatorial core
of the statement that a cheating prover must perform non-parallelizable work growing
linearly with the number of layers.

All constants are explicit. The quantitative objective is to make the leading constant
as tight as possible, not merely to prove that it is positive. For the unconditional
finite-size degree-eight Filecoin-shaped profile, the potential-ledger analysis proves
that the asymptotic coefficient lies strictly between `0.02135` and `0.02136`.

## The theorem and its scope

The reusable general theorem in `ProofOfSpace/Latency.lean` assumes:

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
reduction from path length to sequential running time.

The Palomar-facing theorem specializes the analytic data to the proved finite-size
Chung-8 profile and constructs the vertical graph from eight uniform permutations. Its
failure probability is the exact finite union bound `chung8FailureBound n`; only the
independent within-layer depth-robustness and pebbling conditions remain as hypotheses.

No expansion profile is posited. `Challenge.lean` writes out Reyzin's union-bound
exponent `E₈(x, y) = H(x) + H(y) + 8(y H(x/y) - H(x))` and defines the expansion the
theorem demands as the root of `E₈(x, ·) = -H(x)/2²³` — so what a sampled interlayer must
achieve is exactly what Chung's own union bound certifies. The level is *relative*, a
multiple of `H(x)` rather than a constant, and that is what keeps the statement uniform in
the layer width: since `E₈(x, x) = -6 H(x)`, a fixed level cuts out an empty region once
`H(x)` falls below it, and at Filecoin's `n ≈ 10⁹` even `k = 1` would land in that dead
zone.

The rational polygon lives entirely in the proof. `chung8_latency_15` needs the
deterministic latency argument's expansion hypothesis, and the polygon supplies it:
`ChungRelative.lean` proves the polygon lies strictly below that threshold on all of
`(0,1)`, so the profile the statement defines from the exponent alone already demands
everything the deterministic argument consumes.

## Palomar submission surface

The Palomar statement of record is
[`ProofOfSpaceStatement.latency_chung8_whp`](Challenge.lean). `Challenge.lean` imports
only allowlisted Mathlib modules and contains only the deliberate `sorry`s permitted in a
challenge statement. [`Solution.lean`](Solution.lean) proves that statement using
[`ProofOfSpace.latency_general`](ProofOfSpace/Latency.lean).
[`comparator.json`](comparator.json) checks that the statements agree and permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The statement separates its within-layer graph and pebbling data into `LatencyData` and
exposes every remaining conditional assumption through the explicit typeclass parameter
`[LiteratureHypotheses M]`; no hypothesis instance is declared globally. That class
carries no numerals: the parameters it quantifies over (`αpi`, `δ`, `pi`, `ρ`) are
`LatencyData` fields, and their Filecoin values are pinned by equation hypotheses in
`chung8_latency_15`. The Chung-8 profile, vertical permutation construction, and its
expansion probability are theorem data rather than fields of that class.

Submission metadata is in [`formalization.yaml`](formalization.yaml), and the project is
licensed under Apache-2.0. A public submission should use the full 40-character commit
SHA at the [Palomar submission form](https://submit.palomar-registry.org/).

## Proof architecture

- `Chung.lean`, `ChungCurve.lean`, `ChungShifted.lean`, and `Expansion.lean` define the
  expansion exponent, construct its zero-level and finite-size roots, and define the
  abstract expansion interface.
- `ChungFilecoinCurve.lean`, `ChungChord.lean`, and `ChungRegion.lean` define the
  rational degree-eight profile used by the Filecoin specialization, prove its shape
  laws, and certify it inside the Chung region at the fixed level `-2⁻²²`, on
  `[2⁻²⁵, 1 - 2⁻²³]`.
- `ChungRelative.lean` moves to a level proportional to `H(x)` and extends the
  certificate to all of `(0,1)`, covering the two corners the fixed level cannot reach
  with a ray estimate along the polygon's opening chord and its mirror. Its
  `filecoinBeta_lt_shiftedBeta_level` is the bridge `chung8_latency_15` consumes.
- `UnionBound.lean` proves, by the union bound, that a sampled tuple of permutations
  beats a given integer failure profile. It refers to no expansion function at all.
- `Footprint.lean` develops normalized pebble budgets and the footprint recurrence.
- `Tracking.lean`, `Search.lean`, and `Continuation.lean` construct fertile and
  expandable searches through the layers.
- `Growth.lean` bounds the cost of growth windows.
- `Potential.lean` defines a piecewise-linear potential along a certified reference
  trajectory.
- `PotentialLedger.lean` prices search steps with that potential and derives the global
  link count.
- `Chain.lean` organizes continuation links and global budget accounting.
- `Concrete.lean` instantiates the abstract analysis for finite layered graphs and
  splices the links into a directed path.
- `Latency.lean` states the public latency theorems.
- `ChungNumerics.lean` and `ChungFilecoin.lean` prove the degree-eight numerical
  certificates and the optimized asymptotic coefficient.
- `Constructions.lean` states the bounded-indegree graph certificates required by the
  concrete specialization.

`ProofOfSpace.lean` imports the complete public development.

## Indexing convention

The published layered construction labels the challenge layer `V_ℓ` and the top layer
`V₁`. Lean counts forward from the challenge: `layer 0` corresponds to `V_ℓ`,
`layer (ℓ - 1)` corresponds to `V₁`, and edges from `layer (d + 1)` to `layer d` move
toward the challenge.

## Filecoin construction and open graph hypotheses

The specialization uses the degree-eight profile at Reyzin's Appendix C exponent level
`ε_chung = 2⁻²²`. In the Palomar theorem the vertical graph is an eight-tuple of uniform
permutations, sampled once and reused between all consecutive layers. Consequently the
only remaining graph hypothesis is:

1. `LayeredGraph.DepthRobust`: each intra-layer graph has the required deletion-set
   depth robustness.

The expansion the statement demands is the Chung threshold itself, defined from the
exponent. The rational polygon appears only in the proof, where it discharges the
deterministic argument's hypothesis: it is a conservative under-approximation of that
threshold, certified over all of `(0,1)`, and it is used rather than the root because
concavity and a unique gain maximiser — both required of a `Setting.β` — are free for a
minimum of affine functions and unproved for the root.

`UnionBound.lean` proves the exact canonical failure bound uniformly in the layer width,
degree, and abstract expansion setting. `latency_chung8_whp` transports that result to
the explicit path event.

This sampling model does not identify Filecoin's deployed Feistel wiring with a uniform
tuple of permutations. Reyzin's concrete Appendix C estimate `1 - 2⁻²⁴⁹` is for the
deployed-scale Chung calculation; the formal theorem retains its exact combinatorial
union-bound expression instead of importing that numerical estimate as an assumption.

## Build and submission verification

With Lean 4 installed, run the project build. On Linux with Git, Go, Rust/Cargo, and
Python 3 available, also run the pinned Palomar verification toolchain:

```bash
lake build
./scripts/verify-comparator.sh
```

The first command builds the public dependency graph, Challenge, and Solution. The second
uses [`comparator.json`](comparator.json) to check that the proved Solution declaration
has the same name and type as the Challenge declaration, depends only on `propext`,
`Classical.choice`, and `Quot.sound`, and replays through the NanoDa kernel. Both checks
run in `.github/workflows/lean_action_ci.yml`.

## Published literature

- Leonid Reyzin. *Proofs of Space with Maximal Hardness*. 65th IEEE Symposium on
  Foundations of Computer Science, 2024, 1159–1177.
  [ePrint](https://eprint.iacr.org/2023/1530).
- Ben Fisch. *Tight Proofs of Space and Replication*. Advances in Cryptology –
  EUROCRYPT 2019, Part II, LNCS 11477, 324–348.
  [ePrint](https://eprint.iacr.org/2018/702).
- Filecoin, [SDR protocol specification](https://spec.filecoin.io/algorithms/sdr/) and
  [`rust-fil-proofs` stacked graph implementation](https://github.com/filecoin-project/rust-fil-proofs/blob/master/storage-proofs-porep/src/stacked/vanilla/graph.rs).
