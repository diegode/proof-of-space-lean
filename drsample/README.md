# Robustness results from the current paper

This project is being aligned with `paper/finalnew/sections/robustness.tex`
and `robustnessproof.tex`. **The requested full-paper formalization is not yet
complete.** Five of the eleven labeled results have complete Lean proofs and
matching statements in [Challenge.lean](Challenge.lean). [Solution.lean](Solution.lean)
proves the sampler theorems and imports the other three proofs. No unproved
results are assumed by these proofs.

For `L(n) = log₂ n / log₂log₂ n`, the sampler statements now assert that positive
constants `c,C` exist such that, for every fixed `0 < ε < 1` and all sufficiently
large `n`, there are natural parameters `e,b` with

```text
c ε n/L(n) ≤ e ≤ C ε n/L(n)
c L(n)/ε ≤ b ≤ C L(n)/ε
d = c n/(log₂ n)^ε
failure probability ≤ exp(-c ε n/L(n)).
```

The constants are independent of `ε`; the size threshold can depend on it.
BucketSample covers every integer number of draws `r ≥ 1`. The sampler-avoidance
lemma also allows any fixed `0 < β < 1` and guarantees `eb ≥ βn`, with constants
depending only on `β`.

These replace the former public `n ≥ 2^120`, depth `1.48 n/L(n)`, and fixed
numerical parameter statements. A large-size cutoff and numerical constants
remain internal proof tools, not the public statements.

## Complete paper inventory

| Paper label | Lean declaration or status |
| --- | --- |
| `thm:dr-conjecture2` | Proved: `drsample_conjecture2` |
| `lem:sampler-avoidance` | Proved: `sampler_avoidance` |
| `cor:drsample-brg-optimal` | Not yet proved |
| `cor:bucket-optimal` | Proved: `bucketSample_block_robustness` |
| `def:fractional-dr` | Defined: `FractionalDepthRobust` |
| `thm:block-to-fractional` | Not yet proved |
| `cor:bucket-fractional` | Not yet proved (both samplers) |
| `thm:valiant-depth-reduction` | Not yet proved |
| `cor:balanced-robustness-optimality` | Width obstruction proved in `PaperWidth`; balanced bound not yet proved |
| `lem:dr-subsequence` | Proved: `dr_subsequence` |
| `lem:dr-labels` | Proved: `dr_labels`, for every `0 < α < 1` |
| `thm:multiscale` | Independent-graph specialization proved for every `0 < α < 1`; general conditional-label statement not yet proved |

The two algorithms are defined by the exact finite distributions below.
Section and equation labels are represented by the surrounding definitions and
theorems rather than separate theorem declarations. The six remaining labeled
results have not been inserted as unproved Solution declarations.

## Distributions and events

All graphs include predecessor edges. DRSample independently chooses one
bucket in `1,…,ceil(log₂(v+1))`, caps its upper endpoint at `v`, and uniformly
draws a length from `max(2,ceil(upper/2)),…,upper`.

BucketSample uses the same fine position `rv` for all `r` independent draws
at vertex `v`. Each draw chooses one of `ceil(log₂(rv))` buckets uniformly,
uses lower endpoint `max(2,floor(upper/2))`, and divides the fine parent
position by `r`, rounding downward.

The finite-sum probabilities agree with normalized independent product laws.
Vertices zero and one use a dummy parent zero. Ordered edges prevent this from
adding a spurious edge. Path lengths count vertices. Endpoint sets are quantified
after sampling the graph, and backward deletion blocks may overlap or be truncated
at zero.

`sampler_avoidance` uses normalized distributions of whole incoming-edge sets.
`SupportedIncomingEdges` specifies the topological order and line edges;
`HarmonicAvoidance` states the paper's reciprocal-distance bound.

## Proof organization

- `Statement.lean`: exact DRSample and BucketSample definitions.
- `PaperDefinitions.lean`: general graph, finite probability, fractional
  robustness, BRG, pebbling, and conditional-label definitions.
- `PaperSubsequence.lean`: the paper's increasing-subsequence lemma, using
  the existing finite pivot proof.
- `GeneralLabels.lean`: arbitrary deletion fractions, accounting for the
  overlap of the two exceptional sets; the density threshold is `(q-1)/q`.
- `GeneralMultiscale.lean`: the independent-graph multiscale bound for any
  fixed deletion fraction, with failure `exp(-(2-ln 3)n)`.
- `GeneralBlocks.lean`: shift averaging and path lifting at that fraction.
- `GeneralParameters.lean`, `PaperAvoidance.lean`: asymptotic parameters with
  `eb ≥ βn` and the public sampler-avoidance statement.
- `AsymptoticRobustness.lean`: a fixed-fraction parameter choice sufficient
  for the DRSample and BucketSample statements.
- `PaperWidth.lean`: the width obstruction `b < n/e`.

The proof retains the existing integer block geometry (`20a` vertices per full
block) and chooses `a` proportional to `L(n)/ε`. Its internal constants differ
from the appendix's choices; the stated asymptotic orders and dependencies agree.
The imported sampler proofs no longer use the former concrete avoidance lemma.
Historical finite estimates remain available in supporting files.

The BRG definition follows [BHKLXZ19, Definition 4](https://eprint.iacr.org/2018/944.pdf):
it retains the first-layer graph, adds the line on both layers, and joins the
layers by bit reversal. Its pebbling bound remains a proof target.

## Verification

```sh
lake build
python3 ../scripts/check-statement-surface.py drsample
../scripts/verify-comparator.sh drsample
```

The full Lake build, statement-surface check, and Comparator run passed for all
five completed results. Both NanoDa and the Lean default kernel accepted the
exported proofs; the axiom audit reports only the three permitted axioms. Each has
one intentional statement placeholder in Challenge. Solution and its supporting
proofs contain no placeholders or custom axioms. Permitted proof axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.
