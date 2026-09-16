# Robustness results from the current paper

This project is being aligned with `paper/finalnew/sections/robustness.tex`
and `robustnessproof.tex`. **All ten required labeled results now have complete Lean proofs** and
matching statements in [Challenge.lean](Challenge.lean). [Solution.lean](Solution.lean)
proves the block sampler theorems and imports the other proofs. No unproved
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

For every fixed `0 < f < 1/2`, both samplers also have two-sided fractional
parameters `(e,d,f,f)` with the same orders for `e,d` and failure probability.
The constants depend only on `f`; the threshold may also depend on `ε`.
Both directions hold on the same block-robustness event.

These replace the former public `n ≥ 2^120`, depth `1.48 n/L(n)`, and fixed
numerical parameter statements. A large-size cutoff and numerical constants
remain internal proof tools, not the public statements.

## Complete paper inventory

| Paper label | Lean declaration or status |
| --- | --- |
| `thm:dr-conjecture2` | Proved: `drsample_conjecture2` |
| `lem:sampler-avoidance` | Proved: `sampler_avoidance` |
| `cor:drsample-brg-optimal` | Out of scope: cited existing result; not needed by these proofs |
| `cor:bucket-optimal` | Proved: `bucketSample_block_robustness` |
| `def:fractional-dr` | Defined: `FractionalDepthRobust` |
| `thm:block-to-fractional` | Proved: `block_to_fractional` |
| `cor:bucket-fractional` | Proved: `drsample_fractional_robustness`, `bucketSample_fractional_robustness` |
| `thm:valiant-depth-reduction` | Proved: `valiant_depth_reduction` |
| `cor:balanced-robustness-optimality` | Proved: `balanced_robustness_optimality` |
| `lem:dr-subsequence` | Proved: `dr_subsequence` |
| `lem:dr-labels` | Proved: `dr_labels`, for every `0 < α < 1` |
| `thm:multiscale` | Proved: `conditional_multiscale`, for arbitrary joint positive integer labels and every `0 < α < 1` |

The two algorithms are defined by the exact finite distributions below.
Section and equation labels are represented by the surrounding definitions and
theorems rather than separate theorem declarations. The ten required results
are represented by eleven registered declarations; the fractional corollary
has separate DRSample and BucketSample statements.

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
- `Valiant.lean`: the exact finite depth-reduction theorem, selecting the
  cheapest binary edge classes and counting the remaining bit patterns.
- `PaperOptimality.lean`: the balanced bound `min(e,d) = O(n/L(n))` and
  the estimate that each sampler's certified depth eventually exceeds its
  deletion budget; `PaperWidth.lean` supplies `b < n/e`.
- `DiscreteLaw.lean`: conditional moments and the weighted union bound for
  discrete laws with potentially infinite support.
- `ConditionalLabels.lean`: the general conditional-label multiscale theorem,
  with positive labels on the law's support and failure `exp(-(2-ln 3)n)`.
- `Fractional.lean`: block-to-fractional conversion with deletion budget
  `⌊e/2⌋`, including truncated boundary blocks, and reversal of graphs and paths.
- `PaperFractional.lean`: two-sided fractional robustness for both samplers,
  with constants uniform in the exponent and number of bucket draws.

The proof retains the existing integer block geometry (`20a` vertices per full
block) and chooses `a` proportional to `L(n)/ε`. Its internal constants differ
from the appendix's choices; the stated asymptotic orders and dependencies agree.
The imported sampler proofs no longer use the former concrete avoidance lemma.
Historical finite estimates remain available in supporting files.

The fractional conversion follows the statement of
[Blocki--Zhou, Theorem 4](https://doi.org/10.1007/978-3-319-70500-2_15),
checked against the local Zotero item `JLUWR5RH` (attachment `PMHMDREK`).
Its Lean proof uses a residue-class cover of vertices ending long paths,
plus deleted vertices and the final partial block, in place of the paper's
greedy interval procedure. The reverse graph preserves block robustness;
applying the conversion in both orders proves the two-sided claim.

Valiant's bound was checked against Lemma 2.2 of
[Alwen--Blocki--Harsha](https://doi.org/10.1145/3133956.3134031), local Zotero
item `A3LAU3M7` (attachment `2M8AVSYF`). The Lean proof deletes destinations
of edges in the selected classes and bounds path length by distinct surviving
bit patterns. Balanced reduction uses `k = ceil(log₂ ceil(log₂ n))`, which gives
the same asymptotic bound as the paper's choice.

The conditional-label theorem uses a PMF on the joint array of labels for all
deletion sets. It assumes the paper's inequality only on histories of positive
probability. Labels may be unbounded and dependent. Conditioning, summing over
histories, and the `3^n` union bound are proved without added axioms.

The BRG definition follows [BHKLXZ19, Definition 4](https://eprint.iacr.org/2018/944.pdf):
it retains the first-layer graph, adds the line on both layers, and joins the
layers by bit reversal. The cited pebbling bound is outside the formalization
scope and is not used by the proofs.

## Verification

```sh
lake build
python3 ../scripts/check-statement-surface.py drsample
../scripts/verify-comparator.sh drsample
```

The full Lake build, statement-surface check, and Comparator run passed for all
eleven declarations representing all ten required results. Both NanoDa and the
Lean default kernel accepted the exported proofs; the axiom audit reports only
the three permitted axioms. Each declaration has
one intentional statement placeholder in Challenge. Solution and its supporting
proofs contain no placeholders or custom axioms. Permitted proof axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.
