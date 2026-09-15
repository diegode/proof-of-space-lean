# Block depth robustness of DRSample and BucketSample

This project formalizes the DRSample theorem and BucketSample corollary in the
current paper's `robustness.tex`, using the estimates in `robustnessproof.tex`.
[Challenge.lean](Challenge.lean) contains only the DRSample definitions and
`drsample_conjecture2`, using Mathlib alone. [Solution.lean](Solution.lean)
proves that theorem and the BucketSample corollary. HarmonicSample is outside
the current paper and is not imported by the solution.

For every `n ≥ 2^120`, put `L(n) = log₂ n / log₂log₂ n`. Both results use

```text
e = floor(n / (18000 L(n)))
b = floor(3600 L(n))
failure probability ≤ exp(-n / (11000 L(n))).
```

| Distribution | Depth in vertices | Theorem in `ProofOfSpaceStatement` |
| --- | --- | --- |
| DRSample(n) | `1.48 n / L(n)` | `drsample_conjecture2` |
| BucketSample(n,r), every integer r ≥ 1 | `1.48 n / L(n)` | `bucketSample_block_robustness` |

Each event holds simultaneously for every set of at most `e` endpoints,
including endpoints chosen after sampling the graph. Deleting their left
intervals of width `b` leaves a path of the stated depth. Intervals may overlap
and are truncated at vertex zero.

## Exact distributions

All graphs include predecessor edges. DRSample independently chooses one
bucket in `1,…,ceil(log₂(v+1))`, caps its upper endpoint at `v`, and uniformly
draws a length from `max(2,ceil(upper/2)),…,upper`.

BucketSample uses the same fine position `r v` for all `r` independent draws
at vertex `v`. Each draw uniformly chooses one of `ceil(log₂(r v))` buckets,
uses the lower endpoint `max(2,floor(upper/2))`, and rounds the fine parent
position downward by division by `r`.

The public finite-sum probabilities are identified with normalized product
laws. Vertices zero and one use a dummy parent zero; the ordered edge relation
prevents this from adding a spurious edge.

The reciprocal-distance avoidance coefficients are `1/(log₂ n+1)` and
`r/(log₂(r n)+1)`, respectively. The proof covers every positive integer `r`.
Maximum indegree is two for DRSample and at most `r+1` for BucketSample.

## Proof and paper alignment

Both sampler proofs apply `concrete_avoidance_criterion`, corresponding to
Lemma `lem:concrete-avoidance`. The concrete parameters prove the common depth
`1.48 n/L(n)` used by both results.

The overlap of the two exceptional vertex sets gives at least `M-3|S|/2`
good vertices. The deterministic shallow-label estimate is
`(M/2) exp(-20W/M)` when `|S| ≤ M/3`.

The two-thirds exponential moment is at most `3^(M-|S|)`. Summing over all
deleted sets gives `W ≤ 12M/(5λ)` on a single event, with failure
`exp(-(8/5-ln 4)M)`. Thus the multiscale depth is `(M/2) exp(-48/λ)`.

The paper uses blocks of size `2s`, with `s` any positive integer. Triangular
source/destination ports supply at least `119 s²/200` eligible pairs, and
averaging over all `2s` shifts bounds the number of blocks touched by the
endpoint intervals. The finite bound applies simultaneously to all positive
widths and endpoint budgets satisfying `e(b+2s) ≤ (n-4s)/3`, with failure
`2s exp(-(8/5-ln 4)(n/(2s)-2))`.

Both proofs lift paths through block centers directly, yielding depth
`(9/40)(n-4s) exp(-323/(2ηs))` without an additive rounding loss. The paper
requires each crossing to gain at least `9s/10` vertices. Lean retains the
integer scale `s = 10a` (full block size `20a`) and its slightly stricter
port condition, with integral gain `9a`.

The paper chooses `s = ceil(1160 L(n))`; Lean chooses
`s = 10 ceil(116 L(n))`. Both satisfy `1160 L(n) ≤ s ≤ 1161 L(n)` and give
the same displayed sampler parameters. The rounding and numerical
inequalities at `2^120` for Lean's choice are checked by Lean.

## Verification and layout

```sh
lake build
python3 ../scripts/check-statement-surface.py drsample
../scripts/verify-comparator.sh drsample
```

- `Challenge.lean`: the sole submission statement, `drsample_conjecture2`.
- `Solution.lean`: proofs of DRSample and BucketSample
  (`thm:dr-conjecture2` and `cor:bucket-optimal`).
- `Statement.lean`, `Registry.lean`, `MultiSamplerRegistry.lean`: public
  definitions and distribution bridges.
- `Samplers.lean`, `BucketSample.lean`: sampler laws and avoidance bounds.
- `MomentSharp.lean`, `MultiscaleSharp.lean`: revised moment and depth estimates.
- `Triangular*.lean`, `ShiftedBlocks.lean`, `ShiftedRobustness.lean`: port
  counting, path lifting, common sampling events, and shift averaging.
- `LogEstimates.lean`, `PaperParameters.lean`, `PaperRobustness.lean`:
  verified numerical cutoff and the common concrete avoidance lemma.
- `ExplicitParameters.lean`: entry point for the concrete avoidance lemma.
- `comparator.json`: selects only `drsample_conjecture2`, with NanoDa enabled.

Only the single intentional Challenge placeholder uses `sorry`. The solution
and supporting proofs use no custom axioms; Comparator permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The cited pebbling optimality and fractional robustness reductions, and the
fully general conditional-label version of the multiscale theorem, are outside
this project's public theorem scope. The multiscale graph specialization used
by both sampler proofs is proved in `MultiscaleSharp.lean`.
