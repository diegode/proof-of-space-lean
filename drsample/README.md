# Block depth robustness of DRSample, BucketSample, and HarmonicSample

This project formalizes the three sampler theorems in the current paper's
`robustness.tex`, using the multiscale estimates in `robustnessproof.tex`.
[Challenge.lean](Challenge.lean) specifies the exact finite distributions and
statements using Mathlib alone; [Solution.lean](Solution.lean) proves all three.

For every `n ≥ 2^120`, put `L(n) = log₂ n / log₂log₂ n`. All three results use

```text
e = floor(n / (18000 L(n)))
b = floor(3600 L(n))
failure probability ≤ exp(-n / (11000 L(n))).
```

| Distribution | Depth in vertices | Registered theorem in `ProofOfSpaceStatement` |
| --- | --- | --- |
| DRSample(n) | `1.48 n / L(n)` | `drsample_conjecture2` |
| BucketSample(n,r), every integer r ≥ 1 | `1.48 n / L(n)` | `bucketSample_block_robustness` |
| HarmonicSample(n,r), every integer r ≥ 1 | `2 n / L(n)` | `harmonicSample_block_robustness` |

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

HarmonicSample independently draws `r` lengths from `2,…,v`, with probability
`1/(s(H_v-1))` for length `s`. The normalization and the inequality
`H_v-1 ≤ ln n` are proved. The public finite-sum probabilities are identified
with normalized product laws. Vertices zero and one use a dummy parent zero;
the ordered edge relation prevents this from adding a spurious edge.

The harmonic avoidance coefficients are `1/(log₂ n+1)`,
`r/(log₂(r n)+1)`, and `r/ln n`, respectively. The proof covers every positive
integer `r`; it does not specialize BucketSample to five draws. Maximum
indegree is two for DRSample and at most `r+1` for the other samplers.

## Proof and paper alignment

The overlap of the two exceptional vertex sets gives at least `M-3|S|/2`
good vertices. The deterministic shallow-label estimate is
`(M/2) exp(-20W/M)` when `|S| ≤ M/3`.

The two-thirds exponential moment is at most `3^(M-|S|)`. Summing over all
deleted sets gives `W ≤ 12M/(5λ)` on a single event, with failure
`exp(-(8/5-ln 4)M)`. Thus the multiscale depth is `(M/2) exp(-48/λ)`.

For block size `B = 20a`, triangular source/destination ports supply at least
`119 B²/800` eligible pairs. Averaging over all `B` shifts bounds the number
of blocks touched by the endpoint intervals. The finite theorem applies
simultaneously to all positive widths and endpoint budgets satisfying
`e(b+B) ≤ (n-2B)/3`, with failure `B exp(-(8/5-ln 4)(n/B-2))`.

Both proofs lift paths through block centers directly. The first intact
half-block already supplies `9a` vertices, yielding the finite depth
`(9/40)(n-2B) exp(-323/(ηB))` without an additive rounding loss.
The specialization `B = 20 ceil(116 L(n))`, including its rounding and all
numerical inequalities at `2^120`, is checked by Lean.

## Verification and layout

```sh
lake build
python3 ../scripts/check-statement-surface.py drsample
../scripts/verify-comparator.sh drsample
```

- `Challenge.lean`, `Solution.lean`: the three matching submission statements.
- `Statement.lean`, `Registry.lean`, `MultiSamplerRegistry.lean`: public
  definitions and distribution bridges.
- `HarmonicSample.lean`, `BucketSample.lean`: exact sampler laws and avoidance.
- `MomentSharp.lean`, `MultiscaleSharp.lean`: revised moment and depth estimates.
- `Triangular*.lean`, `ShiftedBlocks.lean`, `ShiftedRobustness.lean`: port
  counting, path lifting, common sampling events, and shift averaging.
- `LogEstimates.lean`, `PaperParameters.lean`, `PaperRobustness.lean`:
  verified numerical cutoff and the three concrete sampler results.
- `ExplicitParameters.lean`: entry point for the current concrete results.
- `comparator.json`: selects all three theorems, with NanoDa enabled.

Only the three intentional Challenge placeholders use `sorry`. The solution
and supporting proofs use no custom axioms; Comparator permits only
`propext`, `Classical.choice`, and `Quot.sound`.
