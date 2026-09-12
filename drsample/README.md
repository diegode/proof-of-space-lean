# Block depth robustness of DRSample

This project proves Conjecture 2 from Appendix F of Blocki, Harsha, Kang, Lee,
Xing, and Zhou (CRYPTO 2019), for the exact independent sampler in
[Challenge.lean](Challenge.lean). The single registered theorem is
`ProofOfSpaceStatement.drsample_conjecture2`. The Challenge imports only
Mathlib and contains no proof-development imports.

For every `n >= 2^128`, with all logarithms below in base two,

```text
e = floor(n log₂log₂ n / (20000 log₂ n))
d = 1.01 n log₂log₂ n / log₂ n
b = floor(3072 log₂ n / log₂log₂ n).
```

Except with probability at most

```text
exp(-(1/14060) n log₂log₂ n/log₂ n),
```

every union of at most `e` left intervals of width `b` can be deleted while
leaving a directed path on at least `d` vertices. The intervals end at their
chosen endpoints, may overlap, and are truncated at vertex zero. Their endpoints
may be chosen after sampling the entire graph. The failure bound tends to zero.

The constants are `c₀ = 1/14060`, `c₁ = 1/20000`, `c₂ = 1.01`, and `c₃ = 3072`.
The registered theorem `drsample_conjecture2` takes `n >= 2^128` directly.
The same cutoff applies to Conjecture 1 and to the ideal degree-six Filecoin
sampler through `drsample_conjecture1` and `filecoin_bucket6`.

## Sampling and statement fidelity

Vertices are numbered from zero. Include each predecessor edge. At a vertex
`v >= 2`, choose a bucket uniformly from `1, ..., ceil(log₂(v+1))`, cap its
upper endpoint at `v`, and choose a distance uniformly from
`max(2,ceil(upper/2)), ..., upper`. The random parent is `v-distance`. All these
choices are independent across vertices. The dummy parent at vertices zero and
one is zero and creates no extra forward edge. This ceiling convention removes
a repeated capped bucket when `v+1` is a power of two; the paper's harmonic
argument also covers the original floor-plus-one convention.

`drsampleProbability` is the finite sum of these product probabilities over
parent assignments. The proof library proves its normalization and identifies
it with the distribution used in the multiscale argument. In particular, the
Challenge does not assume an avoidance bound or depth robustness of an
unspecified sampler. Path length counts vertices, not edges.

## Proof and the stronger finite bound

The following bounds are proved in the supporting Lean modules.

1. A useful bucket for distance `r` has at most `r` choices, including capped
   buckets. Hence the harmonic parent coefficient is at least `1/(log₂ n+1)`.
2. At deletion-density threshold `4/5`, the one-sided covering inequality leaves
   at least `M-3|S|/2` good vertices: both exceptional sets contain every
   deleted vertex, and their overlap is subtracted. A surviving distance with a
   good endpoint shrinks by at most five under rank compression. The increasing-
   subsequence estimate and Jensen's inequality give depth `(M/2) exp(-20W/M)` when
   `|S| <= M/3`, where `W` is the forbidden harmonic mass.
3. Exposing actual depth labels gives an exponential moment at most `2^(M-|S|)`.
   Markov's inequality and the sum over all deleted sets give a single event
   `W <= 8M/(3λ)` for every `S`, with failure `exp(-(4/3-ln 3)M)`.
4. Group vertices into blocks of size `m`. First-third destination ports and
   last-third source ports give
   `λ = floor(m/3)²/[m(log₂ n+1)]`. A metagraph path lifts through intact blocks,
   contributing at least `m/3` vertices per visited block. A left interval of
   width at most `m` touches at most two blocks.
5. With `m = ceil(3072 log₂ n/log₂log₂ n)`, the verified rounding estimates
   give the displayed constants and failure coefficient for every `n >= 2^128`.
   The proof certifies depth at least `1.01 n log₂log₂ n/log₂ n`, including all
   floors and ceilings. A quadratic Taylor sum with a bounded cubic remainder
   gives `exp(441/400) <= 3013/1000` for the numerical base case. The bound on
   `ln 3` certifies `(4/3-ln 3)/3300 >= 1/14060`.

The finite result, for `12 <= m <= n`, is

```text
e = floor(floor(n/m)/6)
d = (m floor(n/m)/6) exp(-160 m (log₂ n+1)/(3 floor(m/3)²))
b = m,
```

with failure at most `exp(-(4/3-ln 3)floor(n/m))`. This retains the stronger
depth whose asymptotic expression at the selected block width is
`(n/6)(log₂ n)^(-5/(32 ln 2))`, with exponent approximately `0.225421`.
The public conjecture parameters give depth `1.01 n log₂log₂ n/log₂ n`.
The library also retains the older finite tradeoffs, Conjecture 1, and the
indegree-six Filecoin BucketSample/MetaBucket corollary. Filecoin's five
independent draws and downward rounding are modeled explicitly; a fixed
pseudorandom seed or machine-word sampling is not certified.

The good-vertex estimate is published as Claim 2 in
[Alwen–Blocki–Harsha](https://eprint.iacr.org/2017/443.pdf), attributed there
to Erdős–Graham–Szemerédi. That paper also supplies the sampler and restricted
metagraph construction. The treap ancestor probability is classical;
[Seidel–Aragon](https://doi.org/10.1007/BF01940876) is a reference. The additional
increasing-subsequence, depth-label, and probability arguments are proved here.
The target conjecture is in the
[CRYPTO 2019 full version](https://eprint.iacr.org/2018/944).

## Verification and layout

```sh
lake build
../scripts/verify-comparator.sh drsample
```

- `Challenge.lean`: self-contained definitions and the single advertised theorem.
- `Solution.lean`: its proof from `ProofOfSpace.DRSample.ExplicitParameters`.
- `ProofOfSpace/DRSample/Statement.lean`: the same public definitions for use by proofs.
- `ProofOfSpace/DRSample/Registry.lean`, `DistributionMap.lean`: the sampling bridge.
- `ProofOfSpace/DRSample/OptimizedRobustness.lean`: the overlap improvement and
  stronger finite graph theorem.
- `ProofOfSpace/DRSample/ExplicitParameters.lean`: the verified numerical cutoff,
  rounded parameters, exact DRSample theorem, and Filecoin specialization.
- `ProofOfSpace/DRSample/`: the complete multiscale and Filecoin development.
- `comparator.json`: compares only `drsample_conjecture2`, with NanoDa enabled.
- `formalization.yaml`: result, provenance, scope, and automation metadata.

Only the intentional Challenge placeholder omits a proof. The proof modules
use no custom axioms; Comparator permits `propext`, `Classical.choice`, and
`Quot.sound`. The license is the repository-root Apache-2.0 license.
