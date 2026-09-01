# Formalized Latency Bounds for Stacked Proofs of Space

This repository formalizes a static latency lower bound for a 15-layer stacked
proof-of-space graph in Lean 4. The vertical wiring follows the Chung model used by
Reyzin: sample one uniform permutation of the `8n` ports `Fin 8 × Fin n`, then reuse
that interlayer across the 14 gaps of the stack.

Under explicit within-layer depth-robustness and pebbling-budget hypotheses, the
Filecoin specialization produces an unpebbled directed path containing at least

```text
(1/5)n + (1/5 - 74/625)n = (176/625)n = 0.2816n
```

vertices. This is a statement about a static black/red pebbling snapshot; it does not
formalize a time-indexed cryptographic game or a reduction from path length to running
time.

## The two theorem statements

[`Challenge.lean`](Challenge.lean) has exactly two theorem declarations. The other
content consists only of definitions and explicit hypotheses needed by their types.

### `chung8_pebbling_latency_whp`

`ProofOfSpaceStatement.chung8_pebbling_latency_whp` is the generic probabilistic lifting step.
If every sampled interlayer satisfying the certified integer expansion event has some
deterministic latency consequence, then the same consequence holds under the uniform
law with failure at most `chung8FailureBound n`.

The required `ChungExpansionConditions n` make the finite-size and integer-rounding
conditions explicit:

```text
n > 0,
δₙ = 189/10000 - 1/n > 0,
1/n ≤ αₘₐₓ(probabilistic expansion interval) - αₘₐₓ(pebbling interval).
```

The proof does not assume that a random interlayer expands. It derives the probability
of that event from the fixed-pair count and union bound, then lifts the caller's
deterministic implication.

### `chung8_pebbling_latency_15`

`ProofOfSpaceStatement.chung8_pebbling_latency_15` specializes the generic theorem to the
15-layer Filecoin parameters:

- within-layer path fraction `απ = 1/5`;
- per-layer red budget `δ = 189/5000`;
- depth-robustness threshold `π = 4/5`;
- total black budget `ρ = 4/5`; and
- a red-free challenge set of density at least `4311/5000`.

For a requested real security parameter `lambda`, the theorem assumes
`ChungSecurityConditions n lambda` and concludes

```lean
HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
  (M.HasUnpebbledPathTo A
    ((1 : ℝ) / 5 * M.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * M.n))
  (ENNReal.ofReal (Real.exp (-lambda * Real.log 2)))
```

Thus, in ordinary notation,

```text
Pr[M.HasUnpebbledPathTo A (176n/625)] ≥ 1 - 2^(-lambda).
```

`M.HasUnpebbledPathTo A L P` says that the pebbling game has a nonempty directed path
ending at a vertex of `A`, with no vertex black- or red-pebbled at its layer, and with
real-valued lower bound `Q.length ≥ L`. Since the length is a natural number, this is
equivalent to `Q.length ≥ ⌈L⌉`.

## The simplified expansion-failure bound

Set

```text
α = chung8AlphaMin
  = (961821/74555000)/2,
δₙ = 189/10000 - 1/n,
ε_chung = 2^(-22).
```

The formal definition is

```text
chung8FailureBound(n)
  = exp(1/8) / (2π α sqrt(δₙ))
      · exp(-n ε_chung log 2)
  = exp(1/8) / (2π α sqrt(δₙ))
      · 2^(-n ε_chung).
```

Lean stores this nonnegative real as `ENNReal.ofReal (...)`. In the simplified union
bound, the `1/n` in each fixed-size estimate cancels against at most `n` possible
source-set sizes. This replaces the former exact sum over all sizes and candidate
neighbourhoods.

The paper contains a small internal discrepancy: Appendix A's preview says `2⁻²³`,
whereas the concrete Appendix C calculation says `2⁻²²`. The formalization follows
Appendix C and independently certifies the stronger required exponent inequality at
`ε_chung = 2⁻²²`.

The public expansion profile is defined without the rational polygon. For source size
`k`, let `S(n,k)` contain precisely the integers `m < n` satisfying

```text
k < m,
α ≤ 1 - m/n,
δₙ ≤ m/n - k/n,
E₈(k/n,m/n) ≤ -ε_chung log 2.
```

Then `chung8FailureProfile n k` is the largest member of `S(n,k)`, defaulting to zero
if it is empty. Thus the statement mentions only Reyzin's exponent and the finite-grid
margin conditions. The event `P.Expands` says that every source set in the active
interval has more than this certified number of distinct predecessor vertices.

The rational polygon is proof-only: `Solution.lean` uses it to exhibit a member of
`S(n,k)` at every active source size and to show that the exponent-defined public profile
is strong enough for the deterministic latency argument.

### Bounds on `epsilonChung` and `n`

For the simplified bound, the exponent level must be admissible at every active source
density. In the paper's bit convention this is

```text
0 < ε_chung < 6 H₂(x).
```

The Lean proof establishes the corresponding natural-log inequality
`ε_chung log 2 < 6 H(x)` from the certified strict negativity of the polygon; it is
not left as an assumption.

For `lambda` bits of failure security, the paper's sufficient width condition is

```text
n > (λ - 2.4 - log₂(α) - ½ log₂(δₙ)) / ε_chung.
```

This inequality is the `security` field of `ChungSecurityConditions n lambda`.
The formalization also proves the numerical prefactor estimate behind `2.4` and derives
`chung8FailureBound n ≤ 2^(-lambda)`.

## What the displayed probability statement means

For

```lean
HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
  (M.HasUnpebbledPathTo A L)
  (chung8FailureBound M.n)
```

the meanings are:

- `P` is one uniformly random permutation of all `8n` ports, not eight independent
  permutations of the `n` vertices;
- the same `P` is used between every pair of consecutive layers;
- each child vertex owns eight ports, and its predecessor neighbourhood consists of
  the vertex components reached by permuting those ports;
- the probability of the latency event is at least
  `1 - chung8FailureBound M.n`.

`HoldsWithFailureAtMost` uses extended nonnegative reals and is defined as
`1 - failure ≤ successProbability`. As with any untruncated union bound, a failure
expression at least one is valid but uninformative; the size and security conditions
ensure the intended finite-size regime.

## Proof architecture

- `Chung.lean`, `ChungCurve.lean`, and `ChungShifted.lean` develop the exponent and its
  finite-size shifted section.
- `ChungFilecoinCurve.lean`, `ChungChord.lean`, `ChungNumerics.lean`, and
  `ChungRegion.lean` define and certify the rational degree-eight polygon.
- `PortExpansionProbability.lean` proves the sharp Stirling estimate, the fixed-pair
  port-permutation count, and the abstract exponential union bound.
- `ChungFilecoinExpansion.lean` proves all polygon, rounding, `ε_chung`, width, and
  security side conditions needed for the Filecoin expansion instantiation.
- `Footprint.lean`, `Tracking.lean`, `Continuation.lean`, `Potential.lean`, and related
  files develop the deterministic accounting argument.
- `Concrete.lean`, `Latency.lean`, and `Constructions.lean` realize the argument on
  finite layered graphs and build the one-permutation port stack.
- [`Solution.lean`](Solution.lean) connects the probabilistic expansion theorem to the
  deterministic 15-layer latency result.

[`ProofOfSpace.lean`](ProofOfSpace.lean) imports the complete library development.

## Challenge and verification

`Challenge.lean` imports only Mathlib and leaves its two theorem bodies as `sorry`.
`Solution.lean` repeats the same public declarations and proves them. The comparator
registers `ProofOfSpaceStatement.chung8_pebbling_latency_15` and permits only `propext`,
`Classical.choice`, and `Quot.sound`.

Run:

```bash
lake build
./scripts/verify-comparator.sh
```

The first command builds the library, challenge, and solution. The second checks the
registered Challenge/Solution statement, permitted axioms, and NanoDa replay using the
pinned Palomar toolchain.

## Scope and literature

Lean numbers layers forward from the challenge: layer `0` is the challenge layer and
layer `14` is the top layer. Vertical edges point from layer `d + 1` to layer `d`.

The sampling theorem concerns an ideal uniform Chung port permutation. It does not
identify Filecoin's deployed Feistel wiring with that distribution.

- Leonid Reyzin. *Proofs of Space with Maximal Hardness*. FOCS 2024, 1159–1177.
  [ePrint](https://eprint.iacr.org/2023/1530).
- Ben Fisch. *Tight Proofs of Space and Replication*. EUROCRYPT 2019, Part II,
  324–348. [ePrint](https://eprint.iacr.org/2018/702).

The project is licensed under Apache-2.0.
