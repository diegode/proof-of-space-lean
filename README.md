# Formalized Latency Bounds for Stacked Proofs of Space

This repository formalizes in Lean 4 a static latency lower bound for a
14-layer stacked proof-of-space graph. The vertical wiring is one uniformly
sampled permutation of the `8n` ports `Fin 8 × Fin n`, reused between all
consecutive layers.

## Main result

[`chung8_pebbling_latency_14`](Challenge.lean) proves that, except with
probability `2^(-lambda)` over the sampled wiring, **every** admissible
14-layer pebbling position at the Filecoin parameters and **every** challenge
set of weight `ζ = 9/10` in the final layer admit an unpebbled directed path,
ending in that challenge set, of length at least

```text
(176/625)n = 0.2816n
```

The statement is uniform in this sense on purpose: the pebble sets are chosen
with the wiring in hand, so the game may not be fixed before the sample. The
width `n` is a parameter of `PebblingGame`, not a field, which is what lets one
probability space `ChungInterlayer n` carry a quantifier over all games.

[`chung8_pebbling_latency_whp`](Challenge.lean) is the theorem that carries the
argument, and `chung8_pebbling_latency_14` is one point of it. Its six game
parameters, the source weight `σ`, the expansion range `[a, b]`, the link count
`z` and the layer count `ℓ` are symbolic. What ties them together is one
inequality in layers,

```text
chung8SearchCost (ζ - δ) + (z - 1)·chung8LinkCost + chung8ChargeRate·ρ < ℓ
```

the initial search, one further chain link (`3.822` layers), and the black weight
(`11.87` layers per unit), each priced in layers. The search price
`0.43 + 6.46·(0.89 - (ζ - δ))₊` is a function of the challenge weight rather than a
constant, so a thinner challenge set is paid for instead of being excluded. The whole
latency argument — the union bound, the transfer of the public profile to the
deterministic setting, the layered graph, the red-pebble removal from the challenge set
and the potential ledger — lives in this proof.

Reading the inequality as a budget for `ℓ` is what the theorem is for. Two links
need `ℓ = 14` at the Filecoin parameters (`13.928 < 14`), `ℓ = 13` at `ρ = 7/10`,
and `ℓ = 12` at challenge weight `0.75` against half the space; a third link at
the Filecoin budget needs `ℓ = 18`. Worked points are checked in
[`ChungFilecoinGeneral.lean`](ProofOfSpace/ChungFilecoinGeneral.lean).

The remaining hypotheses are the ranges the profile is certified on, named rather
than written as bare numerals: `δ ≤ chung8Delta`, `π ≤ chung8Pi`,
`ρ ≤ chung8Rho`, `chung8PiBar + ρ < ζ - δ ≤ chung8ActiveHi`, and
`chung8SourceLo ≤ σ ≤ chung8SourceHi` with `σ < απ`. Three of these ceilings are
genuinely tight rather than conservative: the blocked-range certificate is fitted
exactly to `ρ = 4/5`, `gain_δ(σ) = 2g_π` holds with equality at `chung8SourceLo`,
and `chung8ActiveHi` is where the adjusted gain vanishes. Raising `δ` or `π`
means re-certifying the curve constants `α_δ^min`, `α_δ^max`, `g_π` and `π̄`,
which are the polygon evaluations of `ChungFilecoin.lean`.

## Expansion is assumed only on a density range

`ChungInterlayer.ExpandsOn a b` demands the Chung-8 profile only of source sets
whose density lies in `[a, b]`, and `chung8FailureBound n a b` pays for exactly
that range. This matters: at density `1/n` a Chung profile is a birthday
collision, so a bound covering every nonempty set is `Θ(1/n)` however large `n`
is, and near density `1` the union bound is vacuous. The deterministic argument
only ever queries expansion at densities in `[αmin, αmax]`, and a set denser
than `b` is handled by expanding a subset of the queried density.

The window hypotheses are `a ≤ chung8ActiveLo` and `chung8ActiveHi + 1/n ≤ b`,
the active interval `[0.0129…, 0.9493…]` itself, so the range may be shrunk to
whatever the union bound is cheapest on; the 14-layer instance uses
`[1/100, 24/25]` with `1000 ≤ n`. `ChungSecurityConditions n lambda
a b` remains an assumption on the width, with `lambda` a number of bits and the
failure probability `2⁻ˡᵃᵐᵇᵈᵃ`: it is satisfiable at the deployed
`lambda = 128` only for `n` around `2^35`, because the public margin
`chung8Level` scales the entropy by `2^-23`. The library's polygon route
([`expansionFailureBound_le_security`](ProofOfSpace/ChungFilecoinExpansion.lean))
reaches the same security level at `n = 2^30` with a flat `2^-22` margin; the
two are not yet connected.

## Scope

The result concerns a static black/red pebbling snapshot. It does not formalize
a time-indexed cryptographic game, a reduction from path length to running time,
a bound on the catching probability from the challenge distribution, or an
equivalence between Filecoin's deployed Feistel wiring and the uniform
port-permutation model.

## Repository layout

- [`Challenge.lean`](Challenge.lean) contains the public definitions and the
  theorem statements, with proof bodies replaced by `sorry`.
- [`Solution.lean`](Solution.lean) proves those statements from the library.
- [`ProofOfSpace/`](ProofOfSpace/) contains the deterministic latency argument,
  the layer specializations, and the expansion probability bound.
- [`ProofOfSpace.lean`](ProofOfSpace.lean) imports the complete development.

## Verification

```bash
lake build
./scripts/verify-comparator.sh
```

The comparator checks the registered theorem
`ProofOfSpaceStatement.chung8_pebbling_latency_14`, its permitted axioms, and
NanoDa replay using the pinned toolchain.

The development builds on Leonid Reyzin's *Proofs of Space with Maximal
Hardness* (FOCS 2024) and Ben Fisch's *Tight Proofs of Space and Replication*
(EUROCRYPT 2019). Licensed under Apache-2.0.
