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
`z` and the layer count `ℓ` are symbolic, constrained by the intervals the
Chung-8 profile is certified on and by the ledger's level condition

```text
0.6 + (z - 1)·3.822 + 11.87·ρ < ℓ
```

Its three terms are the search head, the price of one further chain link, and
the charge the black budget pays; the whole latency argument — the union bound,
the transfer of the public profile to the deterministic setting, the layered
graph, the red-pebble removal from the challenge set and the potential ledger —
is in its proof. The level condition is what a change of parameters has to buy:
two links need `ℓ = 14` at `ρ = 4/5` (`13.918 < 14`), `ℓ = 13` at `ρ = 7/10`, and
a third link at the Filecoin budget needs `ℓ = 18`. Worked points are checked in
[`ChungFilecoinGeneral.lean`](ProofOfSpace/ChungFilecoinGeneral.lean).

The red-pebble fraction `δ` and the depth-robustness threshold `π` enter the
window one-sidedly (`δ ≤ 0.0378`, `π ≤ 4/5`): a game with fewer red pebbles, or
a weaker robustness threshold, satisfies the certified one. Moving them upwards
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

Both public theorems use a range containing `[1/100, 24/25]`, which brackets the
Filecoin `[αmin, αmax] = [0.0129…, 0.9493…]`, and assumes `1000 ≤ n` so that the
rounding of a subset back into the range fits. `ChungSecurityConditions n lambda
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
