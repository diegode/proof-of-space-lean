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
argument, and it is generic: it holds for **any** expansion profile with a certified
level budget, and `chung8_pebbling_latency_14` is one instance of it. It is itself the
`j = 0` case of [`chung8_pebbling_latency_mixed`](Challenge.lean), described under
[one chain, one payoff parameter](#one-chain-one-payoff-parameter) below.

An `ExpansionProfile` is the expansion calculus of the analysis — a map of the unit
interval into itself fixing `0`, strictly increasing, concave, expanding, satisfying
Chung's reversal law, with a unique gain maximiser and the two zeros of the adjusted
gain. One field, `le_chung8`, ties it to the sampled wiring: the profile must lie under
the degree-eight Chung threshold, which is what the union bound pays for. A
`LevelBudget` is a reference trajectory for the profile together with the certificate
that prices one step of the search along it, and it yields the three prices the layer
count is spent on.

The parameters are then tied together only by relations among themselves:

```text
δ ≤ E.δ,  π ≤ E.π,  ρ ≤ L.ρmax,  E.piBar + ρ < ζ - δ ≤ E.αmax,  σ < απ,
a ≤ E.αmin,  E.αmax + 1/n ≤ b,
L.searchCost (ζ - δ) + (z - 1)·L.linkCost + L.chargeRate·ρ < ℓ
```

The last line is what a change of parameters has to buy. At the Chung-8 budget the three
prices are `0.5982`, `3.8212` and `11.8588` per unit of black weight, so two links need
`ℓ = 14` at `ρ = 4/5` (`13.907 < 14`), `ℓ = 13` at `ρ = 7/10`, and a third link needs
`ℓ = 18`; these instances are checked in [`Solution.lean`](Solution.lean).

`chung8_pebbling_latency_14` supplies `chung8Profile` — every field a theorem about the
constructed degree-eight profile — and `chung8Budget`, the `β_δ` orbit of the tracking
floor with its certificate. `chung8BudgetAt` gives the same budget at any source weight
in `[0.1184, 0.6]`, where the tracking constants do not move.

## The asymptotic bounds

`chung8_pebbling_latency_whp` prices a chosen number `z` of chain links, so its path
length grows with `ℓ` only through how many links the layer count pays for. The theorem
below is the Reyzin-style statement instead: a path length linear in `ℓ`, for every layer
count past a fixed head.

It comes from a change to the chain. `chung8_pebbling_latency_14` reaches a
footprint of weight `π`, takes *one* depth-robust path of length `α_π n` inside it, and
keeps that path's first `σ n` nodes as the next source; a source node is the `i`-th node
of a prefix, so it carries only the suffix behind it, and a link is worth
`(α_π - σ) n = 0.0816 n`. The asymptotic theorem instead takes as its source *every*
node of the footprint that begins a whole `α_π n` path inside it. If the footprint has
weight `τ + σ` and the layer is depth robust at threshold `τ`, there are at least `σ n` of
those ([`card_fullSources`](ProofOfSpace/FullSources.lean)) — delete the sources and depth
robustness hands back a long path whose first node was a source after all. Each link is
then worth the whole `α_π n = 0.2 n`.

That needs `τ + σ` to be the fertility threshold the ledger stops at, and the theorem
below closes that gap by raising the profile's threshold rather than weakening the game's.

### At Filecoin's robustness threshold

[`chung8_pebbling_latency_asymptotic`](Solution.lean) keeps the game's robustness
threshold at Filecoin's `π = 4/5` — the very hypothesis of
`chung8_pebbling_latency_14` — and raises the *profile's* fertility threshold to
`0.8886`, at source weight `σ = 0.0886`, so that `π + σ` meets it exactly. For every
`ℓ ≥ 22`, except with probability `2^(-lambda)`,

```text
(17/400)(ℓ - 21.2) n
```

so every layer buys another `0.0425 n`, against the `0.02135 n` per layer that
`chung8_pebbling_latency_whp` gives as `z` grows — 1.99 times the slope, under the same
graph assumption. This is the theorem for Filecoin's parameters, and it is a genuine
strengthening of `chung8_pebbling_latency_14` rather than a trade: the bound passes
`0.2 n` at `ℓ = 26`, first passes the `z`-link bound at `ℓ = 40`, and is ahead of it at
every layer count from `ℓ = 42` on.

The price is the head, `21.2` layers against `10.09`. Raising the fertility threshold
lowers the tracking gain from `g_π = 0.11131` to `0.04525`, and the ledger charges the
whole black budget `ρ = 0.8` at `λ/ĝ`, so that charge grows from `9.49` layers to
`19.89`; the per-link span grows from `3.8212` to `4.6991`.

What keeps the new certificate cheap is the reversal symmetry `β(1 - β x) = 1 - x` of the
polygon. The `β_δ` orbit of the new tracking floor `1 - β(0.8886) = 0.02834573` is the old
chain's list of `β`-values read backwards, so all five of its points

```text
0.02834573,  0.0736,  0.2284,  0.5337,  0.8   →  0.91131 = β_δ(4/5)
```

are certified breakpoints of the polygon already, and the first bucket is again exactly
`ĝ` wide. [`ChungFilecoinMirror.lean`](ProofOfSpace/ChungFilecoinMirror.lean) carries that
chain and its ledger certificate, at `λ = 9/8`, `cs = 2.33` and `loss = 0.79598`.

### The generic theorem

[`FullSources.lean`](ProofOfSpace/FullSources.lean) proves `latency_full_asymptotic`,
whose slope is `α_π / L.linkCost` for any profile and certified budget, and
`chung8_pebbling_latency_full_asymptotic` lifts it to the sampled wiring. Its graph
hypothesis is the single inequality `π + σ ≤ E.π`, and the theorem above is one way of
meeting it. Both are stated in
[`Challenge.lean`](Challenge.lean), proved in [`Solution.lean`](Solution.lean), and
registered in `comparator.json` alongside the other public theorems.

## One chain, one payoff parameter

The chain is the same object whatever its source rule is: a sequence of ever-shallower
source sets of weight `σ`, each reached from the one above through the footprint, ending
in the challenge set. Only two numbers about it vary — what one completed link is worth,
call it `y n`, and what the source rule assumes of the layer graph in order to deliver
`y`. [`PayChain.lean`](ProofOfSpace/PayChain.lean) carries the chain itself, parameterized
by `y` alone. A `SourceRule` is the whole of what the graph side supplies: at a fertile
footprint, one intra-layer path of the depth-robust length `α_π n`, and a source set of
weight `σ` every node of which begins a path of length `y n` inside that footprint. The
ledger of [`PotentialLedger.lean`](ProofOfSpace/PotentialLedger.lean) prices the chain
without ever seeing `y`, so `latency_pay` and its asymptotic form `latency_pay_asymptotic`
are the whole deterministic engine, and every latency theorem in the development is one
of their instances:

| theorem | source rule | payoff `y` | graph assumption |
| --- | --- | --- | --- |
| `latency_potential`, `latency_general` | `sourceRule_prefix` | `α_π - σ` | `DepthRobust α_π` at `π` |
| `latency_full`, `latency_full_asymptotic` | `sourceRule_full` | `α_π` | `DepthRobustThr (π - σ) α_π` |
| — | `sourceRule_mixed j` | `α_π - σ + j/n` | `DepthRobustThr τ α_π`, `j ≤ (π - τ) n` |

### The family between the two rules

Nothing forces a layer graph to sit at either end. `sourceRule_mixed` reads the *slack*
`π - τ` between the fertility threshold and the threshold the graph is actually robust
at, spends `j ≤ (π - τ) n` of it on nodes that begin a whole `α_π n` path inside the
footprint, and fills the source up to weight `σ` with a prefix of a path chosen to avoid
them. The `j` full nodes carry `α_π n`; the prefix is `j` nodes shorter than it would
otherwise be, so its last node carries `j` more. Either way a link is worth
`(α_π - σ) n + j`. `j = 0` is the prefix rule; `j = σ n` is the full rule.

[`chung8_pebbling_latency_mixed`](Challenge.lean) is that family on the sampled wiring,
and `chung8_pebbling_latency_whp` is proved from it as the case `j = 0`. It buys the
intermediate robustness thresholds that neither end covers. At the fourteen-layer
certificate (`E.π = 0.8`, `σ = 0.1184`, span `3.8212`, head `10.0853`) a graph robust at

```text
π = 0.8      0.0816 n per link,  slope 0.02135   (chung8_pebbling_latency_whp)
π = 0.75     0.1316 n per link,  slope 0.03444
π = 0.70     0.1816 n per link,  slope 0.04752
π = 0.6816   0.2000 n per link,  slope 0.05234
```

and at fourteen layers, where the certificate pays for two links, the bound at those
thresholds is `0.2816 n`, `0.3316 n`, `0.3816 n`, `0.4 n`. At the raised-threshold
certificate of [`ChungFilecoinMirror.lean`](ProofOfSpace/ChungFilecoinMirror.lean) the
same family runs from slope `0.02371` at `π = 0.8886` to `0.04256` at `π = 0.8`, the
latter being `chung8_pebbling_latency_asymptotic`.

The full rule stays a separate statement rather than the `j = σ n` instance for one
reason. At `j = σ n` the prefix is empty and the second depth-robustness call disappears
with it, so no deletion budget is needed and the threshold can be read at `π + σ ≤ E.π`
exactly; the mixed rule, which must delete `j` nodes before calling depth robustness
again, would have to ask for `π n + ⌈σ n⌉ ≤ E.π n`. The gap is one node of `n`, and it is
the only place where the family is not exact.

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
- [`ProofOfSpace/PayChain.lean`](ProofOfSpace/PayChain.lean) is the chain itself,
  parameterized by the per-link payoff, together with the prefix source rule.
- [`ProofOfSpace/FullSources.lean`](ProofOfSpace/FullSources.lean) is the
  full-length path-source lemma, the full and mixed source rules, and
  [`ProofOfSpace/FullSourcesFilecoin.lean`](ProofOfSpace/FullSourcesFilecoin.lean)
  is its deterministic Chung-8 instance.
- [`ProofOfSpace/ChungFilecoinMirror.lean`](ProofOfSpace/ChungFilecoinMirror.lean) is the
  raised-threshold ledger certificate: the mirrored reference chain at `E.π = 0.8886`
  that lets the full-payoff chain run at Filecoin's own robustness threshold `4/5`.
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
