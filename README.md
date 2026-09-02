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

[`chung8_pebbling_latency_whp`](Challenge.lean) is the reusable probabilistic
Chung-8 theorem. Its game parameters, source weight `σ`, expansion range
`[a, b]`, and link count `z` are all symbolic. `Chung8LatencyRegion` gives a
semantic, proof-independent description of the covered scalar tuples: a tuple
belongs to the region when every wiring that expands on `[a, b]` gives the
deterministic `z`-link latency property, for every admissible game with those
fundamental parameters. The theorem itself is the transfer from that
deterministic hypothesis through the union bound; the latency content lives in
the region-membership proof, which for the 14-layer tuple is discharged in
`Solution.lean` from the analytic and potential-ledger certificates.

## Expansion is assumed only on a density range

`ChungInterlayer.ExpandsOn a b` demands the Chung-8 profile only of source sets
whose density lies in `[a, b]`, and `chung8FailureBound n a b` pays for exactly
that range. This matters: at density `1/n` a Chung profile is a birthday
collision, so a bound covering every nonempty set is `Θ(1/n)` however large `n`
is, and near density `1` the union bound is vacuous. The deterministic argument
only ever queries expansion at densities in `[αmin, αmax]`, and a set denser
than `b` is handled by expanding a subset of the queried density.

Both layer instances instantiate `[1/100, 24/25]`, which brackets the
Filecoin `[αmin, αmax] = [0.0129…, 0.9493…]`, and assumes `1000 ≤ n` so that the
rounding of a subset back into the range fits. `ChungSecurityConditions n lambda
a b` remains an assumption on the width: it is satisfiable at the deployed
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
