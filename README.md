# Uniform-gain latency for stacked proofs of space

This Lean 4 project proves a general latency amplification theorem from ordinary
within-layer depth robustness, interval expansion, and static black/red pebble budgets.
The Filecoin corollary gives **at least `0.205n > 0.2n` path vertices at 18 layers**,
for `n >= 10000`, under the explicit depth-robustness and security conditions.

## The theorem

Use Reyzin's parameters: every set of density at least `π` contains an intra-layer
path on at least `απ n` vertices. Black pebbles have total density at most `ρ`;
red pebbles have density at most `δ` per layer. A challenge has density at least
`ζ`, with adjusted density `ζδ = ζ - δ`.

Choose integer footprint and source sizes `ceil(π n) <= m <= n` and
`1 <= s <= m`, and set `σ = s/n`. Define the gain explicitly by

```text
g = β(m/n) - δ - m/n.
```

The profile must be nondecreasing on the query interval

```text
I = [min(ζδ, β(m/n) - δ) - ρ, m/n],
```

whose lower endpoint must be positive. Require `σ ∈ I`, adjusted gain at least
`g > 0` throughout `I`, and the source condition

```text
β(σ) - δ - min(ζδ, β(m/n) - δ) + ρ >= 2g.
```

For `z >= 1`, the layer condition is

```text
g ℓ > ρ + g + max(m/n - ζδ, g + β(m/n) - β(σ))
          + (z - 1)(g + β(m/n) - β(σ)).
```

It guarantees a path ending in the challenge set `S` on at least
`ceil(απ n) + (z - 1)q` vertices, where the positive integer increment is

```text
q = min(ceil(απ n), ceil(απ n) + m - ceil(π n) - s + 1).
```

When `ζδ >= m/n`, the layer condition simplifies to

```text
ℓ > 1 + ρ/g + z(1 + (β(m/n) - β(σ))/g).
```

The source count follows from ordinary depth robustness. The gain condition
is a hypothesis; it is not automatic from the definition of `g`. With concave
`β`, it suffices to check it at the lower endpoint of `I`. The public theorem
fixes the gain at `m/n`; the internal scalar theorem also permits any smaller
certified positive gain.

The [explanation](../proof_of_space/lean/explanation.tex) gives the complete argument
and an appendix with the Filecoin specialization.

## Public results

All three are stated in [Challenge.lean](Challenge.lean), proved in
[Solution.lean](Solution.lean), and registered in [comparator.json](comparator.json).

- `pebbling_latency`: deterministic uniform-gain amplification for a port-wired stack.
- `chung8_pebbling_latency_whp`: the uniform probability theorem for any suitable
  profile below the entropy-defined Chung-8 curve.
- `chung8_pebbling_latency_18`: Filecoin fractions `π = 0.8`, `απ = 0.2`,
  `δ = 0.0378`, `ρ = 0.8`, `ζ = 0.9`; latency at least `(41/200)n`.

The last proof uses `m = ceil(0.8n)`, `s = ceil(0.195n)`, and `z = 2`.
It proves `0.111 <= g <= 0.11131` and
`g + β(m/n) - β(σ) <= 0.54212`. Thus the layer cost is at most
`1.99555 < 1.998 <= 18g`, and the integer path bound
`2 ceil(0.2n) - ceil(0.195n) + 1` exceeds `0.205n`.

## Probability and scope

The random wiring is one uniform permutation of all `8n` ports, reused between
consecutive layers. On its expansion event, the result holds simultaneously
for all admissible within-layer graphs, pebble positions, and challenges,
including those chosen after observing the wiring. Reuse requires no factor of
`ℓ` in the expansion failure bound.

`chung8Beta` is defined by the entropy formula. Its exact finite union bound is
`chung8FailureBound`. The Filecoin corollary assumes
`ChungSecurityConditions n lambda (1/100) (24/25)`, which requires this sum to be
at most `2^(-lambda)`. The condition `n >= 10000` handles latency rounding;
it does not by itself establish a chosen security level.

The theorem is about an unpebbled path in a static snapshot. Within-layer depth
robustness remains a graph assumption. The development does not include a
reduction to time-indexed cryptographic latency or identify Filecoin's Feistel
wiring with a uniform port permutation.

## Proof organization

| Module | Purpose |
| --- | --- |
| `Model.lean` | Physical layered DAGs, pebblings, footprints, and path splicing |
| `Sources.lean` | Exact integer source count from depth robustness |
| `UniformGain.lean` | Scalar floor invariants and affine layer accounting |
| `Amplification.lean` | Source chains and the general graph latency theorem |
| `PortModel.lean`, `PortStack.lean` | Port permutations and their physical stacks |
| `UnionBound.lean`, `PortExpansionProbability.lean` | Finite sampling and expansion probability |
| `Chung*.lean` | Entropy analysis and certified expansion lower bound |
| `UniformGainNumerics.lean` | Exact Filecoin gain and source estimates |

The internal graph theorem permits different layer graphs and interlayers.
The public game uses a single within-layer relation and a reused port permutation.
Lean depth zero denotes Reyzin's bottom level `ℓ`.

## Verification

```sh
lake build
./scripts/verify-comparator.sh
```

The proved library and `Solution.lean` contain no `sorry`. `Challenge.lean`
intentionally omits proof bodies. Comparator checks all three statements and
the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`); NanoDa replays
the solution through its independent kernel. The toolchain and verifier revisions
are pinned by the repository.

The argument builds on Leonid Reyzin's *Proofs of Space with Maximal Hardness*
(FOCS 2024) and Ben Fisch's *Tight Proofs of Space and Replication*
(EUROCRYPT 2019). Licensed under Apache-2.0.
