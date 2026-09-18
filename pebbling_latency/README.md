# Reference-trajectory latency for stacked proofs of space

This Lean 4 project proves latency amplification using ordinary within-layer
depth robustness, concave interval expansion, and static black/red pebble budgets.
The main theorem follows the paper's interpolated free-trajectory argument, with
explicit accounting for repair steps.

## The theorem

Write `p = m/n`, `σ = s/n`, `F(x) = β(x) - δ`, and `g = F(p) - p`.
Here `m` and `s` are integer footprint and source sizes, black pebbles have total
density at most `ρ`, red pebbles have density at most `δ` per layer, and the
challenge has density at least `ζ`. Choose a band floor `a` satisfying

```text
0 < a <= σ < p,       0 < g,
ρ + a <= min(ζ - δ, F(p)),
g <= F(a) - a,        2g <= F(σ) - σ.
```

Require `β` to be nondecreasing and concave on `[a,p]`, and a lower bound on
interlayer expansion for every vertex set whose density is in that interval.
Concavity and the endpoint conditions imply gain at least `g` throughout the band.

Let `y₀ = a`, `yᵢ₊₁ = F(yᵢ)`, and supply the first crossing time `t`:
`yᵢ < p` for `i < t` and `p <= yₜ`. Let `τ` linearly interpolate `τ(yᵢ) = i`.
Define

```text
D  = τ(p) - τ(σ),
D₀ = τ(p) - τ(min(p, ζ - δ)),
κ  = F(σ) - a - 2g.
```

For `z >= 1`, the proved layer condition is

```text
ℓ > 1 + D₀ + (z - 1)(1 + D) + ρ/g + max(0, (ρ - κ)/g).
```

It guarantees an unpebbled path ending in the challenge with at least
`ceil(απ n) + (z - 1)q` vertices, where

```text
q = min(ceil(απ n), ceil(απ n) + m + 1 - (ceil(π n) + s)).
```

Subtraction in this definition is natural-number subtraction. The theorem
requires `ceil(π n) <= m` and `q >= 1`; ordinary depth robustness says that every
set of at least `ceil(π n)` vertices contains a path with at least `ceil(απ n)`
vertices. All vertex rounding is retained in the formal statement.

The global correction `max(0, (ρ - κ)/g)` pays for repairs. The theorem does
not assume that repairs have zero net cost or replace the floor-based `D` by the
seed's free fertility time. It is a corrected sufficient bound, with no claim
of optimal constants or exact equivalence to the unfinished draft.

The notation above follows Carla's September 17 revision: her new `κ` is
`Reference.Parameters.K`. The registered statement retains its original local
name `κ₀=F(σ)-a`; its correction `max(0,(ρ-κ₀)/g+2)` is exactly the same bound.
The manuscript now defines `τ_x=τ(p)-τ(x)` and uses it in the Terminal theorem.
Its condition (a) requires `ζ-δ >= π`, which gives `D₀=0` when `p=π`.

[Transition.lean](ProofOfSpace/Transition.lean) now proves the September 18
kill-length certificate `c + τ_(p-κ-mg) - κ/g`, including the elimination of
actual spending `W`, and sums the strict kill premiums over disjoint windows.
[CrushAllowance.lean](ProofOfSpace/CrushAllowance.lean) proves that the resulting
integer optimization is finite and attains its maximum, bounds every feasible
plan by `A(B)`, and proves monotonicity in the available budget. The empty plan
is retained at zero budget. Carla has repaired the earlier parent-regrowth depth
claim and restored local spending and parent containment to Transition (III).

The registered graph proof continues to use its proved global repair bound.
The new manuscript's full Transition/Terminal/Round construction and cost
theorem are not asserted as end-to-end Lean results. In particular, its latency
maximum needs a domain restriction and its finite-depth existence argument
needs completion. [ADVISOR_ALIGNMENT.md](ADVISOR_ALIGNMENT.md#september-18-review)
records the remaining issues. The verified 17-layer result is unchanged.

## Public results

The single registered theorem is `ProofOfSpaceStatement.pebbling_latency`, stated
in the Mathlib-only [Challenge.lean](Challenge.lean) and proved in
[Solution.lean](Solution.lean). [comparator.json](comparator.json) selects it.

- `pebbling_latency`: deterministic reference-trajectory amplification.
- `chung8_reference_latency_whp`: its uniform probability counterpart for any
  suitable profile below the entropy-defined Chung-8 curve.
- `chung8_reference_latency_17`: the Filecoin specialization, proved from the
  reference-trajectory theorem with finite-width rounding.

## Filecoin layer count

**17 layers suffice for at least `0.205n > 0.2n` path vertices**, for every
`n >= 10000`, under the explicit depth-robustness and Chung security assumptions.
The parameters are `π = ρ = 0.8`, `απ = 0.2`, `δ = 0.0378`, and `ζ = 0.9`.
Choose `m = ceil(0.8n)`, `s = ceil(0.195n)`, `z = 2`, and `a = 0.05089`.

For the certified rational profile `ChungCurve.filecoinBeta`, the free trajectory
from `a` is exactly

```text
0.05089, 0.1622, 0.4285, 0.7338, 0.8886.
```

Ignoring vertex rounding, `g = 0.11131`, `D₀ = 0`, `D ≈ 2.30447922`, and
`κ ≈ 0.20711326`; the layer condition is `ℓ > 16.81806055`.
The Lean corollary accounts for rounding uniformly for `n >= 10000`, using
`g >= 0.111`, `g <= 0.11131`, `D <= 2.31`, and a repair density at most `0.59291`:

```text
ρ + repair + g(2+D) <= 1.8726561 < 1.887 <= 17g.
```

The exact path count is `2 ceil(0.2n) + 1 - ceil(0.195n) >= 0.205n`.
This is a sufficient layer count certified by the theorem, not a lower bound
showing that fewer layers are impossible. Within-layer depth robustness and
`ChungSecurityConditions n lambda (1/100) (24/25)` remain explicit hypotheses.

## Filecoin crush allowance

For the cost-model choice `σ = απ = 0.2`, with `π = ρ = 0.8`, `δ = 0.0378`
and `ζ = 0.9`, Carla's new definition gives:

| Expansion profile | `c_free^max` | `b_max = ceil(c_free^max + ρ/g)` |
| --- | ---: | ---: |
| Entropy-defined Chung-8 curve, numerical evaluation | 0.692642050643042 | 8 |
| Certified rational `ChungCurve.filecoinBeta`, exact Lean proof | `6011005/8615394 ≈ 0.697705177499717` | 8 |

Both maxima use initial depth zero and one crush of kill length four. Two
crushes cannot fit in the budget. For initial depth one, the remaining budget
is `0.7378`, the maximizing kill length is three, and the resulting total
certificate is smaller. These are unrounded density calculations; the rational
profile result is separate from the entropy calculation, not an error bound
for it or a newly proved graph cost theorem.

[FilecoinCrushNumerics.lean](ProofOfSpace/FilecoinCrushNumerics.lean) proves the
exact rational maximum and `b_max = 8`.
[FILECOIN_CRUSH_ALLOWANCE.md](FILECOIN_CRUSH_ALLOWANCE.md) gives the enumeration,
assumptions, and reproducible calculation command.

## Probability and scope

The random wiring is one uniform permutation of all `8n` ports, reused between
consecutive layers. On its expansion event the result holds simultaneously for
all admissible within-layer graphs, pebble positions, and challenges, including
those chosen after observing the wiring. Reuse requires no factor of `ℓ` in the
expansion failure bound.

`chung8Beta` is defined by the entropy formula. The probability theorem assumes
`ChungSecurityConditions n lambda u v`, including the exact finite union bound
`chung8FailureBound <= 2^(-lambda)` on the chosen interval. Within-layer depth
robustness remains a graph assumption. The conclusion concerns an unpebbled
path in a static snapshot.

## Proof organization

| Module | Purpose |
| --- | --- |
| `Delay.lean` | Interpolated clock, concavity, general and seed-based delay bounds |
| `Reference.lean` | Floors, standard expandability, protected levels, finite budget accounting |
| `Transition.lean` | First-fertile and kill-length certificates, parent floor, exact terminal spending bounds, historical regrowth example |
| `CrushAllowance.lean` | Finite attained crush maximum, budget monotonicity, clock domain, zero-budget case |
| `ReferenceAmplification.lean` | Actual footprint lower bounds, source chains, graph latency |
| `Model.lean`, `Sources.lean` | Physical graphs, path splicing, exact integer source count |
| `PortModel.lean`, `PortStack.lean` | Port permutations and their physical stacks |
| `UnionBound.lean`, `PortExpansionProbability.lean`, `Chung*.lean` | Finite expansion probability and entropy bounds |
| `FilecoinReferenceNumerics.lean` | Exact free trajectory and rounded 17-layer estimates |
| `FilecoinCrushNumerics.lean` | Exact cost-model crush optimization and `b_max = 8` for the rational profile |

Lean depth zero is the paper's bottom level `ℓ`. The internal graph theorem
permits different layer graphs and interlayers; the public game uses one
within-layer relation and a reused port permutation.

## Verification

```sh
lake build
../scripts/verify-comparator.sh pebbling_latency
```

The proved library and `Solution.lean` contain no `sorry`. `Challenge.lean` has
one intentional theorem placeholder. Comparator checks the public statement,
permits only `propext`, `Quot.sound`, and `Classical.choice`, and runs NanoDa replay.
