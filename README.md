# Latency Hardness for Stacked Proofs of Space

This repository contains a Lean 4 formalization of the latency argument in
[`docs/explanation.tex`](docs/explanation.tex), *The Hardness of Proofs of Space Beyond
Depth Robustness*. Its main result is a conditional lower bound that constructs an
explicit nonempty unpebbled directed path from a challenge footprint. Under the stated
expansion, depth-robustness, pebbling-budget, and scalar hypotheses, the path has length

```text
απ n + (zMin(ℓ) - 1)(απ - σ)n.
```

The Palomar statement of record is
[`ProofOfSpaceStatement.latency_general`](Challenge.lean). `Challenge.lean` imports only
allowlisted Mathlib modules and contains the one deliberate `sorry`; [`Solution.lean`](Solution.lean)
proves the same statement by invoking the substantive theorem
[`ProofOfSpace.latency_general`](ProofOfSpace/Latency.lean). [`comparator.json`](comparator.json)
asks Palomar's Comparator to check that correspondence and permits only `propext`,
`Classical.choice`, and `Quot.sound`.

This is a substantive formalization repository, not a thin wrapper. Its Palomar metadata
is in [`formalization.yaml`](formalization.yaml), and the root [`LICENSE`](LICENSE) is
Apache-2.0. Once a public commit is ready, submit its full 40-character commit SHA at
[the Palomar submission form](https://submit.palomar-registry.org/).

There is a single dependency chain and a single general latency theorem. The Filecoin
numbers come from *evaluating* that theorem's constants, which
`FilecoinLatencyParameters` does by carrying the three collapses `ĝ = g_π`, `g̃ = g_π`
and `b^max = 0` that `app:filecoin` verifies of the Chung-8 curve. The concrete
specialization remains conditional on the assumptions listed under
[Trust assumptions](#trust-assumptions).

## Notation

Every quantity the paper names has a Lean name that transcribes it, and every constant
is defined by the same formula:

| paper | defined at | Lean |
| --- | --- | --- |
| `β_δ`, `gain_δ`, `g_π`, `π̄` | `sec:model` | `Setting.betaD`, `.gainD`, `.gpi`, `.piBar` |
| `π̂` | `eq:tracking` | `Tracking.lam` |
| `ĝ` | `eq:tracking` | `Tracking.ghat` |
| `g̃` | `eq:gzeta` | `Setting.gtilde` |
| `s` | `eq:cap-search` | `sCap` (`= sCapOf S ĝ g̃`; `sCapOf S g h` is `s` at a general pair of gains) |
| `h_0` | `eq:cap-span` | `h₀` (`localSpan = h₀ - 1`, the `eq:attempt-bound` span, by `localSpan_succ_le_h₀`) |
| `h_1` | `eq:cap-span-global` | `h₁` (`= growthConst + 1`; see the optimized constants below) |
| `b^max` | `eq:cap-break` | `bMax` |
| `s_0`, `s_1` | `eq:global-constants` | `s₀`, `s₁` (the `2ρ/ĝ` term of `s_1` alone is `ledgerSlack`) |
| `s_2` | `eq:joint-constants` | `s₂` (its two summands are `searchHead` and `jointSlack`); the entry is `jointEntry` |
| `z_min(ℓ)` | `eq:zmin` | `zMin` (`zMinNoBreak` is `eq:zmin` specialized to `b^max = 0`) |
| `Φ`, `σ̃` | `eq:midpoint` | `growthPot`, `Tracking.mid`; the growth term of `h_1` is `growthConst` |
| `f`, footprint bound | `eq:footprint-bound` | `IsFootprintBound`, `footprintBound` |
| challenge footprint bound | `eq:challenge-bound` | `ChallengeBound`, `challengeBound` |
| `ρ_grow`, `ρ_cont` | `lem:growth-window`, `lem:fertile-continuation` | local `growthSpend`, `continuationSpend` in `extension_attempt_gen` |
| `ρ_search`, `ρ_attempts` | `lem:joint-ledger` | the search- and attempt-region interval sums in `general_ledger` |
| `∑_{j=i}^{i'} ρ_j` | `eq:budgets` | `∑ d ∈ Finset.Ico .., B.spend d` |
| level `j` | `sec:model` | `depth d = ℓ - j` — see below |

`Tracking.lam` is the retained Lean identifier implementing `π̂`.
`Tracking.sigmaHat` is an internal auxiliary: `π̂ = min{π̄, σ̂}` with
`σ̂ = min{σ, 1-β(σ)}`, while `eq:tracking` writes the three-way minimum directly.

## Optimized constants

The note and formalization retain two optimized bounds alongside the baseline
constant-charge and separate-ledger bounds.

1. **The growth constant.**  `eq:cap-span-global` linearizes the growth phase at the
   single rate `ĝ`, giving `h_1 = a + 1` with `a = max{1, (π-σ)/ĝ}`.  `Growth.lean`'s
   two-piece potential `growthPot` charges `2ĝ` per level on an initial segment
   `[σ, σ̃]`, which the source condition and concavity certify, and `ĝ` after it;
   `growthConst = min{a, Φ_{σ̃}(π) + 1}` takes whichever is better and
   `h₁ = growthConst + 1`.  The mid-point `σ̃` is the new `Tracking.mid` field —
   `mid := σ` is always admissible and recovers the old constant, and the Chung-8
   instantiation supplies `σ̃ = 3/5`.
   Filecoin: `5.957 < h₁ < 5.961` against `7.123`.

2. **The joint ledger.**  `s_1 = s + 2ρ/ĝ` charges the black budget `ρ` three times: in
   the infertile-capacity term of `s`, in its blocked-window term, and twice in
   `2ρ/ĝ`.  Searches and attempts occupy disjoint level ranges, so one interval sum
   pays for all three.  `s₂ = searchHead + 2ρ/min{ĝ,g̃}` is that accounting and
   `jointEntry` is the corresponding entry of `zMin`, guarded by `b^max = 0`.  The
   header of `Ledger.lean` has the argument; Filecoin: `s₂ < 14.82` against
   `s_1 > 28.36` (`FilecoinLatencyParameters.s₂_lt_s₁`).

`zMin` is a maximum and keeps the baseline entries beside the optimized ones, so no parameter
regime is worse off.  Together the two move the first layer count certifying more than
`0.2 n` from `ℓ = 36` to `ℓ = 21`, with the same `0.2816 n` at the threshold, and raise
the certified slope `(α_π - σ)/h_1` from `0.01146` to `0.01370`.

One indexing convention differs.

**Depth versus level.**  The paper follows Reyzin: the top layer is `V_1`, the bottom
layer `V_ℓ` carries the challenge, and the analysis reads the stack from level `ℓ`
upward to level `1`.  Lean instead counts *depth* forward from the challenge, so **Lean
depth `d` is the paper's level `ℓ - d`**: Lean `layer 0` is the paper's `V_ℓ`, Lean
`layer (ℓ-1)` is the paper's `V_1`, and Lean's inter-layer edges from `layer (d+1)` to
`layer d` are the paper's `V_{j-1}` to `V_j`.  Every direction word flips: the paper's
recurrence runs upward in `j`, Lean's runs forward in `d`.  Counting forward is what
keeps the recurrence and every induction free of truncated `ℕ` subtraction.

The paper reserves *depth* for the length of a path and *level* for a layer index, so
the Lean fields named `depth` are level indices in the paper's sense; `NodeDepthRobust`
and its relatives use `depth` in the paper's path-length sense.

## Structure

Files in dependency order.

- `Chung.lean`, `Expansion.lean`, `Footprint.lean`, `Tracking.lean`, `Search.lean`,
  `Continuation.lean`: the reversal law, the expansion calculus, the footprint
  recurrence and its floors, the fertile–expandable search, and the continuation lemmas.
- `Growth.lean`: the mirror floor, the growth window `growth_window`, and the
  post-fertile floor.  It also carries the two-piece growth potential `growthPot` and
  its window bound `growthPot_window`, which sharpen the growth constant under the
  doubled-gain certificate carried by `Tracking.mid`.  `growthConst` at the end of the
  file is what `Chain.h₁` uses; the `ℕ`-valued `growthSpan`/`growthCap` still drive
  `localSpan` and `h₀`, the constant-charge entry.  That file's section header has the
  exact comparison of the two window constants.
- `Potential.lean`: the reference-trajectory potential.  A `RefChain` is a finite
  chain `x 0 ≤ … ≤ x m` with `x (k+1) ≤ β_δ (x k)` and every step at least `ĝ` wide;
  `refPot` is the piecewise-linear potential normalized by `refPot (x k) = k`.  Its
  three properties — monotone, `1/ĝ`-Lipschitz (`refPot_lipschitz`), and one free level
  advancing it by one up to saturation (`refPot_step`) — are proved from **concavity of
  `β_δ` alone**, through the chord inequality `bucket_shift`.  This generalizes
  `Growth.lean`'s two-piece `growthPot`, whose single doubled-gain certificate it
  replaces by the whole `β_δ` orbit. Not yet consumed by the ledger.
- `Chain.lean`: the `ChainSystem` interface and the unique definitions of `h₀`, `h₁`,
  `ledgerSlack`, `localSpan` and `zMinNoBreak`.  The accounting that consumes them is
  in `Ledger.lean`.
- `Ledger.lean`: the **single** chain-counting theorem, formalizing `sec:latency`.
  `GeneralRegime` is `eq:scalar-conditions`.  Two things
  change once breaks are possible and nothing else does: infertile challenge levels are
  charged at the coarser rate `g̃` of `eq:gzeta` (`lem:challenge-floor`), and an attempt
  can *break*.  `extension_attempt_gen` is `lem:extension-attempt`, whose third outcome
  is the tracked footprint falling below `π̂`; `general_ledger` runs the whole
  construction — attempts, breaks and restart searches — through one induction that
  charges every level of the graph to one of four capacities and carries the
  constant-charge bound and `eq:level-ledger` simultaneously; `exists_many_links_gen` is
  `lem:chain-length`, the pigeonhole over the at most `b^max + 1` segments.  Restart
  searches are charged *together* at `s(ĝ, g̃)`, as the proof of `lem:global-ledger`
  claims, because `infertile_card_le_gen` bounds the infertile count of every prefix and
  the searches occupy disjoint level ranges.  The paper splits this into the four
  displayed inequalities of `lem:global-ledger` (`eq:segment-ledger`, `eq:level-ledger`,
  `eq:global-level-ledger`, `eq:break-ledger`) and combines them in `lem:chain-length`;
  Lean fuses them into the one induction, so there is no Lean statement matching any of
  the four on its own.

  A break is charged `β_δ(π) - π̂` (`Growth.break_charge`, the paper's
  `lem:break-charge`), so the budget condition of `eq:no-break-conditions` —
  `ρ < β_δ(π) - π̄` — says outright that no break can be paid for and `bMax_eq_zero`
  fires.  `zMin` carries the ledger entry alongside the constant-charge one, so the
  certified slope stays `1/h_1` (≈ `1/5.96` at Filecoin) instead of `1/h_0` (= `1/29`);
  `slope_comparison` puts the ratio at `4.87`.  `zMin` carries the joint-ledger entry
  `jointEntry` as well, which is what fixes the offset.  `zMin_eq_zMinNoBreak` then proves the
  general chain length *equals* `zMinNoBreak` whenever `b^max = 0`.
- `Concrete.lean`: genuine directed paths, reachability footprints, the concrete
  red/black pebbling model, the proved footprint recurrence, and the concrete
  base/extension operations.  `Pebbling.footprintBound_le` proves that the scalar bound
  really is dominated by the actual footprint, and `IsFootprintBound.sum_le` is the
  accumulated form of the recurrence; the paper quotes both to Reyzin rather than
  proving them.  The pebbling model is a *static space snapshot*, not a time-indexed
  game; see the `Pebbling` docstring for what that does and does not certify.  The
  intra-layer depth-robustness and inter-layer expansion properties remain explicit
  graph-construction assumptions; bounded-degree realizations are in
  `Constructions.lean`.  Ordinary `(e, dep)` node depth robustness in deletion-set form,
  and its equivalence with the survivor form the latency theorem consumes, are here as
  `NodeDepthRobustAt` and `depthRobustAt_iff_nodeDepthRobustAt`.
- `Latency.lean`: the public end-to-end concrete latency theorems and path witnesses,
  the exact path-length formula, the finite linear/hardness-gap bounds, and the
  certified Filecoin numerical specialization.  `latency_general` is the concrete form
  of `thm:latency`, and the only one.  `FilecoinLatencyParameters.zMin_eq` evaluates its
  `zMin` to `filecoinZMin` by rewriting with `zMin_eq_zMinNoBreak`, `sCap_eq_sCapOf` and
  `zMinNoBreak_eq`, so the Filecoin corollaries are substitutions into `latency_general`
  rather than a second theorem.  It proves `filecoinZMin 20 = 1` and
  `filecoinZMin 21 = 2`; hence the first strict improvement over `0.2 n` occurs at
  `ℓ = 21`, where `latency_21` gives `0.2816 n`.
- `ChungCurve.lean`, `ChungNumerics.lean`, `ChungFilecoin.lean`: the canonical
  specialization, on the genuine degree-eight Chung curve.  `ChungCurve.lean` constructs
  `chungBeta d` as the unique zero of the union-bound exponent and proves mapping,
  strict expansion, strict monotonicity, and the reversal law for it;
  `ChungNumerics.lean` discharges the Filecoin scalar inequalities from logarithm
  brackets, pinning `0.1113 < g_π < 0.1114`; `ChungFilecoin.lean` assembles
  `chung8Setting` and the `ℓ = 21` latency corollary `chung8_latency_21`.  Its two
  unproved global shape facts are isolated in `Chung8AnalyticAssumptions`.
- `Constructions.lean`: concrete small-indegree graph constructions, so the graph
  hypotheses stop being about an abstract `G`.  Its declarations correspond to the
  source paper's construction section.  The shape of the correspondence:
  `permutationStack` is the stack of `def:permutation-stack`, whose layer
  hypothesis `permutationStack_nodeDepthRobustAt_iff` shows is *exactly* the standalone
  one; `DRSampleAdmissible` and `DRSampleParentLaw` are the bucket-then-gap sampler of
  `def:drsample`; `intervalBlockTransfer` is `thm:interval-contraction` and
  `bucketSample_nodeDR_of_blockNodeDR` is `cor:bucketsample-node-dr`, which together
  reduce a deployed layer to a single block certificate for the base graph;
  `FilecoinWithinLayerTarget` is `eq:deployed-layer` and
  `depthRobust_of_filecoinWithinLayerTarget` is `prop:deployed-layer-suffices`.  What is
  left open is `ass:deployed-certificate`, whose degree-two form is
  `DRSampleFilecoinConjecture`; `filecoin_budget_exceeds_published_certificate` and
  `filecoin_depth_exceeds_published_certificate` are the two halves of
  `prop:published-gap`, and `shortSeed_not_target` is `rem:seed-not-shape`.

- `Witness.lean`: a consistency witness, not a specialization.  The Möbius curve
  `β(x) = 2916x/(625+2291x)` has concavity and a unique gain maximizer as theorems, so
  it closes a model — `wSetting`, `wGeneralRegime`, `wFilecoin` — of the hypothesis
  stack the development quantifies over.  That model is what keeps the theorems from
  being vacuous.  The curve is not a profile claimed for any construction: it runs above
  the degree-eight Chung boundary, so the degree-eight union bound does not certify it.

The entry point `ProofOfSpace.lean` imports the canonical latency chain through the
Chung-8 specialization (`ChungFilecoin`), the constructions (`Constructions`), and the
Möbius consistency witness (`Witness`).

## How to Execute

With [Lean 4](https://leanprover.github.io/) installed, run from this directory:

```bash
lake build
```

Exit code `0` means the whole public dependency graph typechecks.  The development
declares no axioms of its own: `#print axioms` on any public result returns only
`propext`, `Classical.choice`, and `Quot.sound`, and there is no `sorry`.

That axiom claim is checked mechanically rather than by reading `#print axioms` output
by hand.  Also from this directory:

```bash
lake env lean scripts/AxiomAudit.lean
```

It walks every declaration in the `ProofOfSpace` namespace -- all modules are reachable
from the entry point, so that is the whole development -- and fails if any of them
depends on an axiom outside those three, `sorryAx` included.  `scripts/` sits outside
the library root, so `lake build` does not compile it.

Both commands run on every push and pull request in
`.github/workflows/lean_action_ci.yml`.

## Trust assumptions

Inspect the hypotheses of `chung8_latency_21`.  There are three groups.

1. `LayeredGraph.expands` — that the sampled permutation interlayers realize the
   profile, in the sense of `def:permutation-stack`.  The paper does not compute this
   probability either: `prop:stack` and `prop:deployed-layer-suffices` take realization
   as a hypothesis.  `PermutationExpansionWhpClaim` is the probability-facing form of
   the claim; nothing consumes it, it only names the gap.

2. `LayeredGraph.DepthRobust`, passed in at each call site — the paper's
   `ass:deployed-certificate`, and its open construction problem: no bounded-degree
   construction is known that is simultaneously expanding and node depth robust at that
   budget.  The published DRSample certificate (`prop:abh-certificate`) is far short in
   both coordinates.  Its deletion budget at the deployed base size `N = 5·2^30` is
   about `4·10^4`, against the `(1 - π)n = 214,748,364` deletions the target quantifies
   over at `n = 2^30`; `filecoin_budget_exceeds_published_certificate` proves the
   shortfall for *any* budget up to `10^6`, so it survives granting the published one a
   factor of `25`.  On depth, contraction by `r = 5` turns the published `0.03N` into
   `0.03·2^30` metavertices, and `filecoin_depth_exceeds_published_certificate` shows
   six times that is still below the target.  `rem:valiant` also bounds how general any
   fix can be: by Valiant depth reduction, no indegree-six family satisfies
   `eq:deployed-layer` for all large `n`, so the assumption is necessarily a
   finite-size statement.  It is not formalized.

3. `Chung8AnalyticAssumptions` — that `chungBeta8` is concave on `[0,1]` and that its
   unadjusted gain has a unique maximizer.  Everything else the expansion calculus needs
   is derived, including both adjusted-gain roots.  `Witness.lean` does not discharge
   this group: its model is a different curve.  The proofs use concavity only through
   the endpoint-minimum property of `gain_δ` on subintervals, so quasi-concavity of
   `β(x) - x` would suffice and would subsume the maximizer clause.  `chung8_αg_unique`
   shows any two instances of the bundle give the same `chung8Setting`, which is
   rigidity, not consistency.
