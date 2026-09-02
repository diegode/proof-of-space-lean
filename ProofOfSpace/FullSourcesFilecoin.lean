/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.FullSources
import ProofOfSpace.ChungFilecoin
import ProofOfSpace.ChungFilecoinMirror

/-!
# The asymptotic Filecoin latency bound at full link payoff

`FullSources.lean` proves that a chain of `z` full-payoff links realizes `z α_π n`, from
depth robustness at the threshold `S.pi - T.σ`.  This file instantiates it at the
degree-eight Chung profile of `ChungFilecoin.lean`, *reusing that file's certificate
unchanged*: the setting, tracking, reference chain and ledger certificate are the very
ones the fourteen-layer theorem is built from, so the three ledger prices are still

  `potHead = 463/774 = 0.5982`,  `potSpan < 3.8212`,  `λρ/ĝ = 105600/11131 = 9.4870`.

Only the graph assumption moves.  `chung8_latency_deterministic` assumes depth robustness
at `π = 4/5` and pays `(α_π - σ) n = 0.0816 n` per link; here the assumption is depth
robustness at `π - σ = 426/625 = 0.6816` — in deletion form, that removing `0.3184 n`
nodes of a layer still leaves an intra-layer path on `0.2 n` nodes — and every link pays
the whole `α_π n = 0.2 n`.

The resulting slope is `α_π / potSpan > 0.05234` of path per layer, against the
`(α_π - σ) / potSpan > 0.02135` of `Latency.lean`.
-/

namespace ProofOfSpace

namespace ChungCurve

open Concrete

universe u

/-- The per-link span is positive: the top saturation allowance alone is `331/774`. -/
theorem chung8_potSpan_pos :
    0 < LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) := by
  have h := (chung8RefChain).refPot_le_m (chung8Tracking).σ
  simp only [LedgerCert.potSpan, chung8LedgerCert_loss, chung8RefChain_m] at *
  push_cast at *
  linarith

/-- The head of the asymptotic bound: the initial search plus the whole black budget,
`463/774 + 105600/11131 < 10.0853` layers. -/
theorem chung8_full_head_lt :
    LedgerCert.potHead (chung8RefChain) (chung8LedgerCert)
      + (chung8LedgerCert).lam * (chung8Setting).ρ / (chung8Tracking).ghat < 11 := by
  rw [chung8_potHead_eq, chung8_ledgerCharge_eq]
  norm_num

/--
**The asymptotic Filecoin latency bound.**

At the degree-eight Chung parameters, with the layer graphs depth robust at threshold
`426/625` for path length `α_π = 1/5`, every layer buys another `0.0523 n` of unpebbled
path ending in the challenge set.  The coefficient of `ℓ` is `α_π / potSpan`, certified
here at `523/10000`, and the offset `10.1` absorbs the ledger head
`463/774 + 105600/11131 < 10.0853`: the initial search and the whole black budget.

Against `chung8_latency_deterministic`, whose linear envelope is
`0.02135 (ℓ - 10.0853) + 0.2`, this is 2.45 times the slope and overtakes it at `ℓ = 16`,
the first layer count at which the discrete link count is still two.  The two are not
comparable as graph theorems: this one assumes depth robustness at `426/625`, that one
at `4/5`.
-/
theorem chung8_latency_asymptotic
    {V : Type u} {ℓ n : ℕ} (hℓ : 11 ≤ ℓ)
    (G : Concrete.LayeredGraph V (chung8Setting) ℓ n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5)
    (hDepth : G.DepthRobustThr ((426 : ℝ) / 625) G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8Setting).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A ((523 : ℝ) / 10000 * ((ℓ : ℝ) - 101 / 10) * n) := by
  have hℓ' : (11 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hthr : (chung8Setting).pi - (chung8Tracking).σ = (426 : ℝ) / 625 := by
    rw [chung8Setting_pi, chung8Tracking_sigma]; norm_num
  have hαpi0 : (0 : ℝ) ≤ G.αpi := by rw [hαpi]; norm_num
  have hlong : LedgerCert.potHead (chung8RefChain) (chung8LedgerCert)
      + (chung8LedgerCert).lam * (chung8Setting).ρ / (chung8Tracking).ghat < (ℓ : ℝ) :=
    lt_of_lt_of_le chung8_full_head_lt hℓ'
  have h := latency_full_asymptotic G P (chung8Tracking) (chung8LedgerCert) hn hαpi0
    (by rw [hthr]; exact hDepth) (chung8_zeta_le) (chung8_entry) (chung8_nobreak)
    (chung8_cs_slack) (chung8_potSpan_pos) hlong A hA hred hweight
  refine P.hasPath_mono A ?_ h
  -- weaken the certified span and head to the round constants of the statement
  set Sp := LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) with hSpdef
  have hSp0 : 0 < Sp := chung8_potSpan_pos
  have hSpB : Sp < 4 - 675 / 1113 + 331 / 774 := chung8_potSpan_lt
  rw [chung8_potHead_eq, chung8_ledgerCharge_eq, hαpi]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnum : (0 : ℝ) ≤ (ℓ : ℝ) - 463 / 774 - 105600 / 11131 := by linarith
  have hdiv : ((ℓ : ℝ) - 463 / 774 - 105600 / 11131) / (4 - 675 / 1113 + 331 / 774)
      ≤ ((ℓ : ℝ) - 463 / 774 - 105600 / 11131) / Sp :=
    div_le_div_of_nonneg_left hnum hSp0 hSpB.le
  set q : ℝ := ((ℓ : ℝ) - 463 / 774 - 105600 / 11131) / (4 - 675 / 1113 + 331 / 774)
    with hqdef
  have hqB : q * (4 - 675 / 1113 + 331 / 774) = (ℓ : ℝ) - 463 / 774 - 105600 / 11131 := by
    rw [hqdef]; field_simp
  norm_num at hqB
  have hkey : (523 : ℝ) / 10000 * ((ℓ : ℝ) - 101 / 10) ≤ q * (1 / 5) := by linarith
  have hstep1 : (523 : ℝ) / 10000 * ((ℓ : ℝ) - 101 / 10) * n ≤ q * (1 / 5) * n :=
    mul_le_mul_of_nonneg_right hkey hn0
  have hstep2 : q * (1 / 5) * (n : ℝ)
      ≤ (((ℓ : ℝ) - 463 / 774 - 105600 / 11131) / Sp) * (1 / 5) * n :=
    mul_le_mul_of_nonneg_right (by linarith) hn0
  linarith

/--
**The asymptotic Filecoin latency bound at Filecoin's own robustness threshold.**

The same full-payoff chain, run against the raised-threshold certificate of
`ChungFilecoinMirror.lean` instead.  Because `π' - σ' = 0.8886 - 0.0886 = 4/5` exactly,
the graph hypothesis here is depth robustness at `4/5` — the fourteen-layer theorem's own
assumption, unchanged — and every link still pays the whole `α_π n = 0.2 n`.

The coefficient of `ℓ` is `α_π / potSpan = 0.2 / 4.69908 > 0.0425`, certified here at
`17/400`, and the offset `21.2` absorbs the ledger head `1.23718 + 19.88763 < 21.12481`.
Against `chung8_latency_deterministic`, whose linear envelope is
`0.02135 (ℓ - 10.0852) + 0.2`, this is 1.99 times the slope at the *same* graph
assumption; the two are comparable, and this one is ahead from `ℓ = 42` on.
-/
theorem chung8_latency_asymptotic_filecoinDR
    {V : Type u} {ℓ n : ℕ} (hℓ : 22 ≤ ℓ)
    (G : Concrete.LayeredGraph V (chung8SettingHi) ℓ n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5)
    (hDepth : G.DepthRobustThr ((4 : ℝ) / 5) G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8SettingHi).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A ((17 : ℝ) / 400 * ((ℓ : ℝ) - 106 / 5) * n) := by
  have hℓ' : (22 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hthr : (chung8SettingHi).pi - (chung8TrackingHi).σ = (4 : ℝ) / 5 := by
    rw [chung8SettingHi_pi, chung8TrackingHi_sigma]; norm_num
  have hαpi0 : (0 : ℝ) ≤ G.αpi := by rw [hαpi]; norm_num
  have hlong : LedgerCert.potHead (chung8RefChainHi) (chung8LedgerCertHi)
      + (chung8LedgerCertHi).lam * (chung8SettingHi).ρ / (chung8TrackingHi).ghat
        < (ℓ : ℝ) :=
    lt_of_lt_of_le chung8Hi_head_lt (by linarith)
  have h := latency_full_asymptotic G P (chung8TrackingHi) (chung8LedgerCertHi) hn hαpi0
    (by rw [hthr]; exact hDepth) (chung8Hi_zeta_le) (chung8Hi_entry) (chung8Hi_nobreak)
    (chung8Hi_cs_slack) (chung8Hi_potSpan_pos) hlong A hA hred hweight
  refine P.hasPath_mono A ?_ h
  rw [chung8Hi_potHead_eq, chung8Hi_ledgerCharge_eq, chung8Hi_potSpan_eq, hαpi]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set q : ℝ := ((ℓ : ℝ) - (1 + 2640 / 11131) - 90000000 / 4525427)
    / (4 - 25 / 258 + 8860 / 11131) with hqdef
  have hqS : q * (4 - 25 / 258 + 8860 / 11131)
      = (ℓ : ℝ) - (1 + 2640 / 11131) - 90000000 / 4525427 := by
    rw [hqdef]; field_simp
  norm_num at hqS
  have hkey : (17 : ℝ) / 400 * ((ℓ : ℝ) - 106 / 5) ≤ q * (1 / 5) := by linarith
  exact mul_le_mul_of_nonneg_right hkey hn0

end ChungCurve

end ProofOfSpace
