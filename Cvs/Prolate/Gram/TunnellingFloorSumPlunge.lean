import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Prolate.TunnellingIntegralMargin
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.DyadicShellPowerSums

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tunnelling floor sum from the plunge count, the plunge law and the two cell floors

Split at `T_j = χ_{4j}/c² = ¾`. On `T_j ≤ ¾` the plunge law `1 − λ_{4j} ≤ c^K e^{−2cW}`, the CP-b floor
`σ'_j ≥ e^{−2cΔ − εc}` and `TunnellingIntegralMargin`'s margin bound each term by `√(c^{K(½+η)}e^{−g*c/2})`; on `T_j > ¾` the band floor
`σ'_j ≥ x^{−ε}`, the Karnik–Romberg–Davenport count and Cvs.Upstream.DyadicShellPowerSums give `x^{ε/2}(A·log(100c/π + 25) + B)`. Together:
`CaseFiniteFromWindowChain`'s `ExtTunnelSum η` for every `η ≥ 0`.
-/

noncomputable section

open Real Set Filter Finset Topology
open Cvs.Prolate.EvenRungsByIndex (lev lamR)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram cellGram_posDef)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.TunnellingIntegralMargin (tunW tunD gStar)
open Cvs.Upstream.DyadicShellPowerSums (InShell)

namespace Cvs.Prolate.Gram.TunnellingFloorSumPlunge
open Cvs.ZeroCounting

/-! ### The four inputs -/

/-- The rung level ratio `T_j = χ_{4j}/c²` at `c = 2πx`. -/
def tLev (x j : ℕ) : ℝ := lev (2 * π * x) (2 * j) / (2 * π * x) ^ 2

/-- The Karnik–Romberg–Davenport plunge count (arXiv:2006.00427, Theorem 3) restricted to the rungs `h_{4j}`. -/
def KRDCount : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ((univ.filter fun j : Cvs.Approximant.SpineSubspace.SF x =>
        ε < lamR (2 * π * x) (2 * (j : ℕ)) ∧ lamR (2 * π * x) (2 * (j : ℕ)) < 1 - ε).card : ℝ)
      ≤ 2 / π ^ 2 * log (100 * (2 * π * x) / π + 25) * log (5 / (ε * (1 - ε))) + 7

/-- The plunge law H-B9 on the rungs: `1 − λ_{4j} ≤ c^K e^{−2cW(T_j)}` whenever `c² − χ_{4j} ≥ 5c`. -/
def PlungeLaw : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x,
    5 * (2 * π * x) ≤ (2 * π * x) ^ 2 - lev (2 * π * x) (2 * (j : ℕ)) →
      1 - lamR (2 * π * x) (2 * (j : ℕ))
        ≤ (2 * π * x) ^ K * exp (-(2 * (2 * π * x) * tunW (tLev x j)))

/-- The CP-b floor H-cpb: `σ'_j ≥ e^{−2cΔ(T_j) − εc}` on the rungs with `T_j ≤ ¾`, for every `ε > 0`. -/
def CPbFloor : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, tLev x j ≤ 3 / 4 →
    exp (-(2 * (2 * π * x) * tunD (tLev x j)) - ε * (2 * π * x)) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)

/-- The band floor H-U ∧ H-top: `σ'_j ≥ x^{−ε}` on the rungs with `T_j > ¾`, for every `ε > 0`. -/
def BandFloor : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < tLev x j →
    (x : ℝ) ^ (-ε) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)

/-! ### The band sum in closed form -/

/-- The closed-form band constant `A(q) = (2/π²)(log 20/(1 − r) + log 2·r/(1 − r)²)`, `r = 2^{−q}`. -/
def bandA (q : ℝ) : ℝ :=
  2 / π ^ 2 * (log 20 / (1 - (1 / 2 : ℝ) ^ q) + log 2 * ((1 / 2 : ℝ) ^ q / (1 - (1 / 2 : ℝ) ^ q) ^ 2))

/-- The closed-form band constant `B(q) = 7/(1 − r)`, `r = 2^{−q}`. -/
def bandB (q : ℝ) : ℝ := 7 / (1 - (1 / 2 : ℝ) ^ q)

theorem bandA_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ bandA q := by
  have hr := Cvs.Upstream.DyadicShellPowerSums.half_rpow_lt_one hq
  have h1 : 0 < 1 - (1 / 2 : ℝ) ^ q := by linarith
  unfold bandA
  have : 0 ≤ log 20 := log_nonneg (by norm_num)
  have : 0 ≤ log 2 := log_nonneg (by norm_num)
  positivity

theorem bandB_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ bandB q := by
  have hr := Cvs.Upstream.DyadicShellPowerSums.half_rpow_lt_one hq
  unfold bandB
  exact div_nonneg (by norm_num) (by linarith)

/-- `log(5/(ε(1 − ε))) ≤ log 20 + k·log 2` at `ε = 2^{−k−1}`. -/
theorem log_krd_le (k : ℕ) :
    log (5 / ((1 / 2 : ℝ) ^ (k + 1) * (1 - (1 / 2 : ℝ) ^ (k + 1)))) ≤ log 20 + k * log 2 := by
  have he : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  have he1 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have h2 : 0 < (2 : ℝ) ^ k := by positivity
  rw [← log_pow, ← log_mul (by norm_num) h2.ne']
  refine log_le_log (div_pos (by norm_num) (mul_pos he (by linarith))) ?_
  rw [div_le_iff₀ (by nlinarith)]
  have : (2 : ℝ) ^ k * (1 / 2) ^ (k + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  nlinarith

/-- **The band power sum from a KRD-type count**: if `λ_i ∈ [½, 1]` and every plunge window `(ε, 1 − ε)` holds at
most `(2/π²)·L·log(5/(ε(1 − ε))) + 7` of them, then `Σ_i (1 − λ_i)^q ≤ A(q)·L + B(q)`. -/
theorem sum_one_sub_rpow_le {ι : Type*} (s : Finset ι) (lam : ι → ℝ) {q L : ℝ} (hq : 0 < q) (hL : 0 ≤ L)
    (hlam : ∀ i ∈ s, 1 / 2 ≤ lam i ∧ lam i ≤ 1)
    (hK : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ((s.filter fun i => ε < lam i ∧ lam i < 1 - ε).card : ℝ) ≤ 2 / π ^ 2 * L * log (5 / (ε * (1 - ε))) + 7) :
    ∑ i ∈ s, (1 - lam i) ^ q ≤ bandA q * L + bandB q := by
  have hπ : 0 ≤ 2 / π ^ 2 := by positivity
  have h20 : 0 ≤ log 20 := log_nonneg (by norm_num)
  have h2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hmain := Cvs.Upstream.DyadicShellPowerSums.sum_rpow_le_of_shellCount s (fun i => 1 - lam i) hq
    (a := 2 / π ^ 2 * L * log 20 + 7) (b := 2 / π ^ 2 * L * log 2)
    (fun i hi => ⟨by linarith [(hlam i hi).2], by linarith [(hlam i hi).1]⟩) (fun k => ?_)
  · calc _ ≤ _ := hmain
      _ = bandA q * L + bandB q := by unfold bandA bandB; ring
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : (s.filter fun i => InShell 0 (1 - lam i)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun i hi h => ?_
        have := (hlam i hi).1
        simp only [InShell, zero_add, pow_one] at h
        linarith [h.1]
      rw [this, Finset.card_empty]
      push_cast
      have : 0 ≤ 2 / π ^ 2 * L * log 20 := by positivity
      linarith
    · set ε : ℝ := (1 / 2 : ℝ) ^ (k + 1) with hε
      have he0 : 0 < ε := by positivity
      have hek : ε ≤ 1 / 4 := by
        calc ε ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 4 := by norm_num
      have hk1 : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 2 := by norm_num
      have hsub : (s.filter fun i => InShell k (1 - lam i)) ⊆ (s.filter fun i => ε < lam i ∧ lam i < 1 - ε) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        simp only [InShell] at hi
        refine ⟨hi.1, by linarith [(hlam i hi.1).1], by linarith [hi.2.1]⟩
      calc ((s.filter fun i => InShell k (1 - lam i)).card : ℝ)
          ≤ (s.filter fun i => ε < lam i ∧ lam i < 1 - ε).card := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ 2 / π ^ 2 * L * log (5 / (ε * (1 - ε))) + 7 := hK ε he0 (by linarith)
        _ ≤ 2 / π ^ 2 * L * (log 20 + k * log 2) + 7 := by
            gcongr; exact log_krd_le k
        _ = 2 / π ^ 2 * L * log 20 + 7 + 2 / π ^ 2 * L * log 2 * k := by ring

/-! ### The deep rungs -/

/-- On a deep rung the term `√((1 − λ)^p)/√σ'` is at most `√(c^{Kp}e^{−g*c/2})`, given the plunge law and the
CP-b floor at `ε = g*/2`. -/
theorem deep_term_le {c ω σ W D K p : ℝ} (hc : 0 < c) (hp : 1 / 2 ≤ p) (hω0 : 0 ≤ ω)
    (hω : ω ≤ c ^ K * exp (-(2 * c * W))) (hσ : exp (-(2 * c * D) - gStar / 2 * c) ≤ σ)
    (hm : gStar / 2 ≤ p * W - D) :
    √(ω ^ p) / √σ ≤ √(c ^ (K * p) * exp (-(gStar / 2) * c)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (exp_pos _) hσ
  rw [← sqrt_div' _ hσ0.le]
  refine sqrt_le_sqrt ?_
  have h1 : ω ^ p ≤ c ^ (K * p) * exp (-(2 * c * W) * p) := by
    calc ω ^ p ≤ (c ^ K * exp (-(2 * c * W))) ^ p := rpow_le_rpow hω0 hω (by linarith)
      _ = _ := by rw [mul_rpow (by positivity) (by positivity), ← rpow_mul hc.le, ← exp_mul]
  rw [div_le_iff₀ hσ0]
  calc ω ^ p ≤ c ^ (K * p) * exp (-(2 * c * W) * p) := h1
    _ ≤ c ^ (K * p) * (exp (-(gStar / 2) * c) * exp (-(2 * c * D) - gStar / 2 * c)) := by
        rw [← exp_add]
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
        nlinarith
    _ ≤ c ^ (K * p) * exp (-(gStar / 2) * c) * σ := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hσ (by positivity)

/-- `x·√(c^{Kp}e^{−g*c/2}) ≤ 1` at `c = 2πx`, eventually in `x`. -/
theorem eventually_deep_small (K p : ℝ) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) * √((2 * π * x) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x))) ≤ 1 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K * p + 2) (gStar / 2) (by linarith [Cvs.Prolate.TunnellingIntegralMargin.gStar_pos])
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hev := (ht.comp hc).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, eventually_ge_atTop 1] with x h hx1
  have hx : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hc0 : 0 < 2 * π * (x : ℝ) := by positivity
  have hxc : (x : ℝ) ≤ 2 * π * x := by nlinarith [pi_gt_three]
  simp only [Function.comp] at h
  have hpow : (2 * π * (x : ℝ)) ^ (K * p + 2) = (2 * π * x) ^ (K * p) * (2 * π * x) ^ 2 := by
    rw [rpow_add hc0, rpow_two]
  have hA : 0 ≤ (2 * π * (x : ℝ)) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x)) := by positivity
  rw [show (x : ℝ) * √((2 * π * (x : ℝ)) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x)))
      = √((x : ℝ) ^ 2 * ((2 * π * (x : ℝ)) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x)))) by
    rw [sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)], ← sqrt_one]
  refine sqrt_le_sqrt ?_
  calc (x : ℝ) ^ 2 * ((2 * π * x) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x)))
      ≤ (2 * π * x) ^ 2 * ((2 * π * x) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hxc 2) (by positivity)
    _ = (2 * π * x) ^ (K * p + 2) * exp (-(gStar / 2) * (2 * π * x)) := by rw [hpow]; ring
    _ ≤ 1 := h.le

/-! ### The band rungs and the assembly -/

/-- On a band rung, `√((1 − λ)^p)/√σ' ≤ x^{ε/2}(1 − λ)^{p/2}` from `σ' ≥ x^{−ε}`. -/
theorem band_term_le {x ω σ p ε : ℝ} (hx : 0 < x) (hω0 : 0 ≤ ω) (hσ : x ^ (-ε) ≤ σ) :
    √(ω ^ p) / √σ ≤ x ^ (ε / 2) * ω ^ (p / 2) := by
  have hxe : 0 < x ^ (-ε) := rpow_pos_of_pos hx _
  have h1 : √(ω ^ p) = ω ^ (p / 2) := by
    rw [sqrt_eq_rpow, ← rpow_mul hω0]; ring_nf
  have h2 : √(x ^ (-ε)) = x ^ (-(ε / 2)) := by
    rw [sqrt_eq_rpow, ← rpow_mul hx.le]; ring_nf
  calc √(ω ^ p) / √σ ≤ √(ω ^ p) / √(x ^ (-ε)) :=
        div_le_div_of_nonneg_left (sqrt_nonneg _) (sqrt_pos.mpr hxe) (sqrt_le_sqrt hσ)
    _ = x ^ (ε / 2) * ω ^ (p / 2) := by
        rw [h1, h2, rpow_neg hx.le, div_inv_eq_mul, mul_comm]

/-- `log(200x + 25) ≤ (2/ε)·225^{ε/2}·x^{ε/2}` for `x ≥ 1`. -/
theorem log_le_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    log (100 * (2 * π * x) / π + 25) ≤ 2 / ε * (225 : ℝ) ^ (ε / 2) * x ^ (ε / 2) := by
  have hπ := pi_pos
  have he : 100 * (2 * π * x) / π + 25 = 200 * x + 25 := by field_simp; ring
  rw [he]
  calc log (200 * x + 25) ≤ (200 * x + 25) ^ (ε / 2) / (ε / 2) := log_le_rpow_div (by linarith) (by linarith)
    _ ≤ (225 * x) ^ (ε / 2) / (ε / 2) := by
        gcongr; linarith
    _ = 2 / ε * (225 : ℝ) ^ (ε / 2) * x ^ (ε / 2) := by
        rw [mul_rpow (by norm_num) (by linarith)]; field_simp

/-- **The tunnelling floor sum** from the KRD count, the plunge law, the CP-b floor and the band floor:
`ExtTunnelSum η` for every `η ≥ 0`. -/
theorem extTunnelSum_of_floors (hK : KRDCount) (hP : PlungeLaw) (hD : CPbFloor) (hB : BandFloor)
    {η : ℝ} (hη : 0 ≤ η) : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η := by
  intro ε hε
  obtain ⟨K, hPK⟩ := hP
  set p : ℝ := 1 / 2 + η with hpdef
  have hp : 1 / 2 ≤ p := by linarith
  have hq : 0 < p / 2 := by linarith
  refine ⟨1 + bandB (p / 2) + bandA (p / 2) * (2 / ε * (225 : ℝ) ^ (ε / 2)), ?_⟩
  filter_upwards [hK, hPK, hD (gStar / 2) (by linarith [Cvs.Prolate.TunnellingIntegralMargin.gStar_pos]), hB ε hε,
    eventually_deep_small K p, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hKx hPx hDx hBx hsmall hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have hlam : ∀ j : Cvs.Approximant.SpineSubspace.SF x, 1 / 2 ≤ lamR (2 * π * x) (2 * (j : ℕ)) ∧ lamR (2 * π * x) (2 * (j : ℕ)) ≤ 1 :=
    fun j => ⟨Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (Cvs.Approximant.SpineSubspace.SF_lt x j j.2),
      Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 ((Cvs.Prolate.RungSpanBernsteinNikolskii.spine_landau hx).1 j (Cvs.Approximant.SpineSubspace.SF_lt x j j.2))⟩
  set f : Cvs.Approximant.SpineSubspace.SF x → ℝ := fun j => √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ p)
    / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)) with hf
  set M : ℝ := √((2 * π * x) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x)))
  -- deep rungs
  have hdeep : ∑ j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => tLev x j ≤ 3 / 4), f j ≤ 1 := by
    have hterm : ∀ j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => tLev x j ≤ 3 / 4), f j ≤ M := by
      intro j hj
      have hT : tLev x j ≤ 3 / 4 := (Finset.mem_filter.1 hj).2
      have hlev : lev (2 * π * x) (2 * (j : ℕ)) ≤ 3 / 4 * (2 * π * x) ^ 2 := by
        have := hT; unfold tLev at this; rwa [div_le_iff₀ (by positivity)] at this
      have h5 : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 - lev (2 * π * x) (2 * (j : ℕ)) := by nlinarith
      exact deep_term_le hc0 hp (by linarith [(hlam j).2]) (hPx j h5) (hDx j hT) (Cvs.Prolate.TunnellingIntegralMargin.half_gStar_le hp hT)
    have hcard : ((univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => tLev x j ≤ 3 / 4)).card : ℝ) ≤ x := by
      have h1 := Finset.card_filter_le (univ : Finset (Cvs.Approximant.SpineSubspace.SF x)) (fun j => tLev x j ≤ 3 / 4)
      have h2 : (univ : Finset (Cvs.Approximant.SpineSubspace.SF x)).card ≤ x := by
        rw [Finset.card_univ, Fintype.card_coe]
        exact (Finset.card_filter_le _ _).trans (Finset.card_range x).le
      exact_mod_cast h1.trans h2
    calc _ ≤ ∑ _j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => tLev x j ≤ 3 / 4), M := Finset.sum_le_sum hterm
      _ = (univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => tLev x j ≤ 3 / 4)).card * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x * M := mul_le_mul_of_nonneg_right hcard (sqrt_nonneg _)
      _ ≤ 1 := hsmall
  -- band rungs
  have hband : ∑ j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => ¬ tLev x j ≤ 3 / 4), f j
      ≤ (x : ℝ) ^ (ε / 2) * (bandA (p / 2) * log (100 * (2 * π * x) / π + 25) + bandB (p / 2)) := by
    set s := univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => ¬ tLev x j ≤ 3 / 4)
    have hterm : ∀ j ∈ s, f j ≤ (x : ℝ) ^ (ε / 2) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) := by
      intro j hj
      have hT : 3 / 4 < tLev x j := not_le.1 (Finset.mem_filter.1 hj).2
      exact band_term_le hx0 (by linarith [(hlam j).2]) (hBx j hT)
    have hL : 0 ≤ log (100 * (2 * π * x) / π + 25) := log_nonneg (by
      have : 0 ≤ 100 * (2 * π * x) / π := by positivity
      linarith)
    have hsum := sum_one_sub_rpow_le s (fun j => lamR (2 * π * x) (2 * (j : ℕ))) hq hL (fun j _ => hlam j)
      (fun e he0 he1 => le_trans (by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s)))
        (hKx e he0 he1))
    calc _ ≤ ∑ j ∈ s, (x : ℝ) ^ (ε / 2) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) :=
          Finset.sum_le_sum hterm
      _ = (x : ℝ) ^ (ε / 2) * ∑ j ∈ s, (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  -- assembly
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Cvs.Approximant.SpineSubspace.SF x))
    (fun j : Cvs.Approximant.SpineSubspace.SF x => tLev x j ≤ 3 / 4) f
  have hlog := log_le_rpow hx1 hε
  have hA := bandA_nonneg hq
  have hBn := bandB_nonneg hq
  have hxe : (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) = (x : ℝ) ^ ε := by
    rw [← rpow_add hx0]; ring_nf
  have hxe1 : (1 : ℝ) ≤ (x : ℝ) ^ ε := one_le_rpow hx1 hε.le
  have hxe2 : (x : ℝ) ^ (ε / 2) ≤ (x : ℝ) ^ ε := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxe0 : 0 ≤ (x : ℝ) ^ (ε / 2) := by positivity
  change ∑ j : Cvs.Approximant.SpineSubspace.SF x, f j ≤ _
  rw [← hsplit]
  calc _ ≤ 1 + (x : ℝ) ^ (ε / 2) * (bandA (p / 2) * log (100 * (2 * π * x) / π + 25) + bandB (p / 2)) :=
        add_le_add hdeep hband
    _ ≤ 1 + (x : ℝ) ^ (ε / 2) * (bandA (p / 2) * (2 / ε * (225 : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2))
          + bandB (p / 2)) := by gcongr
    _ = 1 + bandB (p / 2) * (x : ℝ) ^ (ε / 2)
          + bandA (p / 2) * (2 / ε * (225 : ℝ) ^ (ε / 2)) * ((x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2)) := by ring
    _ ≤ 1 * (x : ℝ) ^ ε + bandB (p / 2) * (x : ℝ) ^ ε
          + bandA (p / 2) * (2 / ε * (225 : ℝ) ^ (ε / 2)) * (x : ℝ) ^ ε := by
        rw [hxe]; gcongr; linarith
    _ = _ := by ring

end Cvs.Prolate.Gram.TunnellingFloorSumPlunge

end
