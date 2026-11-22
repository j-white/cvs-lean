import Mathlib
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.StepACriterion
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.PointInterpolationHardyDatum
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Blaschke product of the other deep points at `w_σ`, uniformly in the height

For a zero `σ` with `w = w_σ` and every deep set, the Blaschke product of `deepPts δ_D H ∖ {w, w̄}` at `w` is at
least `β_σ = e^{−K_σ/2}`, `K_σ = #N_σ/d_σ + (|γ_σ| + 1)²Z`, where `N_σ` holds the zeros with `|γ| ≤ |γ_σ| + 1`,
`d_σ = Π_{ρ ∈ N_σ, w_ρ ∉ {w, w̄}} min(1, |w − w_ρ|²)` and `Z = Σ m_ρ/γ²` (caseinf-W Theorem F (v)).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.WindowCoshTransformDuality (wR)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (deepPts)
open Cvs.Upstream.PointInterpolationHardyDatum (bS)

namespace Cvs.StepA.Edge.OtherDeepPointsBlaschke
open Cvs.ZeroCounting

/-- The near zeros `N_σ = {ρ : |γ_ρ| ≤ |γ_σ| + 1}`. -/
def nearSet (σ : nonTrivialZeroSet) : Finset nonTrivialZeroSet := deepSet 0 (|(σ : ℂ).im| + 1)

/-- The near zeros whose point is neither `w_σ` nor its conjugate. -/
def nearOther (σ : nonTrivialZeroSet) : Finset nonTrivialZeroSet :=
  (nearSet σ).filter fun ρ => wR ρ ≠ wR σ ∧ wR ρ ≠ conj (wR σ)

/-- `d_σ = Π_{ρ ∈ nearOther σ} min(1, |w_σ − w_ρ|²)`. -/
def dS (σ : nonTrivialZeroSet) : ℝ := ∏ ρ ∈ nearOther σ, min 1 (‖wR σ - wR ρ‖ ^ 2)

theorem dS_pos (σ : nonTrivialZeroSet) : 0 < dS σ := by
  unfold dS
  refine Finset.prod_pos fun ρ hρ => lt_min one_pos ?_
  have h := (Finset.mem_filter.1 hρ).2.1
  exact pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))) 2

theorem dS_le (σ : nonTrivialZeroSet) {ρ : nonTrivialZeroSet} (hρ : ρ ∈ nearOther σ) :
    dS σ ≤ ‖wR σ - wR ρ‖ ^ 2 := by
  unfold dS
  have hle : ∏ ρ' ∈ nearOther σ, min 1 (‖wR σ - wR ρ'‖ ^ 2) ≤ min 1 (‖wR σ - wR ρ‖ ^ 2) := by
    rw [← Finset.mul_prod_erase _ _ hρ]
    refine mul_le_of_le_one_right (le_min zero_le_one (sq_nonneg _)) ?_
    exact Finset.prod_le_one₀ (fun _ _ => le_min zero_le_one (sq_nonneg _)) fun _ _ => min_le_left _ _
  exact hle.trans (min_le_right _ _)

/-- `K_σ = #N_σ/d_σ + (|γ_σ| + 1)²Z`. -/
def kS (σ : nonTrivialZeroSet) : ℝ :=
  (nearSet σ).card / dS σ + (|(σ : ℂ).im| + 1) ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum

/-- One point against `w_σ`: `1/|w_σ − w_ρ|² ≤ [ρ ∈ N_σ]/d_σ + (|γ_σ| + 1)²m_ρ/γ_ρ²`. -/
theorem inv_norm_sq_le (σ ρ : nonTrivialZeroSet) (h1 : wR ρ ≠ wR σ) (h2 : wR ρ ≠ conj (wR σ)) :
    1 / ‖wR σ - wR ρ‖ ^ 2 ≤ (if ρ ∈ nearSet σ then 1 / dS σ else 0)
      + (|(σ : ℂ).im| + 1) ^ 2 * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)) := by
  have hn0 : 0 < ‖wR σ - wR ρ‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h1))) 2
  have hm : (1 : ℝ) ≤ mult ρ := by exact_mod_cast Cvs.Criterion.one_le_divisorWeight ρ
  have hγρ : (6.24 : ℝ) < |(ρ : ℂ).im| := Cvs.StepA.StepACriterion.lt_abs_im ρ
  have hsq : 0 < ((ρ : ℂ).im) ^ 2 := by rw [← sq_abs]; nlinarith
  by_cases hN : ρ ∈ nearSet σ
  · rw [ite_eq_left hN]
    have hρ : ρ ∈ nearOther σ := Finset.mem_filter.2 ⟨hN, h1, h2⟩
    have := dS_le σ hρ
    have hd := dS_pos σ
    have h3 : 1 / ‖wR σ - wR ρ‖ ^ 2 ≤ 1 / dS σ := one_div_le_one_div_of_le hd this
    have : 0 ≤ (|(σ : ℂ).im| + 1) ^ 2 * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)) := by positivity
    linarith
  · rw [ite_eq_right hN, zero_add]
    have hfar : |(σ : ℂ).im| + 1 < |(ρ : ℂ).im| := by
      by_contra h
      exact hN (mem_deepSet.2 ⟨not_lt.1 h, abs_nonneg _⟩)
    have hσa := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im σ
    have hρa := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im ρ
    have him : |(ρ : ℂ).im| - |(σ : ℂ).im| ≤ ‖wR σ - wR ρ‖ := by
      have e : |(wR σ - wR ρ).im| ≤ ‖wR σ - wR ρ‖ := Complex.abs_im_le_norm _
      have e2 : |(wR ρ).im| - |(wR σ).im| ≤ |(wR σ - wR ρ).im| := by
        rw [Complex.sub_im, abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
      rw [hσa, hρa] at e2
      linarith
    have hratio : |(ρ : ℂ).im| / (|(σ : ℂ).im| + 1) ≤ |(ρ : ℂ).im| - |(σ : ℂ).im| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg ((σ : ℂ).im)]
    have hpos : 0 < |(ρ : ℂ).im| / (|(σ : ℂ).im| + 1) := by positivity
    have hb : (|(ρ : ℂ).im| / (|(σ : ℂ).im| + 1)) ^ 2 ≤ ‖wR σ - wR ρ‖ ^ 2 :=
      pow_le_pow_left₀ hpos.le (hratio.trans him) 2
    calc 1 / ‖wR σ - wR ρ‖ ^ 2 ≤ 1 / (|(ρ : ℂ).im| / (|(σ : ℂ).im| + 1)) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) hb
      _ = (|(σ : ℂ).im| + 1) ^ 2 * (1 / ((ρ : ℂ).im) ^ 2) := by
          rw [div_pow, sq_abs]; field_simp
      _ ≤ (|(σ : ℂ).im| + 1) ^ 2 * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : 0 ≤ 1 / ((ρ : ℂ).im) ^ 2 := by positivity
          nlinarith

/-- The other deep points `deepPts δ_D H ∖ {w_σ, w̄_σ}`. -/
def others (δD H : ℝ) (σ : nonTrivialZeroSet) : Finset ℂ :=
  ((deepPts δD H).erase (wR σ)).erase (conj (wR σ))

/-- **The uniform Blaschke bound at `w_σ`**: `|B_{others}(w_σ)| ≥ e^{−K_σ/2}` for every `δ_D > 0` and `H`. -/
theorem exp_le_norm_bS_others (σ : nonTrivialZeroSet) {δD : ℝ} (hδ : 0 < δD) (H : ℝ) :
    Real.exp (-(kS σ / 2)) ≤ ‖bS (others δD H σ) (wR σ)‖ := by
  set w := wR σ with hwdef
  set S := others δD H σ with hSdef
  have hwre : w.re = |Cvs.GaussKernel.del σ| := Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re σ
  have hwlt : w.re < 1 / 2 := by rw [hwre]; exact Cvs.StepA.Edge.TransplantAngleHighZeros.abs_del_lt_half σ
  have hw0 : 0 ≤ w.re := by rw [hwre]; exact abs_nonneg _
  have hmemS : ∀ ζ ∈ S, ζ ∈ deepPts δD H ∧ ζ ≠ w ∧ ζ ≠ conj w := by
    intro ζ hζ
    simp only [hSdef, others, Finset.mem_erase] at hζ
    exact ⟨hζ.2.2, hζ.2.1, hζ.1⟩
  have hfac : ∀ ζ ∈ S, Real.exp (-(1 / 2 * (1 / ‖w - ζ‖ ^ 2))) ≤ ‖Cvs.Upstream.ExpSumBlaschkeProduct.bfac ζ w‖ := by
    intro ζ hζ
    obtain ⟨hζD, hne1, _⟩ := hmemS ζ hζ
    obtain ⟨_, _, _, h1, h2, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζD
    have hζ0 : 0 < ζ.re := by linarith
    refine le_trans ?_ (Cvs.StepA.Edge.DeepPointBlaschkeCount.exp_le_norm_bfac hζ0 hw0 (Ne.symm hne1))
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hn : 0 < ‖w - ζ‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne1))) 2
    rw [div_le_iff₀ hn]
    have : 1 / 2 * (1 / ‖w - ζ‖ ^ 2) * ‖w - ζ‖ ^ 2 = 1 / 2 := by
      rw [mul_assoc, one_div_mul_cancel hn.ne', mul_one]
    rw [this]; nlinarith
  have hprod : Real.exp (-(1 / 2 * ∑ ζ ∈ S, 1 / ‖w - ζ‖ ^ 2)) ≤ ‖bS S w‖ := by
    rw [Cvs.Upstream.PointInterpolationHardyDatum.bS, norm_prod, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun ζ _ => (Real.exp_pos _).le) hfac
  refine le_trans (Real.exp_le_exp.2 (neg_le_neg ?_)) hprod
  set F := (deepSet δD H).filter fun ρ => wR ρ ≠ w ∧ wR ρ ≠ conj w with hF
  have hsub : S ⊆ F.image wR := by
    intro ζ hζ
    obtain ⟨hζD, hne1, hne2⟩ := hmemS ζ hζ
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hζD
    exact Finset.mem_image.2 ⟨ρ, Finset.mem_filter.2 ⟨hρ, hne1, hne2⟩, rfl⟩
  have h1 : ∑ ζ ∈ S, 1 / ‖w - ζ‖ ^ 2 ≤ ∑ ρ ∈ F, 1 / ‖w - wR ρ‖ ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (Finset.sum_image_le_of_nonneg fun _ _ => by positivity)
  have h2 : ∑ ρ ∈ F, 1 / ‖w - wR ρ‖ ^ 2
      ≤ ∑ ρ ∈ F, ((if ρ ∈ nearSet σ then 1 / dS σ else 0)
        + (|(σ : ℂ).im| + 1) ^ 2 * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2))) :=
    Finset.sum_le_sum fun ρ hρ => by
      have := (Finset.mem_filter.1 hρ).2
      exact inv_norm_sq_le σ ρ this.1 this.2
  have h3 : ∑ ρ ∈ F, (if ρ ∈ nearSet σ then 1 / dS σ else 0) ≤ (nearSet σ).card / dS σ := by
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    refine div_le_div_of_nonneg_right ?_ (dS_pos σ).le
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have h4 : ∑ ρ ∈ F, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) ≤ Cvs.StepA.Edge.DeepSetZeroSums.invSqSum :=
    Summable.sum_le_tsum _ (fun ρ _ => mul_nonneg (mult_nonneg ρ) (by positivity))
      Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
  have h5 : (|(σ : ℂ).im| + 1) ^ 2 * ∑ ρ ∈ F, mult ρ * (1 / ((ρ : ℂ).im) ^ 2)
      ≤ (|(σ : ℂ).im| + 1) ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := mul_le_mul_of_nonneg_left h4 (by positivity)
  unfold kS
  linarith

end Cvs.StepA.Edge.OtherDeepPointsBlaschke

end
