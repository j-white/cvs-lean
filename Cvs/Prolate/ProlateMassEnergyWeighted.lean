import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate's mass from below with its local energy as the weight

For a solution of the prolate equation on `[ξ₀, ξ₁]`, `1 < ξ₀`, with energy at most `G_M`,
`∫_{ξ₀}^{ξ₁} ψ² ≥ ∫_{ξ₀}^{ξ₁} E(t)/(2a(t)) dt − G_M/(2q(ξ₀))`: the identity of Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy with the cross term and the edge
terms bounded by the energy, the energy under the integral kept as it is.
-/

namespace Cvs.Prolate.ProlateMassEnergyWeighted

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- **The energy-weighted mass law**: `∫_{ξ₀}^{ξ₁} E/(2a) − G_M/(2q(ξ₀)) ≤ ∫_{ξ₀}^{ξ₁} ψ²`. -/
theorem mass_ge_weighted {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ GM : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hGM : ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u t ≤ GM) :
    (∫ t in ξ₀..ξ₁, energy (aP c χ) ψ u t / (2 * aP c χ t)) - GM / (2 * qP c χ ξ₀) ≤ ∫ t in ξ₀..ξ₁, ψ t ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hI : uIcc ξ₀ ξ₁ = Icc ξ₀ ξ₁ := uIcc_of_le hle
  have hmem0 : ξ₀ ∈ Icc ξ₀ ξ₁ := left_mem_Icc.mpr hle
  have hmem1 : ξ₁ ∈ Icc ξ₀ ξ₁ := right_mem_Icc.mpr hle
  have hq : ∀ t ∈ Icc ξ₀ ξ₁, 0 < qP c χ t := fun t ht => qP_pos (gt1 t ht) hc2 hχc
  have ha : ∀ t ∈ Icc ξ₀ ξ₁, 0 < aP c χ t := fun t ht => aP_pos (gt1 t ht) hc2 hχc
  have hqd : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := fun t _ => by
    have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
    exact h.congr_deriv (by ring)
  have cont : ∀ f : ℝ → ℝ, (∀ t ∈ Icc ξ₀ ξ₁, DifferentiableAt ℝ f t) → ContinuousOn f (Icc ξ₀ ξ₁) :=
    fun f hf t ht => (hf t ht).continuousAt.continuousWithinAt
  have hac : ContinuousOn (aP c χ) (Icc ξ₀ ξ₁) :=
    cont _ fun t ht => (hasDerivAt_aP (gt1 t ht) hc2 hχc).differentiableAt
  have hpc : ContinuousOn pP (Icc ξ₀ ξ₁) := by unfold pP; fun_prop
  have hqc : ContinuousOn (qP c χ) (Icc ξ₀ ξ₁) := by unfold qP; fun_prop
  have hψc := cont ψ fun t ht => (hψ t ht).differentiableAt
  have huc := cont u fun t ht => (hu t ht).differentiableAt
  have hid := Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy.integral_sq_eq (q' := fun t => 2 * c ^ 2 * t) hle ha
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => (hq t ht).ne')
    (fun t ht => aP_sq (gt1 t ht) hc2 hχc) hψ hu hqd (by fun_prop) hac hpc
  have hqq' : ContinuousOn (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) (Icc ξ₀ ξ₁) :=
    ContinuousOn.div (f := fun t => 2 * c ^ 2 * t) (g := fun t => qP c χ t ^ 2) (by fun_prop) (hqc.pow 2)
      fun t ht => (pow_pos (hq t ht) 2).ne'
  -- ∫ q'/q² = 1/q₀ − 1/q₁
  have hqq : ∫ t in ξ₀..ξ₁, 2 * c ^ 2 * t / qP c χ t ^ 2 = 1 / qP c χ ξ₀ - 1 / qP c χ ξ₁ := by
    have hd : ∀ t ∈ uIcc ξ₀ ξ₁, HasDerivAt (fun s => -(1 / qP c χ s))
        (2 * c ^ 2 * t / qP c χ t ^ 2) t := fun t ht => by
      have := ((hqd t (hI ▸ ht)).inv (hq t (hI ▸ ht)).ne').neg
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with s; simp [one_div]
    rw [integral_eq_sub_of_hasDerivAt hd]
    · ring
    · exact ContinuousOn.intervalIntegrable_of_Icc hle hqq'
  have hEc : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)) (Icc ξ₀ ξ₁) := by
    unfold energy
    exact ((hac.mul (hψc.pow 2)).add ((huc.pow 2).div hac fun t ht => (ha t ht).ne')).div
      (g := fun t => 2 * aP c χ t) (continuousOn_const.mul hac) fun t ht => (mul_pos two_pos (ha t ht)).ne'
  have hint1 : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) (Icc ξ₀ ξ₁) := by
    refine ContinuousOn.sub (f := fun t => energy (aP c χ) ψ u t / (2 * aP c χ t))
      (g := fun t => ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) hEc ?_
    have h2 : ContinuousOn (fun t : ℝ => 2 * c ^ 2 * t) (Icc ξ₀ ξ₁) := by fun_prop
    have hn : ContinuousOn (fun t => ψ t * u t * (2 * c ^ 2 * t)) (Icc ξ₀ ξ₁) :=
      (hψc.mul huc).mul h2
    have hd : ContinuousOn (fun t => 2 * qP c χ t ^ 2) (Icc ξ₀ ξ₁) :=
      continuousOn_const.mul (hqc.pow 2)
    exact hn.div hd fun t ht => (mul_pos two_pos (pow_pos (hq t ht) 2)).ne'
  have hcross : ∀ t ∈ Icc ξ₀ ξ₁, |ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)|
      ≤ GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) := fun t ht => by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht)
    have hqt := hq t ht
    have ht0 : 0 ≤ 2 * c ^ 2 * t := by have := gt1 t ht; positivity
    rw [abs_div, abs_mul, abs_of_nonneg ht0, abs_of_pos (by positivity : 0 < 2 * qP c χ t ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    have : |ψ t * u t| ≤ GM / 2 := by linarith [hGM t ht]
    have e : GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) * (2 * qP c χ t ^ 2) = GM / 2 * (2 * c ^ 2 * t) := by
      field_simp; ring
    rw [e]; exact mul_le_mul_of_nonneg_right this ht0
  have hmainL : ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u t / (2 * aP c χ t)
      - GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2)
      ≤ energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2) := by
    intro t ht
    have := le_abs_self (ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2))
    linarith [hcross t ht]
  have iE : IntervalIntegrable (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)) MeasureTheory.volume ξ₀ ξ₁ :=
    hEc.intervalIntegrable_of_Icc hle
  have iQ : IntervalIntegrable (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) MeasureTheory.volume ξ₀ ξ₁ :=
    hqq'.intervalIntegrable_of_Icc hle
  have iH : IntervalIntegrable (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) MeasureTheory.volume ξ₀ ξ₁ :=
    hint1.intervalIntegrable_of_Icc hle
  have iL := integral_mono_on hle (iE.sub (iQ.const_mul (GM / 4))) iH hmainL
  rw [intervalIntegral.integral_sub iE (iQ.const_mul _), intervalIntegral.integral_const_mul, hqq] at iL
  -- the edge terms
  have e0 : |ψ ξ₀ * u ξ₀ / qP c χ ξ₀ / 2| ≤ GM / (4 * qP c χ ξ₀) := by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha ξ₀ hmem0)
    have hq0 := hq ξ₀ hmem0
    rw [abs_div, abs_div, abs_of_pos hq0, abs_two, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hGM ξ₀ hmem0]
  have e1 : |ψ ξ₁ * u ξ₁ / qP c χ ξ₁ / 2| ≤ GM / (4 * qP c χ ξ₁) := by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha ξ₁ hmem1)
    have hq1 := hq ξ₁ hmem1
    rw [abs_div, abs_div, abs_of_pos hq1, abs_two, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hGM ξ₁ hmem1]
  have hq0 := hq ξ₀ hmem0
  have hq1 := hq ξ₁ hmem1
  have hsum : GM / 4 * (1 / qP c χ ξ₀ - 1 / qP c χ ξ₁) + GM / (4 * qP c χ ξ₁) + GM / (4 * qP c χ ξ₀)
      = GM / (2 * qP c χ ξ₀) := by field_simp; ring
  have a0' := neg_abs_le (ψ ξ₀ * u ξ₀ / qP c χ ξ₀ / 2)
  have a1 := le_abs_self (ψ ξ₁ * u ξ₁ / qP c χ ξ₁ / 2)
  rw [hid]
  linarith [iL, e0, e1, hsum]

end Cvs.Prolate.ProlateMassEnergyWeighted
