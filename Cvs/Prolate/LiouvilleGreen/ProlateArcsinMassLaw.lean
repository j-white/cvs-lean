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
# The arcsin law for the prolate's L² mass outside `[−1, 1]`

For a solution of the prolate equation on `[ξ₀, ξ₁]`, `1 < ξ₀`, whose energy lies in `[G_m, G_M]`, with
`Δ = arccos(1/ξ₁) − arccos(1/ξ₀)` (which tends to `arcsin(1/ξ₀)` as `ξ₁ → ∞`),
`G_m Δ/(2c) − G_M/(2q(ξ₀)) ≤ ∫_{ξ₀}^{ξ₁} ψ² ≤ G_M Δ/(2√(c²−χ)) + G_M/(2q(ξ₀))`.
-/

namespace Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `d/dξ arccos(1/ξ) = 1/(ξ√(ξ²−1))` for `ξ > 1`. -/
theorem hasDerivAt_arcsec {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (fun s => arccos (1 / s)) (1 / (ξ * √(ξ ^ 2 - 1))) ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hinv : HasDerivAt (fun s : ℝ => 1 / s) (-(1 / ξ ^ 2)) ξ := by
    have := (hasDerivAt_inv hξ0.ne')
    simpa [one_div] using this
  have h1 : 1 / ξ ≠ -1 := by
    have : 0 < 1 / ξ := by positivity
    linarith
  have h2 : 1 / ξ ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hξ0.ne'] at h; linarith
  have := (hasDerivAt_arccos h1 h2).comp ξ hinv
  refine this.congr_deriv ?_
  have hB : 0 < ξ ^ 2 - 1 := by nlinarith
  have hs : √(1 - (1 / ξ) ^ 2) = √(ξ ^ 2 - 1) / ξ := by
    rw [show 1 - (1 / ξ) ^ 2 = (ξ ^ 2 - 1) / ξ ^ 2 by field_simp, sqrt_div hB.le, sqrt_sq hξ0.le]
  rw [hs]
  have := sqrt_pos.mpr hB
  field_simp

section
variable {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
include hξ hc hχ hχc

omit hξ hc hχ in
theorem sub_pos' : 0 < c ^ 2 - χ := by linarith

/-- `1/(cξ√(ξ²−1)) ≤ 1/a`. -/
theorem inv_a_ge : 1 / (c * (ξ * √(ξ ^ 2 - 1))) ≤ 1 / aP c χ ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχc
  have hB : 0 < ξ ^ 2 - 1 := by nlinarith
  apply one_div_le_one_div_of_le ha
  unfold aP pP qP
  rw [sqrt_mul hB.le]
  have hq : √(c ^ 2 * ξ ^ 2 - χ) ≤ c * ξ := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  have := sqrt_nonneg (ξ ^ 2 - 1)
  nlinarith

/-- `1/a ≤ 1/(√(c²−χ) ξ√(ξ²−1))`. -/
theorem inv_a_le : 1 / aP c χ ξ ≤ 1 / (√(c ^ 2 - χ) * (ξ * √(ξ ^ 2 - 1))) := by
  have hB : 0 < ξ ^ 2 - 1 := by nlinarith
  have hd := sub_pos' hχc
  have hξ0 : 0 < ξ := by linarith
  apply one_div_le_one_div_of_le (by positivity)
  unfold aP pP qP
  rw [sqrt_mul hB.le]
  have hq : √(c ^ 2 - χ) * ξ ≤ √(c ^ 2 * ξ ^ 2 - χ) := by
    rw [show √(c ^ 2 - χ) * ξ = √((c ^ 2 - χ) * ξ ^ 2) by
      rw [sqrt_mul hd.le, sqrt_sq hξ0.le]]
    apply sqrt_le_sqrt; nlinarith
  have := sqrt_nonneg (ξ ^ 2 - 1)
  nlinarith

end

/-- **The arcsin law, two-sided.** For a prolate solution on `[ξ₀, ξ₁]` with energy in `[G_m, G_M]`,
`G_m Δ/(2c) − G_M/(2q(ξ₀)) ≤ ∫ψ² ≤ G_M Δ/(2√(c²−χ)) + G_M/(2q(ξ₀))`, `Δ = arccos(1/ξ₁) − arccos(1/ξ₀)`. -/
theorem prolate_mass_bounds {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ Gm GM : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hGm : ∀ t ∈ Icc ξ₀ ξ₁, Gm ≤ energy (aP c χ) ψ u t)
    (hGM : ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u t ≤ GM) (hGm0 : 0 ≤ Gm) :
    Gm * (arccos (1 / ξ₁) - arccos (1 / ξ₀)) / (2 * c) - GM / (2 * qP c χ ξ₀)
        ≤ ∫ t in ξ₀..ξ₁, ψ t ^ 2 ∧
      ∫ t in ξ₀..ξ₁, ψ t ^ 2
        ≤ GM * (arccos (1 / ξ₁) - arccos (1 / ξ₀)) / (2 * √(c ^ 2 - χ)) + GM / (2 * qP c χ ξ₀) := by
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
  -- the arcsec integral
  set Δ := arccos (1 / ξ₁) - arccos (1 / ξ₀)
  have hsec : ContinuousOn (fun t => 1 / (t * √(t ^ 2 - 1))) (Icc ξ₀ ξ₁) := by
    have hden : ContinuousOn (fun t : ℝ => t * √(t ^ 2 - 1)) (Icc ξ₀ ξ₁) := by fun_prop
    refine (continuousOn_const (c := (1 : ℝ))).div hden fun t ht => ?_
    have h1t := gt1 t ht; have h2 : 0 < t ^ 2 - 1 := by nlinarith
    exact (mul_pos (by linarith) (sqrt_pos.mpr h2)).ne'
  have hΔ : ∫ t in ξ₀..ξ₁, 1 / (t * √(t ^ 2 - 1)) = Δ :=
    integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_arcsec (gt1 t (hI ▸ ht)))
      (hsec.intervalIntegrable_of_Icc hle)
  have h2c : ContinuousOn (fun t : ℝ => 2 * c ^ 2 * t) (Icc ξ₀ ξ₁) := by fun_prop
  have hq2 : ContinuousOn (fun t => qP c χ t ^ 2) (Icc ξ₀ ξ₁) := hqc.pow 2
  have hqq' : ContinuousOn (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) (Icc ξ₀ ξ₁) :=
    h2c.div hq2 fun t ht => (pow_pos (hq t ht) 2).ne'
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
  -- pointwise bounds on the integrand of the identity
  have hint1 : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) (Icc ξ₀ ξ₁) := by
    have hE : ContinuousOn (fun t => energy (aP c χ) ψ u t) (Icc ξ₀ ξ₁) := by
      unfold energy
      exact (hac.mul (hψc.pow 2)).add ((huc.pow 2).div hac fun t ht => (ha t ht).ne')
    have h2a : ContinuousOn (fun t => 2 * aP c χ t) (Icc ξ₀ ξ₁) := continuousOn_const.mul hac
    have hL : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)) (Icc ξ₀ ξ₁) :=
      hE.div h2a fun t ht => (mul_pos two_pos (ha t ht)).ne'
    have hn : ContinuousOn (fun t => ψ t * u t * (2 * c ^ 2 * t)) (Icc ξ₀ ξ₁) :=
      (hψc.mul huc).mul h2c
    have hd : ContinuousOn (fun t => 2 * qP c χ t ^ 2) (Icc ξ₀ ξ₁) := continuousOn_const.mul hq2
    exact hL.sub (hn.div hd fun t ht => (mul_pos two_pos (pow_pos (hq t ht) 2)).ne')
  have hainv : ContinuousOn (fun t => 1 / aP c χ t) (Icc ξ₀ ξ₁) :=
    continuousOn_const.div hac fun t ht => (ha t ht).ne'
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
  have hmainU : ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)
      ≤ GM / (2 * √(c ^ 2 - χ)) * (1 / (t * √(t ^ 2 - 1))) + GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) := by
    intro t ht
    have hat := ha t ht
    have hle' := inv_a_le (gt1 t ht) hc hχ hχc
    have h1' : energy (aP c χ) ψ u t / (2 * aP c χ t) ≤ GM / 2 * (1 / aP c χ t) := by
      have e : energy (aP c χ) ψ u t / (2 * aP c χ t) = energy (aP c χ) ψ u t / 2 * (1 / aP c χ t) := by
        field_simp
      rw [e]; exact mul_le_mul_of_nonneg_right (by linarith [hGM t ht]) (by positivity)
    have h2' : GM / 2 * (1 / aP c χ t) ≤ GM / (2 * √(c ^ 2 - χ)) * (1 / (t * √(t ^ 2 - 1))) := by
      have hGM0 : 0 ≤ GM := le_trans hGm0 (le_trans (hGm t ht) (hGM t ht))
      calc GM / 2 * (1 / aP c χ t) ≤ GM / 2 * (1 / (√(c ^ 2 - χ) * (t * √(t ^ 2 - 1)))) :=
            mul_le_mul_of_nonneg_left hle' (by positivity)
        _ = _ := by ring
    have := neg_abs_le (ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2))
    linarith [hcross t ht]
  have hmainL : ∀ t ∈ Icc ξ₀ ξ₁, Gm / (2 * c) * (1 / (t * √(t ^ 2 - 1)))
      - GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2)
      ≤ energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2) := by
    intro t ht
    have hat := ha t ht
    have hge' := inv_a_ge (gt1 t ht) hc hχ hχc
    have h1' : Gm / 2 * (1 / aP c χ t) ≤ energy (aP c χ) ψ u t / (2 * aP c χ t) := by
      have e : energy (aP c χ) ψ u t / (2 * aP c χ t) = energy (aP c χ) ψ u t / 2 * (1 / aP c χ t) := by
        field_simp
      rw [e]; exact mul_le_mul_of_nonneg_right (by linarith [hGm t ht]) (by positivity)
    have h2' : Gm / (2 * c) * (1 / (t * √(t ^ 2 - 1))) ≤ Gm / 2 * (1 / aP c χ t) := by
      calc Gm / (2 * c) * (1 / (t * √(t ^ 2 - 1)))
          = Gm / 2 * (1 / (c * (t * √(t ^ 2 - 1)))) := by field_simp
        _ ≤ Gm / 2 * (1 / aP c χ t) := mul_le_mul_of_nonneg_left hge' (by positivity)
    have := le_abs_self (ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2))
    linarith [hcross t ht]
  have iS : IntervalIntegrable (fun t => 1 / (t * √(t ^ 2 - 1))) MeasureTheory.volume ξ₀ ξ₁ :=
    hsec.intervalIntegrable_of_Icc hle
  have iQ : IntervalIntegrable (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) MeasureTheory.volume ξ₀ ξ₁ :=
    hqq'.intervalIntegrable_of_Icc hle
  have iH : IntervalIntegrable (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) MeasureTheory.volume ξ₀ ξ₁ :=
    hint1.intervalIntegrable_of_Icc hle
  have iU := integral_mono_on hle iH
    ((iS.const_mul (GM / (2 * √(c ^ 2 - χ)))).add (iQ.const_mul (GM / 4))) hmainU
  have iL := integral_mono_on hle ((iS.const_mul (Gm / (2 * c))).sub (iQ.const_mul (GM / 4))) iH hmainL
  rw [intervalIntegral.integral_add (iS.const_mul _) (iQ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hΔ, hqq] at iU
  rw [intervalIntegral.integral_sub (iS.const_mul _) (iQ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hΔ, hqq] at iL
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
  have hGM0 : 0 ≤ GM := le_trans hGm0 (le_trans (hGm ξ₀ hmem0) (hGM ξ₀ hmem0))
  have hsum : GM / 4 * (1 / qP c χ ξ₀ - 1 / qP c χ ξ₁) + GM / (4 * qP c χ ξ₁) + GM / (4 * qP c χ ξ₀)
      = GM / (2 * qP c χ ξ₀) := by field_simp; ring
  have a0 := le_abs_self (ψ ξ₀ * u ξ₀ / qP c χ ξ₀ / 2)
  have a0' := neg_abs_le (ψ ξ₀ * u ξ₀ / qP c χ ξ₀ / 2)
  have a1 := le_abs_self (ψ ξ₁ * u ξ₁ / qP c χ ξ₁ / 2)
  have a1' := neg_abs_le (ψ ξ₁ * u ξ₁ / qP c χ ξ₁ / 2)
  have hdivs : ∀ t, ψ t * u t / qP c χ t / 2 = ψ t * u t / qP c χ t / 2 := fun _ => rfl
  constructor
  · rw [hid]
    have : Gm * Δ / (2 * c) = Gm / (2 * c) * Δ := by ring
    rw [this]
    nlinarith [iL, e0, e1, hsum]
  · rw [hid]
    have : GM * Δ / (2 * √(c ^ 2 - χ)) = GM / (2 * √(c ^ 2 - χ)) * Δ := by ring
    rw [this]
    nlinarith [iU, e0, e1, hsum]

end Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
