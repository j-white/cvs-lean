import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate equation outside `[−1, 1]`: its energy is constant up to `w(ξ₀)`

For `((ξ²−1)ψ')' + (c²ξ² − χ)ψ = 0` on `ξ > 1` with `0 ≤ χ`, `χ < c²`, the Liouville–Green rate
`w = (pq)'/(2q√(pq))` is positive and decreasing (its derivative has the sign of
`−P`, `P = (c²−χ)² + 2c²y(c²−χ) + c²y²(3c²+χ) + 2c⁴y³ ≥ 0`, `y = ξ² − 1`), so the energy satisfies
`G ξ₁ ≤ G ξ₀ (1 + W/2)/(1 − W/2) exp(W/(2 − W))`, `W = w ξ₀ < 2`, for every solution.
-/

namespace Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

variable (c χ : ℝ)

/-- `p = ξ² − 1`. -/
def pP (ξ : ℝ) : ℝ := ξ ^ 2 - 1
/-- `q = c²ξ² − χ`. -/
def qP (ξ : ℝ) : ℝ := c ^ 2 * ξ ^ 2 - χ
/-- `(pq)' = 2ξ(2c²ξ² − c² − χ)`. -/
def dP (ξ : ℝ) : ℝ := 2 * ξ * (2 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ)
/-- `a = √(pq)`. -/
noncomputable def aP (ξ : ℝ) : ℝ := √(pP ξ * qP c χ ξ)
/-- The Liouville–Green rate `w = (pq)'/(2qa)`. -/
noncomputable def wP (ξ : ℝ) : ℝ := dP c χ ξ / (2 * qP c χ ξ * aP c χ ξ)
/-- Its derivative, by the quotient rule with `a' = w q`. -/
noncomputable def wP' (ξ : ℝ) : ℝ :=
  (2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) * (2 * qP c χ ξ * aP c χ ξ)
    - dP c χ ξ * (2 * (2 * c ^ 2 * ξ * aP c χ ξ + qP c χ ξ * (wP c χ ξ * qP c χ ξ))))
    / (2 * qP c χ ξ * aP c χ ξ) ^ 2

variable {c χ}

/-- **The sign polynomial is nonnegative**: with `y = X − 1`, it equals
`(c²−χ)² + 2c²y(c²−χ) + c²y²(3c²+χ) + 2c⁴y³`. -/
theorem signPoly_nonneg {X : ℝ} (hX : 1 ≤ X) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) :
    0 ≤ c ^ 4 * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X) + c ^ 2 * χ * (X ^ 2 - 4 * X + 1) + χ ^ 2 := by
  have e : c ^ 4 * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X) + c ^ 2 * χ * (X ^ 2 - 4 * X + 1) + χ ^ 2
      = (c ^ 2 - χ) ^ 2 + 2 * c ^ 2 * (X - 1) * (c ^ 2 - χ) + c ^ 2 * (X - 1) ^ 2 * (3 * c ^ 2 + χ)
        + 2 * c ^ 4 * (X - 1) ^ 3 := by ring
  rw [e]
  have hy : 0 ≤ X - 1 := by linarith
  have hd : 0 ≤ c ^ 2 - χ := by linarith
  have h1 : 0 ≤ 2 * c ^ 2 * (X - 1) * (c ^ 2 - χ) := by positivity
  have h2 : 0 ≤ c ^ 2 * (X - 1) ^ 2 * (3 * c ^ 2 + χ) := by positivity
  have h3 : 0 ≤ 2 * c ^ 4 * (X - 1) ^ 3 := by positivity
  nlinarith [sq_nonneg (c ^ 2 - χ)]

section pos
variable {ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
include hξ hc hχ hχc

omit hc hχ hχc in
theorem pP_pos : 0 < pP ξ := by unfold pP; nlinarith
omit hχ in
theorem qP_pos : 0 < qP c χ ξ := by
  have h1 : 0 < c ^ 2 * (ξ ^ 2 - 1) := mul_pos hc (by nlinarith)
  unfold qP; nlinarith
omit hχ in
theorem aP_pos : 0 < aP c χ ξ :=
  sqrt_pos.mpr (mul_pos (pP_pos hξ) (qP_pos hξ hc hχc))
omit hχ in
theorem dP_pos : 0 < dP c χ ξ := by
  have h1 : 0 < c ^ 2 * (ξ ^ 2 - 1) := mul_pos hc (by nlinarith)
  have h2 : 0 < 2 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ := by nlinarith
  unfold dP; positivity
omit hχ in
theorem wP_pos : 0 < wP c χ ξ := by
  unfold wP
  have := aP_pos hξ hc hχc; have := qP_pos hξ hc hχc; have := dP_pos hξ hc hχc
  positivity
omit hχ in
theorem aP_sq : aP c χ ξ ^ 2 = pP ξ * qP c χ ξ :=
  sq_sqrt (mul_pos (pP_pos hξ) (qP_pos hξ hc hχc)).le

omit hχ in
/-- `a' = w q`. -/
theorem hasDerivAt_aP : HasDerivAt (aP c χ) (wP c χ ξ * qP c χ ξ) ξ := by
  have hf : HasDerivAt (fun s => pP s * qP c χ s) (dP c χ ξ) ξ := by
    have h := ((hasDerivAt_pow 2 ξ).sub_const 1).mul
      (((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ)
    refine h.congr_deriv ?_
    simp only [dP, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
  have hs := hf.sqrt (mul_pos (pP_pos hξ) (qP_pos hξ hc hχc)).ne'
  refine hs.congr_deriv ?_
  have ha := aP_pos hξ hc hχc
  have hq := qP_pos hξ hc hχc
  unfold wP
  rw [show √(pP ξ * qP c χ ξ) = aP c χ ξ from rfl]
  field_simp

omit hχ in
/-- `w'` is the derivative of `w`. -/
theorem hasDerivAt_wP : HasDerivAt (wP c χ) (wP' c χ ξ) ξ := by
  have hd : HasDerivAt (dP c χ) (2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ)) ξ := by
    have h := (((hasDerivAt_pow 3 ξ).const_mul (4 * c ^ 2)).sub
      ((hasDerivAt_id ξ).const_mul (2 * (c ^ 2 + χ))))
    have e : dP c χ = fun s => 4 * c ^ 2 * s ^ 3 - 2 * (c ^ 2 + χ) * id s := by
      funext s; unfold dP; simp; ring
    rw [e]; refine h.congr_deriv ?_; simp; ring
  have hq : HasDerivAt (qP c χ) (2 * c ^ 2 * ξ) ξ := by
    have h := ((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ
    have e : qP c χ = fun s => c ^ 2 * s ^ 2 - χ := rfl
    rw [e]; refine h.congr_deriv ?_; ring
  have hden := ((hq.const_mul 2).fun_mul (hasDerivAt_aP hξ hc hχc))
  have hne : 2 * qP c χ ξ * aP c χ ξ ≠ 0 := by
    have := aP_pos hξ hc hχc; have := qP_pos hξ hc hχc; positivity
  have h := hd.fun_div hden hne
  have e : wP c χ = fun s => dP c χ s / (2 * qP c χ s * aP c χ s) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold wP'
  ring

/-- **`w` decreases**: `w' ≤ 0`. -/
theorem wP'_nonpos : wP' c χ ξ ≤ 0 := by
  have ha := aP_pos hξ hc hχc
  have hq := qP_pos hξ hc hχc
  have hP := signPoly_nonneg (X := ξ ^ 2) (by nlinarith) hχ hχc
  have ha2 := aP_sq hξ hc hχc
  unfold wP' wP
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  -- numerator × a = q · (−4P) ≤ 0
  have key : (2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) * (2 * qP c χ ξ * aP c χ ξ)
      - dP c χ ξ * (2 * (2 * c ^ 2 * ξ * aP c χ ξ
        + qP c χ ξ * (dP c χ ξ / (2 * qP c χ ξ * aP c χ ξ) * qP c χ ξ)))) * aP c χ ξ
      = qP c χ ξ * (-4 * (c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2)
        + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1) + χ ^ 2)) := by
    field_simp
    rw [ha2]
    unfold pP qP dP
    ring
  have hrhs : qP c χ ξ * (-4 * (c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2)
        + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1) + χ ^ 2)) ≤ 0 := by nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_pos hcon ha
  linarith

omit hχ in
/-- `w'` is continuous at every `ξ > 1`. -/
theorem continuousAt_wP' : ContinuousAt (wP' c χ) ξ := by
  have ha := (hasDerivAt_aP hξ hc hχc).continuousAt
  have hw := (hasDerivAt_wP hξ hc hχc).continuousAt
  have hq : ContinuousAt (qP c χ) ξ := by unfold qP; fun_prop
  have hd : ContinuousAt (dP c χ) ξ := by unfold dP; fun_prop
  have hne : (2 * qP c χ ξ * aP c χ ξ) ^ 2 ≠ 0 := by
    have := aP_pos hξ hc hχc; have := qP_pos hξ hc hχc; positivity
  unfold wP'
  refine ContinuousAt.div ?_ ((continuousAt_const.mul hq).mul ha |>.pow 2) hne
  refine (((continuousAt_const.mul ((continuousAt_const.mul (continuousAt_id.pow 2)).sub
    continuousAt_const |>.sub continuousAt_const)).mul
    ((continuousAt_const.mul hq).mul ha))).sub ?_
  exact hd.mul (continuousAt_const.mul (((continuousAt_const.mul continuousAt_id).mul ha).add
    (hq.mul (hw.mul hq))))

end pos

/-- **The prolate energy bound.** For any solution of `ψ' = u/(ξ²−1)`, `u' = −(c²ξ²−χ)ψ` on
`[ξ₀, ξ₁]`, `1 < ξ₀`, with `0 < c²`, `0 ≤ χ`, `χ < c²` and `W = w ξ₀ < 2`,
`G ξ₁ ≤ G ξ₀ (1 + W/2)/(1 − W/2) exp(W/(2 − W))`. -/
theorem prolate_energy_le {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₁ ≤ energy (aP c χ) ψ u ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
      * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hw'c : ContinuousOn (wP' c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (continuousAt_wP' (gt1 t ht) hc hχc).continuousWithinAt
  have hwc : ContinuousOn (wP c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (hasDerivAt_wP (gt1 t ht) hc hχc).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (wP c χ) (Icc ξ₀ ξ₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ξ₀ ξ₁) hwc
    · rw [interior_Icc]; exact fun t ht =>
        (hasDerivAt_wP (gt1 t (Ioo_subset_Icc_self ht)) hc hχc).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hasDerivAt_wP (gt1 t (Ioo_subset_Icc_self ht)) hc hχc).deriv]
      exact wP'_nonpos (gt1 t (Ioo_subset_Icc_self ht)) hc hχ hχc
  have hmem0 : ξ₀ ∈ Icc ξ₀ ξ₁ := left_mem_Icc.mpr hle
  have hmem1 : ξ₁ ∈ Icc ξ₀ ξ₁ := right_mem_Icc.mpr hle
  have hWb : ∀ t ∈ Icc ξ₀ ξ₁, |wP c χ t| ≤ wP c χ ξ₀ := fun t ht => by
    rw [abs_of_pos (wP_pos (gt1 t ht) hc hχc)]; exact hanti hmem0 ht ht.1
  have hE := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth.energy_le_exp hle (fun t ht => aP_pos (gt1 t ht) hc hχc)
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => aP_sq (gt1 t ht) hc hχc) hψ hu
    (fun t ht => hasDerivAt_aP (gt1 t ht) hc hχc) (fun t ht => hasDerivAt_wP (gt1 t ht) hc hχc)
    hw'c hWb hW
  -- ∫ |w'| = w ξ₀ − w ξ₁ ≤ w ξ₀
  have hI : uIcc ξ₀ ξ₁ = Icc ξ₀ ξ₁ := uIcc_of_le hle
  have hint : ∫ t in ξ₀..ξ₁, |wP' c χ t| / (2 - wP c χ ξ₀)
      = (wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀) := by
    rw [intervalIntegral.integral_div]
    congr 1
    have hcongr : ∫ t in ξ₀..ξ₁, |wP' c χ t| = ∫ t in ξ₀..ξ₁, -wP' c χ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [hI] at ht
      exact abs_of_nonpos (wP'_nonpos (gt1 t ht) hc hχ hχc)
    rw [hcongr, intervalIntegral.integral_neg,
      integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_wP (gt1 t (hI ▸ ht)) hc hχc)
        (hw'c.intervalIntegrable_of_Icc hle)]
    ring
  rw [hint, abs_of_pos (wP_pos h1 hc hχc)] at hE
  have hW0 := wP_pos h1 hc hχc
  have hW1 := (wP_pos (gt1 ξ₁ hmem1) hc hχc).le
  have hd : 0 < 2 - wP c χ ξ₀ := by linarith
  have hexp : exp ((wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀))
      ≤ exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hd.le)
  have hG0 : 0 ≤ energy (aP c χ) ψ u ξ₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h1 hc hχc))
  have hpre : 0 ≤ energy (aP c χ) ψ u ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) := by
    apply div_nonneg (mul_nonneg hG0 (by linarith)); linarith
  exact hE.trans (mul_le_mul_of_nonneg_left hexp hpre)

end Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
