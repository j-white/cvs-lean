import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One integration by parts against a non-stationary phase

If `|Φ'| ≥ κ > 0`, `|Φ''| ≤ D`, `|g| ≤ G₀` and `|g'| ≤ G₁` on `[α, β]`, then
`|∫_α^β g e^{iΦ}| ≤ 2G₀/κ + (β − α)(G₁/κ + G₀D/κ²)`, from `e^{iΦ} = (e^{iΦ})'/(iΦ')`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral
open Complex (I)
open scoped Interval

namespace Cvs.Upstream.NonStationaryPhaseParts

/-- **The non-stationary phase bound** `|∫_α^β g e^{iΦ}| ≤ 2G₀/κ + (β − α)(G₁/κ + G₀D/κ²)`. -/
theorem norm_integral_mul_exp_le {α β κ G₀ G₁ D : ℝ} (hαβ : α ≤ β) (hκ : 0 < κ)
    {g g' : ℝ → ℂ} {Φ Φ₁ Φ₂ : ℝ → ℝ}
    (hg : ∀ x ∈ Icc α β, HasDerivAt g (g' x) x) (hg' : ContinuousOn g' (Icc α β))
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (Φ₁ x) x) (hΦ₁ : ∀ x ∈ Icc α β, HasDerivAt Φ₁ (Φ₂ x) x)
    (hΦ₂ : ContinuousOn Φ₂ (Icc α β))
    (hG₀ : ∀ x ∈ Icc α β, ‖g x‖ ≤ G₀) (hG₁ : ∀ x ∈ Icc α β, ‖g' x‖ ≤ G₁)
    (hκx : ∀ x ∈ Icc α β, κ ≤ |Φ₁ x|) (hD : ∀ x ∈ Icc α β, |Φ₂ x| ≤ D) :
    ‖∫ x in α..β, g x * Complex.exp (I * Φ x)‖ ≤ 2 * G₀ / κ + (β - α) * (G₁ / κ + G₀ * D / κ ^ 2) := by
  have hu := uIcc_of_le hαβ
  have hne : ∀ x ∈ Icc α β, I * (Φ₁ x : ℂ) ≠ 0 := fun x hx => by
    refine mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 fun h => ?_)
    have := hκx x hx; rw [h, abs_zero] at this; linarith
  set U : ℝ → ℂ := fun x => g x / (I * Φ₁ x) with hUdef
  set U' : ℝ → ℂ := fun x => (g' x * (I * Φ₁ x) - g x * (I * Φ₂ x)) / (I * Φ₁ x) ^ 2 with hU'def
  set V : ℝ → ℂ := fun x => Complex.exp (I * Φ x) with hVdef
  set V' : ℝ → ℂ := fun x => Complex.exp (I * Φ x) * (I * Φ₁ x) with hV'def
  have hUd : ∀ x ∈ [[α, β]], HasDerivAt U (U' x) x := by
    intro x hx
    rw [hu] at hx
    have h1 : HasDerivAt (fun x : ℝ => I * (Φ₁ x : ℂ)) (I * (Φ₂ x : ℂ)) x :=
      ((hΦ₁ x hx).ofReal_comp).const_mul I
    exact (hg x hx).div h1 (hne x hx)
  have hVd : ∀ x ∈ [[α, β]], HasDerivAt V (V' x) x := by
    intro x hx
    rw [hu] at hx
    have h1 : HasDerivAt (fun x : ℝ => I * (Φ x : ℂ)) (I * (Φ₁ x : ℂ)) x :=
      ((hΦ x hx).ofReal_comp).const_mul I
    exact h1.cexp
  have hgc : ContinuousOn g (Icc α β) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hΦc : ContinuousOn Φ (Icc α β) := fun x hx => (hΦ x hx).continuousAt.continuousWithinAt
  have hΦ₁c : ContinuousOn Φ₁ (Icc α β) := fun x hx => (hΦ₁ x hx).continuousAt.continuousWithinAt
  have hU'i : IntervalIntegrable U' volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hu]
    refine ContinuousOn.div₀ ?_ ?_ fun x hx => pow_ne_zero 2 (hne x hx)
    · refine (hg'.mul (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦ₁c))).sub
        (hgc.mul (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦ₂)))
    · exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦ₁c)).pow 2
  have hV'i : IntervalIntegrable V' volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hu]
    refine ContinuousOn.mul ?_ (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦ₁c))
    exact Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hΦc))
  have hibp := integral_mul_deriv_eq_deriv_mul hUd hVd hU'i hV'i
  have hlhs : ∫ x in α..β, U x * V' x = ∫ x in α..β, g x * Complex.exp (I * Φ x) := by
    refine integral_congr fun x hx => ?_
    rw [hu] at hx
    simp only [hUdef, hV'def]
    have h1 : (Φ₁ x : ℂ) ≠ 0 := right_ne_zero_of_mul (hne x hx)
    field_simp
  rw [← hlhs, hibp]
  have hUb : ∀ x ∈ Icc α β, ‖U x‖ ≤ G₀ / κ := by
    intro x hx
    simp only [hUdef]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div₀ ((norm_nonneg _).trans (hG₀ x hx)) (hG₀ x hx) hκ (hκx x hx)
  have hVb : ∀ x, ‖V x‖ = 1 := fun x => by
    simp only [hVdef]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hU'b : ∀ x ∈ Icc α β, ‖U' x * V x‖ ≤ G₁ / κ + G₀ * D / κ ^ 2 := by
    intro x hx
    rw [norm_mul, hVb, mul_one]
    simp only [hU'def]
    have hk := hκx x hx
    have hk0 : 0 < |Φ₁ x| := by linarith
    have e : (g' x * (I * Φ₁ x) - g x * (I * Φ₂ x)) / (I * Φ₁ x) ^ 2 =
        g' x / (I * Φ₁ x) - g x * (Φ₂ x : ℂ) / (I * (Φ₁ x : ℂ) ^ 2) := by
      have := hne x hx
      have h1 : (Φ₁ x : ℂ) ≠ 0 := right_ne_zero_of_mul this
      field_simp
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div₀ ((norm_nonneg _).trans (hG₁ x hx)) (hG₁ x hx) hκ hk
    · rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x hx)
      have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans (hG₀ x hx)
      exact div_le_div₀ (mul_nonneg hG0 hD0) (mul_le_mul (hG₀ x hx) (hD x hx) (abs_nonneg _) hG0)
        (pow_pos hκ 2) (pow_le_pow_left₀ hκ.le hk 2)
  have hint : ‖∫ x in α..β, U' x * V x‖ ≤ (G₁ / κ + G₀ * D / κ ^ 2) * |β - α| :=
    norm_integral_le_of_norm_le_const fun x hx => hU'b x (by
      rw [uIoc_of_le hαβ] at hx; exact Ioc_subset_Icc_self hx)
  rw [abs_of_nonneg (by linarith)] at hint
  have hb1 := hUb β ⟨hαβ, le_rfl⟩
  have hb2 := hUb α ⟨le_rfl, hαβ⟩
  calc ‖U β * V β - U α * V α - ∫ x in α..β, U' x * V x‖
      ≤ ‖U β * V β‖ + ‖U α * V α‖ + ‖∫ x in α..β, U' x * V x‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ G₀ / κ + G₀ / κ + (G₁ / κ + G₀ * D / κ ^ 2) * (β - α) := by
        rw [norm_mul, norm_mul, hVb, hVb, mul_one, mul_one]
        linarith
    _ = 2 * G₀ / κ + (β - α) * (G₁ / κ + G₀ * D / κ ^ 2) := by ring

end Cvs.Upstream.NonStationaryPhaseParts

end
