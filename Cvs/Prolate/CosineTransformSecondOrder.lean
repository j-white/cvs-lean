import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The finite cosine transform at infinity, to second order

For `g` twice differentiable on `[−1, 1]`, two integrations by parts give
`ψ(ξ) = ∫ g cos(cξs) = (g(1) + g(−1)) sin(cξ)/(cξ) + (g₁(1) − g₁(−1)) cos(cξ)/(cξ)² − (∫ g₂ cos(cξs))/(cξ)²`
and, with `h = sg`, `ψ'(ξ) = (g(1) + g(−1)) cos(cξ)/ξ − (h'(1) + h'(−1)) sin(cξ)/(cξ²) + (∫ h'' sin(cξs))/(cξ²)`;
so `ψ` is `A sin(cξ)/(cξ)` to `O(ξ⁻²)` and `u = (ξ² − 1)ψ'` is `Aξ cos(cξ)` to `O(1)`, `A = g(1) + g(−1)`.
-/

namespace Cvs.Prolate.CosineTransformSecondOrder

open Real Set intervalIntegral Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive
open scoped Interval

variable {g g₁ g₂ : ℝ → ℝ} {c ξ : ℝ}

/-- `sin(cξs)/(cξ)` is an antiderivative of `cos(cξs)` in `s`. -/
theorem hasDerivAt_sin_div (hcξ : c * ξ ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => sin (c * ξ * s) / (c * ξ)) (cos (c * ξ * s)) s := by
  have := (((hasDerivAt_id s).const_mul (c * ξ)).sin).div_const (c * ξ)
  refine this.congr_deriv ?_
  simp only [id, mul_one]
  exact (div_eq_iff hcξ).mpr (by ring)

/-- `−cos(cξs)/(cξ)` is an antiderivative of `sin(cξs)` in `s`. -/
theorem hasDerivAt_neg_cos_div (hcξ : c * ξ ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => -cos (c * ξ * s) / (c * ξ)) (sin (c * ξ * s)) s := by
  have := ((((hasDerivAt_id s).const_mul (c * ξ)).cos).neg).div_const (c * ξ)
  refine this.congr_deriv ?_
  simp only [id, mul_one]
  exact (div_eq_iff hcξ).mpr (by ring)

/-- **The transform to second order**:
`ψ(ξ) = (g(1) + g(−1)) sin(cξ)/(cξ) + (g₁(1) − g₁(−1)) cos(cξ)/(cξ)² − (∫ g₂ cos(cξs))/(cξ)²`. -/
theorem psi_eq (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hcξ : c * ξ ≠ 0) :
    psi c g ξ = (g 1 + g (-1)) * sin (c * ξ) / (c * ξ) + (g₁ 1 - g₁ (-1)) * cos (c * ξ) / (c * ξ) ^ 2
      - (∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)) / (c * ξ) ^ 2 := by
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have i1 := integral_mul_deriv_eq_deriv_mul hg (fun s _ => hasDerivAt_sin_div hcξ s)
    hg₁c.intervalIntegrable ((by fun_prop : Continuous fun s => cos (c * ξ * s)).intervalIntegrable (-1) 1)
  have i2 := integral_mul_deriv_eq_deriv_mul hg₁ (fun s _ => hasDerivAt_neg_cos_div hcξ s)
    hg₂c.intervalIntegrable ((by fun_prop : Continuous fun s => sin (c * ξ * s)).intervalIntegrable (-1) 1)
  unfold psi kint
  rw [i1]
  have e2 : ∫ s in (-1 : ℝ)..1, g₁ s * (sin (c * ξ * s) / (c * ξ))
      = (∫ s in (-1 : ℝ)..1, g₁ s * sin (c * ξ * s)) / (c * ξ) := by
    rw [← integral_div]; congr 1; funext s; ring
  rw [e2, i2]
  have e3 : ∫ s in (-1 : ℝ)..1, g₂ s * (-cos (c * ξ * s) / (c * ξ))
      = -(∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)) / (c * ξ) := by
    rw [← integral_neg, ← integral_div]; congr 1; funext s; ring
  rw [e3]
  simp only [mul_one, mul_neg_one, cos_neg, sin_neg]
  field_simp
  ring

/-- **`ψ` is `(g(1) + g(−1)) sin(cξ)/(cξ)` to `(|g₁(1) − g₁(−1)| + ∫|g₂|)/(cξ)²`.** -/
theorem psi_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hcξ : c * ξ ≠ 0) :
    |psi c g ξ - (g 1 + g (-1)) * sin (c * ξ) / (c * ξ)|
      ≤ (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / (c * ξ) ^ 2 := by
  rw [psi_eq hg hg₁ hg₂c hcξ]
  have hI : |∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)| ≤ ∫ s in (-1 : ℝ)..1, |g₂ s| := by
    refine (abs_integral_le_integral_abs (by norm_num)).trans ?_
    apply integral_mono_on (by norm_num)
    · exact (hg₂c.mul (by fun_prop : Continuous fun s => cos (c * ξ * s)).continuousOn).intervalIntegrable.abs
    · exact hg₂c.intervalIntegrable.abs
    · intro s _; rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hsq : 0 < (c * ξ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hcξ).symm
  rw [show (g 1 + g (-1)) * sin (c * ξ) / (c * ξ) + (g₁ 1 - g₁ (-1)) * cos (c * ξ) / (c * ξ) ^ 2
      - (∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)) / (c * ξ) ^ 2 - (g 1 + g (-1)) * sin (c * ξ) / (c * ξ)
      = ((g₁ 1 - g₁ (-1)) * cos (c * ξ) - ∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)) / (c * ξ) ^ 2 by ring]
  rw [abs_div, abs_of_pos hsq]
  apply div_le_div_of_nonneg_right _ hsq.le
  calc |(g₁ 1 - g₁ (-1)) * cos (c * ξ) - ∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)|
      ≤ |(g₁ 1 - g₁ (-1)) * cos (c * ξ)| + |∫ s in (-1 : ℝ)..1, g₂ s * cos (c * ξ * s)| := abs_sub _ _
    _ ≤ |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| := by
        apply add_le_add _ hI
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

/-- **The derivative of the transform to second order**: with `h = sg`, `h' = g + sg₁`, `h'' = 2g₁ + sg₂`,
`ψ'(ξ) = (g(1) + g(−1)) cos(cξ)/ξ − (h'(1) + h'(−1)) sin(cξ)/(cξ²) + (∫ h'' sin(cξs))/(cξ²)`. -/
theorem dpsi_eq (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hcξ : c * ξ ≠ 0) :
    kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ
      = (g 1 + g (-1)) * cos (c * ξ) / ξ - (g 1 + g₁ 1 + (g (-1) - g₁ (-1))) * sin (c * ξ) / (c * ξ ^ 2)
        + (∫ s in (-1 : ℝ)..1, (2 * g₁ s + s * g₂ s) * sin (c * ξ * s)) / (c * ξ ^ 2) := by
  have hc : c ≠ 0 := left_ne_zero_of_mul hcξ
  have hξ : ξ ≠ 0 := right_ne_zero_of_mul hcξ
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => s * g s) (g s + s * g₁ s) s := fun s hs => by
    refine ((hasDerivAt_id s).mul (hg s hs)).congr_deriv ?_; simp
  have hh' : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => g s + s * g₁ s) (2 * g₁ s + s * g₂ s) s :=
    fun s hs => by
      refine ((hg s hs).add ((hasDerivAt_id s).mul (hg₁ s hs))).congr_deriv ?_; simp; ring
  have i1 := integral_mul_deriv_eq_deriv_mul hh (fun s _ => hasDerivAt_neg_cos_div hcξ s)
    (hgc.add (continuousOn_id.mul hg₁c)).intervalIntegrable
    ((by fun_prop : Continuous fun s => sin (c * ξ * s)).intervalIntegrable (-1) 1)
  have i2 := integral_mul_deriv_eq_deriv_mul hh' (fun s _ => hasDerivAt_sin_div hcξ s)
    ((continuousOn_const.mul hg₁c).add (continuousOn_id.mul hg₂c)).intervalIntegrable
    ((by fun_prop : Continuous fun s => cos (c * ξ * s)).intervalIntegrable (-1) 1)
  beta_reduce at i1 i2
  unfold kint
  have e0 : ∫ s in (-1 : ℝ)..1, g s * -(c * s * sin (c * ξ * s))
      = -c * ∫ s in (-1 : ℝ)..1, s * g s * sin (c * ξ * s) := by
    rw [← integral_const_mul]; congr 1; funext s; ring
  rw [e0, i1]
  have e1 : ∫ s in (-1 : ℝ)..1, (g s + s * g₁ s) * (-cos (c * ξ * s) / (c * ξ))
      = -(∫ s in (-1 : ℝ)..1, (g s + s * g₁ s) * cos (c * ξ * s)) / (c * ξ) := by
    rw [← integral_neg, ← integral_div]; congr 1; funext s; ring
  rw [e1, i2]
  have e2 : ∫ s in (-1 : ℝ)..1, (2 * g₁ s + s * g₂ s) * (sin (c * ξ * s) / (c * ξ))
      = (∫ s in (-1 : ℝ)..1, (2 * g₁ s + s * g₂ s) * sin (c * ξ * s)) / (c * ξ) := by
    rw [← integral_div]; congr 1; funext s; ring
  rw [e2]
  simp only [mul_one, mul_neg_one, cos_neg, sin_neg, one_mul, neg_mul]
  field_simp
  ring

/-- **`u = (ξ² − 1)ψ'` is `(g(1) + g(−1)) ξ cos(cξ)` to `|g(1) + g(−1)|/ξ + C₂/c`**, for `c > 0`, `ξ ≥ 1`,
`C₂ = |h'(1) + h'(−1)| + ∫ (2|g₁| + |g₂|)`. -/
theorem u_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (hξ : 1 ≤ ξ) :
    |(ξ ^ 2 - 1) * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ - (g 1 + g (-1)) * ξ * cos (c * ξ)|
      ≤ |g 1 + g (-1)| / ξ
        + (|g 1 + g₁ 1 + (g (-1) - g₁ (-1))| + ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s|) / c := by
  have hξ0 : 0 < ξ := by linarith
  have hcξ : c * ξ ≠ 0 := by positivity
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  rw [dpsi_eq hg hg₁ hg₂c hcξ]
  set H := g 1 + g₁ 1 + (g (-1) - g₁ (-1)) with hH
  set I := ∫ s in (-1 : ℝ)..1, (2 * g₁ s + s * g₂ s) * sin (c * ξ * s) with hI
  set J := ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s| with hJ
  have hIJ : |I| ≤ J := by
    refine (abs_integral_le_integral_abs (by norm_num)).trans ?_
    apply integral_mono_on (by norm_num)
    · exact (((continuousOn_const.mul hg₁c).add (continuousOn_id.mul hg₂c)).mul
        (by fun_prop : Continuous fun s => sin (c * ξ * s)).continuousOn).intervalIntegrable.abs
    · exact ((continuousOn_const.mul hg₁c.abs).add hg₂c.abs).intervalIntegrable
    · intro s hs
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
      rw [abs_mul]
      calc |2 * g₁ s + s * g₂ s| * |sin (c * ξ * s)| ≤ |2 * g₁ s + s * g₂ s| * 1 :=
            mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg _)
        _ ≤ 2 * |g₁ s| + |g₂ s| := by
            rw [mul_one]
            calc |2 * g₁ s + s * g₂ s| ≤ |2 * g₁ s| + |s * g₂ s| := abs_add_le _ _
              _ = 2 * |g₁ s| + |s| * |g₂ s| := by rw [abs_mul, abs_mul, abs_two]
              _ ≤ 2 * |g₁ s| + 1 * |g₂ s| := by gcongr
              _ = 2 * |g₁ s| + |g₂ s| := by ring
  -- `(ξ² − 1)ψ' − Aξ cos = (ξ² − 1)(−H sin + I)/(cξ²) − A cos/ξ`
  have e : (ξ ^ 2 - 1) * ((g 1 + g (-1)) * cos (c * ξ) / ξ - H * sin (c * ξ) / (c * ξ ^ 2) + I / (c * ξ ^ 2))
      - (g 1 + g (-1)) * ξ * cos (c * ξ)
      = (ξ ^ 2 - 1) / (c * ξ ^ 2) * (I - H * sin (c * ξ)) - (g 1 + g (-1)) * cos (c * ξ) / ξ := by
    field_simp; ring
  rw [e]
  have h1 : |(ξ ^ 2 - 1) / (c * ξ ^ 2) * (I - H * sin (c * ξ))| ≤ (|H| + J) / c := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (by nlinarith) (by positivity) : 0 ≤ (ξ ^ 2 - 1) / (c * ξ ^ 2))]
    have hf : (ξ ^ 2 - 1) / (c * ξ ^ 2) ≤ 1 / c := by
      rw [div_le_div_iff₀ (by positivity) hc]; nlinarith
    have hb : |I - H * sin (c * ξ)| ≤ |H| + J := by
      calc |I - H * sin (c * ξ)| ≤ |I| + |H * sin (c * ξ)| := abs_sub _ _
        _ ≤ J + |H| := by
            apply add_le_add hIJ
            rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
        _ = |H| + J := add_comm _ _
    calc (ξ ^ 2 - 1) / (c * ξ ^ 2) * |I - H * sin (c * ξ)| ≤ 1 / c * (|H| + J) :=
          mul_le_mul hf hb (abs_nonneg _) (by positivity)
      _ = (|H| + J) / c := by ring
  have h2 : |(g 1 + g (-1)) * cos (c * ξ) / ξ| ≤ |g 1 + g (-1)| / ξ := by
    rw [abs_div, abs_of_pos hξ0, abs_mul]
    apply div_le_div_of_nonneg_right _ hξ0.le
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  calc |(ξ ^ 2 - 1) / (c * ξ ^ 2) * (I - H * sin (c * ξ)) - (g 1 + g (-1)) * cos (c * ξ) / ξ|
      ≤ |(ξ ^ 2 - 1) / (c * ξ ^ 2) * (I - H * sin (c * ξ))| + |(g 1 + g (-1)) * cos (c * ξ) / ξ| := abs_sub _ _
    _ ≤ (|H| + J) / c + |g 1 + g (-1)| / ξ := add_le_add h1 h2
    _ = _ := add_comm _ _

end Cvs.Prolate.CosineTransformSecondOrder
