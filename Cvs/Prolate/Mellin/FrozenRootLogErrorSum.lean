import Mathlib
import Cvs.Prolate.Mellin.FrozenRootCanonicalLog
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Summing the frozen-root log error along a line

For `x₀ ≥ 2`, `Σ_{k<K} 1/(x_k(x_k + c)) ≤ (1 + log(1 + c/2))/(2c)` with `x_k = x₀ + 2k`; hence along `s_k = s₀ + 2k`,
`Σ_{k<K} ‖g(s_k) − ĝ(s_k + 3/2)‖ ≤ 80 (4/ε)⁵ (1 + log(1 + c/2))/c`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.FrozenRootLogErrorSum

open Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.WkbPhaseAntiderivative Cvs.Prolate.Mellin.FrozenRootCanonicalLog

theorem step_le_log {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    1 / ((x + 2) * (x + 2 + c)) ≤ 1 / (2 * c) * (Real.log (1 + c / x) - Real.log (1 + c / (x + 2))) := by
  have ha : 0 < 1 + c / x := by positivity
  have hb : 0 < 1 + c / (x + 2) := by positivity
  have hl : 1 - (1 + c / (x + 2)) / (1 + c / x) ≤ Real.log (1 + c / x) - Real.log (1 + c / (x + 2)) := by
    have := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at this; linarith
  have e : 1 - (1 + c / (x + 2)) / (1 + c / x) = 2 * c / ((x + 2) * (x + c)) := by
    field_simp; ring
  rw [e] at hl
  calc 1 / ((x + 2) * (x + 2 + c)) ≤ 1 / (2 * c) * (2 * c / ((x + 2) * (x + c))) := by
        rw [show 1 / (2 * c) * (2 * c / ((x + 2) * (x + c))) = 1 / ((x + 2) * (x + c)) by field_simp]
        apply one_div_le_one_div_of_le (by positivity); nlinarith
    _ ≤ _ := by gcongr

/-- **The `1/(x(x+c))` sum.** -/
theorem sum_inv_mul_le {c x₀ : ℝ} (hc : 0 < c) (hx : 2 ≤ x₀) (K : ℕ) :
    ∑ k ∈ range K, 1 / ((x₀ + 2 * k) * (x₀ + 2 * k + c)) ≤ (1 + Real.log (1 + c / 2)) / (2 * c) := by
  set φ := fun k : ℕ => Real.log (1 + c / (x₀ + 2 * k))
  have key : ∀ K : ℕ, ∑ k ∈ range (K + 1), 1 / ((x₀ + 2 * k) * (x₀ + 2 * k + c))
      ≤ 1 / (x₀ * (x₀ + c)) + 1 / (2 * c) * (φ 0 - φ K) := by
    intro K
    induction K with
    | zero => simp [φ]
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hK : 0 < x₀ + 2 * (K : ℝ) := by have := K.cast_nonneg (α := ℝ); linarith
      have := step_le_log hc hK
      have e1 : x₀ + 2 * ((K + 1 : ℕ) : ℝ) = x₀ + 2 * (K : ℝ) + 2 := by push_cast; ring
      have e2 : φ (K + 1) = Real.log (1 + c / (x₀ + 2 * (K : ℝ) + 2)) := by simp only [φ]; rw [e1]
      rw [e1]
      have : φ K = Real.log (1 + c / (x₀ + 2 * (K : ℝ))) := rfl
      rw [e2] at *; rw [this] at ih
      linarith
  cases K with
  | zero =>
    have h1 : (0 : ℝ) ≤ Real.log (1 + c / 2) := Real.log_nonneg (by linarith [show 0 ≤ c / 2 by positivity])
    simp; positivity
  | succ K =>
    refine (key K).trans ?_
    have h0 : φ 0 ≤ Real.log (1 + c / 2) := by
      simp only [φ, Nat.cast_zero, mul_zero, add_zero]
      apply Real.log_le_log (by positivity)
      have : c / x₀ ≤ c / 2 := by apply div_le_div_of_nonneg_left hc.le (by norm_num) hx
      linarith
    have hK : 0 ≤ φ K := by
      simp only [φ]; apply Real.log_nonneg
      have : 0 ≤ c / (x₀ + 2 * (K : ℝ)) := by have := K.cast_nonneg (α := ℝ); positivity
      linarith
    have h1 : 1 / (x₀ * (x₀ + c)) ≤ 1 / (2 * c) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    calc 1 / (x₀ * (x₀ + c)) + 1 / (2 * c) * (φ 0 - φ K)
        ≤ 1 / (2 * c) + 1 / (2 * c) * Real.log (1 + c / 2) := by
          have : 1 / (2 * c) * (φ 0 - φ K) ≤ 1 / (2 * c) * Real.log (1 + c / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
          linarith
      _ = _ := by ring

variable {ε c χ : ℝ} {s₀ : ℂ}

/-- **The log-error sum along a line.** -/
theorem Hyp.sum_gL_sub_gh_le (h : Hyp ε c χ s₀) (hε4 : ε ≤ 1 / 4) (K : ℕ) :
    ∑ k ∈ range K, ‖gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2)‖
      ≤ 160 / (ε / 4) ^ 5 * ((1 + Real.log (1 + c / 2)) / (2 * c)) := by
  have hc := h.c_pos
  have hε := h.hε
  have hx0 := h.hre
  calc _ ≤ ∑ k ∈ range K, 160 / (ε / 4) ^ 5 * (1 / ((s₀.re + 3 / 2 + 2 * k) * (s₀.re + 3 / 2 + 2 * k + c))) :=
        Finset.sum_le_sum fun k _ => by
          have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
          have hb := Hyp.norm_gL_sub_gh_le hl hε4
          refine hb.trans ?_
          rw [div_eq_mul_one_div (160 / (ε / 4) ^ 5)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hre : s₀.re + 3 / 2 + 2 * (k : ℝ) ≤ ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ := by
            have := Complex.re_le_norm (s₀ + 2 * (k : ℂ) + 3 / 2); simp at this; linarith
          have hpos : 0 < s₀.re + 3 / 2 + 2 * (k : ℝ) := by have := k.cast_nonneg (α := ℝ); linarith
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul hre (by linarith) (by positivity) (by positivity)
    _ = 160 / (ε / 4) ^ 5 * ∑ k ∈ range K, 1 / ((s₀.re + 3 / 2 + 2 * k) * (s₀.re + 3 / 2 + 2 * k + c)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_inv_mul_le hc (by linarith) K

end Cvs.Prolate.Mellin.FrozenRootLogErrorSum
