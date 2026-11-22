import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.L2a.PlaneBridgePerRung
import Cvs.Prolate.LiouvilleGreen.LayerWindowSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Charging per-rung approximation errors to the tail norm

For `|E_j| ≤ ε_j` on `[p, q]`: `∫(Σ_j a_jE_j)² ≤ (Σ_j |a_j|‖ε_j‖)² ≤ (Σ_j a_j²D_j)·Σ_j ‖ε_j‖²/D_j` for any positive
weights `D_j` (Minkowski, then Cvs.L2a.PlaneBridgePerRung), so with a frame bound `λΣ a_j²D_j ≤ N` the span's layer error is at most
`(Σ_j ‖ε_j‖²/D_j)/λ · N`: the certified `e_N` of the layer bootstrap from per-rung bounds.
-/

namespace Cvs.L2a.RungApproximationErrorCharge

open Real Set Finset MeasureTheory intervalIntegral Cvs.L2a.PlaneBridgePerRung Cvs.Prolate.LiouvilleGreen.LayerWindowSplit

/-- **Minkowski for a finite sum on an interval**: `∫(Σ_j f_j)² ≤ (Σ_j √∫f_j²)²`. -/
theorem integral_sum_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {p q : ℝ} (hpq : p ≤ q)
    (hf : ∀ j ∈ s, ContinuousOn (f j) (Icc p q)) :
    ∫ x in p..q, (∑ j ∈ s, f j x) ^ 2 ≤ (∑ j ∈ s, √(∫ x in p..q, f j x ^ 2)) ^ 2 := by
  have hII : ∀ j ∈ s, ∀ k ∈ s, IntervalIntegrable (fun x => f j x * f k x) volume p q := fun j hj k hk =>
    ((hf j hj).mul (hf k hk)).intervalIntegrable_of_Icc hpq
  have hexp : ∫ x in p..q, (∑ j ∈ s, f j x) ^ 2 = ∑ j ∈ s, ∑ k ∈ s, ∫ x in p..q, f j x * f k x := by
    have e : (fun x => (∑ j ∈ s, f j x) ^ 2) = fun x => ∑ j ∈ s, ∑ k ∈ s, f j x * f k x := by
      funext x; rw [sq, Finset.sum_mul_sum]
    have hsumII : ∀ j ∈ s, IntervalIntegrable (fun x => ∑ k ∈ s, f j x * f k x) volume p q := fun j hj =>
      (continuousOn_finsetSum _ fun k hk => (hf j hj).mul (hf k hk)).intervalIntegrable_of_Icc hpq
    rw [e, intervalIntegral.integral_finsetSum hsumII]
    exact Finset.sum_congr rfl fun j hj => intervalIntegral.integral_finsetSum fun k hk => hII j hj k hk
  rw [hexp, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
  exact (le_abs_self _).trans (abs_integral_mul_le hpq (hf j hj) (hf k hk))

/-- **The layer error of a span from per-rung bounds.** -/
theorem layer_error_le {ι : Type*} [Fintype ι] (a D : ι → ℝ) (E ε : ι → ℝ → ℝ) {p q : ℝ} (hpq : p ≤ q)
    (hD : ∀ j, 0 < D j) (hE : ∀ j, ∀ x ∈ Icc p q, |E j x| ≤ ε j x)
    (hEc : ∀ j, ContinuousOn (E j) (Icc p q)) (hεc : ∀ j, ContinuousOn (ε j) (Icc p q)) :
    ∫ x in p..q, (∑ j, a j * E j x) ^ 2
      ≤ (∑ j, a j ^ 2 * D j) * ∑ j, (∫ x in p..q, ε j x ^ 2) / D j := by
  -- pointwise `|Σ a_jE_j| ≤ Σ |a_j|ε_j`
  have hpt : ∀ x ∈ Icc p q, (∑ j, a j * E j x) ^ 2 ≤ (∑ j, |a j| * ε j x) ^ 2 := fun x hx => by
    have h1 : |∑ j, a j * E j x| ≤ ∑ j, |a j| * ε j x :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hE j x hx) (abs_nonneg _))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hc1 : ContinuousOn (fun x => (∑ j, a j * E j x) ^ 2) (Icc p q) :=
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (hEc j)).pow 2
  have hc2 : ContinuousOn (fun x => (∑ j, |a j| * ε j x) ^ 2) (Icc p q) :=
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (hεc j)).pow 2
  have step1 := intervalIntegral.integral_mono_on hpq (hc1.intervalIntegrable_of_Icc (μ := volume) hpq)
    (hc2.intervalIntegrable_of_Icc (μ := volume) hpq) hpt
  have step2 := integral_sum_sq_le Finset.univ (fun j x => |a j| * ε j x) hpq
    fun j _ => continuousOn_const.mul (hεc j)
  -- `√∫(|a_j|ε_j)² = |a_j|‖ε_j‖`
  have hnorm : ∀ j, √(∫ x in p..q, (|a j| * ε j x) ^ 2) = |a j| * √(∫ x in p..q, ε j x ^ 2) := fun j => by
    have e : (fun x => (|a j| * ε j x) ^ 2) = fun x => |a j| ^ 2 * ε j x ^ 2 := by funext x; ring
    rw [e, intervalIntegral.integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  simp only [hnorm] at step2
  have step3 := sq_sum_le_weighted (fun j => |a j|) (fun j => √(∫ x in p..q, ε j x ^ 2)) D hD
  have hsq : ∀ j, √(∫ x in p..q, ε j x ^ 2) ^ 2 = ∫ x in p..q, ε j x ^ 2 := fun j =>
    Real.sq_sqrt (intervalIntegral.integral_nonneg hpq fun x _ => sq_nonneg _)
  simp only [sq_abs, hsq] at step3
  linarith

end Cvs.L2a.RungApproximationErrorCharge
