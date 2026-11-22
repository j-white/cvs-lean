import Mathlib
import Cvs.Route.NestedBoxInduction
import Cvs.Route.OneCellLaplaceTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The induction step from a Lévy representation of the one-cell function
If `G(L) = ∑ wᵢ (1 − cos γᵢ L)` on `L ≥ 0` with `wᵢ ≥ 0` (summable at each `L`) and `γᵢ` real, the box kernel is a Gram kernel,
`(1−cos a)+(1−cos b)−(1−cos(a−b)) = (1−cos a)(1−cos b) + sin a sin b`, so every step `Cvs.Route.NestedBoxInduction.Step N` holds, hence RH.
Under RH this representation is the zero side, `wᵢ = 4/γᵢ²` over the ordinates; it is what the step lemma needs.
-/

noncomputable section

open Real Finset

namespace Cvs.Route.NestedBoxLevyStep
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G)
open Cvs.Route.NestedBoxInduction (K qf BoxPSD Step)

/-- A Lévy representation of `G`: nonnegative weights at real frequencies, summable at each `L ≥ 0`. -/
structure LevyRep (ι : Type*) where
  w : ι → ℝ
  γ : ι → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  summable_term : ∀ L, 0 ≤ L → Summable fun i => w i * (1 - Real.cos (γ i * L))
  eq : ∀ L, 0 ≤ L → G L = ∑' i, w i * (1 - Real.cos (γ i * L))

variable {ι : Type*} (R : LevyRep ι)

theorem cos_mul_abs (g d : ℝ) : Real.cos (g * |d|) = Real.cos (g * d) := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, mul_neg, Real.cos_neg]

/-- The kernel identity, term by term. -/
theorem kernel_term (g x y : ℝ) :
    ((1 - Real.cos (g * x)) + (1 - Real.cos (g * y)) - (1 - Real.cos (g * |x - y|))) / 2
      = ((1 - Real.cos (g * x)) * (1 - Real.cos (g * y)) + Real.sin (g * x) * Real.sin (g * y)) / 2 := by
  rw [cos_mul_abs, mul_sub, Real.cos_sub]; ring

/-- The box kernel as a Gram series. -/
theorem hasSum_K {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    HasSum (fun i => R.w i * (((1 - Real.cos (R.γ i * x)) * (1 - Real.cos (R.γ i * y))
      + Real.sin (R.γ i * x) * Real.sin (R.γ i * y)) / 2)) (K x y) := by
  have hx' := (R.summable_term x hx).hasSum
  have hy' := (R.summable_term y hy).hasSum
  have hd' := (R.summable_term |x - y| (abs_nonneg _)).hasSum
  rw [← R.eq x hx] at hx'; rw [← R.eq y hy] at hy'; rw [← R.eq _ (abs_nonneg _)] at hd'
  have h := ((hx'.add hy').sub hd').div_const 2
  unfold K
  refine h.congr_fun fun i => ?_
  rw [← kernel_term]; ring

/-- **The step lemma, from a Lévy representation**: the nested-box form is nonnegative at every level. -/
theorem boxPSD (R : LevyRep ι) (M : ℕ) : BoxPSD M := fun c => by
  have hterm : ∀ m ∈ Icc 2 M, ∀ n ∈ Icc 2 M, HasSum (fun i => c m * c n * (R.w i *
      (((1 - Real.cos (R.γ i * Real.log m)) * (1 - Real.cos (R.γ i * Real.log n))
        + Real.sin (R.γ i * Real.log m) * Real.sin (R.γ i * Real.log n)) / 2)))
      (c m * c n * K (Real.log m) (Real.log n)) := fun m _ n _ =>
    (hasSum_K R (Real.log_natCast_nonneg m) (Real.log_natCast_nonneg n)).mul_left _
  have hall := hasSum_sum fun m hm => hasSum_sum fun n hn => hterm m hm n hn
  refine hall.nonneg fun i => ?_
  set u : ℕ → ℝ := fun m => 1 - Real.cos (R.γ i * Real.log m)
  set v : ℕ → ℝ := fun m => Real.sin (R.γ i * Real.log m)
  have hsq : ∑ m ∈ Icc 2 M, ∑ n ∈ Icc 2 M, c m * c n * (R.w i * ((u m * u n + v m * v n) / 2))
      = R.w i / 2 * ((∑ m ∈ Icc 2 M, c m * u m) ^ 2 + (∑ m ∈ Icc 2 M, c m * v m) ^ 2) := by
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  simp only [u, v] at hsq
  rw [hsq]
  exact mul_nonneg (div_nonneg (R.w_nonneg i) two_pos.le) (by positivity)

theorem step (R : LevyRep ι) (N : ℕ) : Step N := Cvs.Route.NestedBoxInduction.step_of_boxPSD (boxPSD R (N + 1))

/-- `RH` from a Lévy representation of the one-cell function. -/
theorem rh_of_levyRep (R : LevyRep ι) : RiemannHypothesis := Cvs.Route.NestedBoxInduction.rh_of_forall_step fun N _ => step R N

end Cvs.Route.NestedBoxLevyStep
