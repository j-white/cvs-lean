import Mathlib
import Cvs.Finite.ModeSumDerivativeEnergy
import Cvs.Finite.WindowCosineBessel

/-!
# The partial sums' derivative energy is bounded by the target's

    ∫₀ᴸ (S_N′)² ≤ ∫₀ᴸ (g′)²

one integration by parts, whose boundary term vanishes because the modes complete a whole
number of turns.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Finite.PartialSumDerivEnergyBound

variable {L : ℝ}

/-- **The derivative's sine overlap, by parts.** -/
theorem integral_deriv_mul_sin (hL : 0 < L) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g') {n : ℕ} (hn : 0 < n) :
    (∫ x in (0:ℝ)..L, g' x * Real.sin (2 * π * n / L * x))
      = -(2 * π * n / L) * (∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * n / L * x)) := by
  set ω : ℝ := 2 * π * n / L with hω
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hωne : ω ≠ 0 := by rw [hω]; positivity
  have hgc : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact (hgd x).continuousAt
  -- the antiderivative of the mode
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.sin (ω * y) / ω) (Real.cos (ω * x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => ω * y) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (ω * y)) (Real.cos (ω * x) * ω) x := h1.sin
    have h3 := h2.div_const ω
    have heq : Real.cos (ω * x) * ω / ω = Real.cos (ω * x) := by
      field_simp
    rwa [heq] at h3
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (u' := g') (v := fun y : ℝ => Real.sin (ω * y) / ω) (v' := fun y : ℝ => Real.cos (ω * y))
    (a := 0) (b := L)
    (fun x _ => hgd x) (fun x _ => hv x)
    (hg'c.intervalIntegrable _ _)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  -- the boundary term is a whole number of turns
  have hsinL : Real.sin (ω * L) = 0 := by
    have hEq : ω * L = (n : ℝ) * (2 * π) := by rw [hω]; field_simp
    rw [hEq]
    have h0 : Real.sin ((n : ℝ) * (2 * π) - 0) = -Real.sin 0 :=
      Real.sin_nat_mul_two_pi_sub 0 n
    simpa using h0
  have hsin0 : Real.sin (ω * 0) = 0 := by simp
  rw [hsinL, hsin0] at hibp
  simp only [zero_div, mul_zero, sub_zero, zero_sub] at hibp
  have hdiv : (∫ x in (0:ℝ)..L, g' x * (Real.sin (ω * x) / ω))
      = (∫ x in (0:ℝ)..L, g' x * Real.sin (ω * x)) / ω := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hdiv] at hibp
  field_simp at hibp ⊢
  linarith [hibp]

/-- **The partial sums' derivative energy is bounded by the target's.** -/
theorem integral_modeSumDeriv_sq_le (hL : 0 < L) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g') (s : Finset ℕ) :
    (∫ x in (0:ℝ)..L, (Cvs.Finite.ModeSumDerivativeEnergy.modeSumDeriv L s
        (Cvs.Finite.WindowCosineBessel.coef L g) x) ^ 2)
      ≤ ∫ x in (0:ℝ)..L, g' x ^ 2 := by
  classical
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  set T : ℝ → ℝ := Cvs.Finite.ModeSumDerivativeEnergy.modeSumDeriv L s a with hT
  have hTc : Continuous T := Cvs.Finite.ModeSumDerivativeEnergy.continuous_modeSumDeriv L s a
  -- the cross term equals the mode sum's own derivative energy
  have hcross : (∫ x in (0:ℝ)..L, g' x * T x) = ∫ x in (0:ℝ)..L, T x ^ 2 := by
    have hpt : ∀ x : ℝ, g' x * T x
        = ∑ n ∈ s, -(a n * (2 * π * n / L)) * (g' x * Real.sin (2 * π * n / L * x)) := by
      intro x
      rw [hT]
      show g' x * (∑ n ∈ s, -(a n * (2 * π * n / L)) * Real.sin (2 * π * n / L * x)) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    have hint : ∀ n : ℕ, IntervalIntegrable
        (fun x : ℝ => -(a n * (2 * π * n / L)) * (g' x * Real.sin (2 * π * n / L * x)))
        volume 0 L := by
      intro n
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_congr (fun x _ => hpt x),
      intervalIntegral.integral_finsetSum (fun n _ => hint n),
      Cvs.Finite.ModeSumDerivativeEnergy.integral_modeSumDeriv_sq hL s a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      norm_num
    · rw [integral_deriv_mul_sin hL hgd hg'c hn, ha,
        Cvs.Finite.WindowCosineBessel.integral_mul_cos hL g n]
      have hne : ¬ (n = 0) := by omega
      rw [if_neg hne]
      ring
  -- expand the square of the difference
  have hexp : ∀ x : ℝ, (g' x - T x) ^ 2 = g' x ^ 2 - 2 * (g' x * T x) + T x ^ 2 := by
    intro x; ring
  have hi1 : IntervalIntegrable (fun x : ℝ => g' x ^ 2) volume 0 L :=
    (hg'c.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => 2 * (g' x * T x)) volume 0 L :=
    ((continuous_const.mul (hg'c.mul hTc))).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun x : ℝ => T x ^ 2) volume 0 L :=
    ((hTc.pow 2)).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ x in (0:ℝ)..L, (g' x - T x) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)
  rw [intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_add (hi1.sub hi2) hi3,
    intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    hcross] at hnn
  linarith

end Cvs.Finite.PartialSumDerivEnergyBound
