import Mathlib
import Cvs.Finite.ConstantModeCarriesL
import Cvs.Finite.ConstantModeOrthogonal
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.ShiftSumModeDiagonal

/-!
# The mode pairing table, constant mode included

    ∫₀^L cos(2πmx/L)·cos(2πnx/L) dx = 0 unless m = n, and then `L` at `m = 0`, `L/2` after

the four cases assembled into one statement, so a sum over a `Finset` that may contain `0`
can be read off without a positivity hypothesis.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.Finite.ModePairingTable

/-- **The mode pairing, all cases.** -/
theorem integral_mode_pair {L : ℝ} (hL : 0 < L) (m n : ℕ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * x))
      = if m = n then (if m = 0 then L else L / 2) else 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h := Cvs.Finite.ConstantModeCarriesL.integral_mode_zero L 0
      simp only [if_pos rfl]
      refine Eq.trans ?_ h
      refine intervalIntegral.integral_congr fun x _ => ?_
      norm_num
    · have hne : (0:ℕ) ≠ n := by omega
      rw [if_neg hne]
      have h := Cvs.Finite.ConstantModeOrthogonal.integral_mode_cross_zero hL hn 0 0
      refine Eq.trans ?_ h
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [add_zero]
      ring
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hne : m ≠ 0 := by omega
      rw [if_neg hne]
      have h := Cvs.Finite.ConstantModeOrthogonal.integral_mode_cross_zero hL hm 0 0
      refine Eq.trans ?_ h
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [add_zero]
    · by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, if_neg (by omega : ¬ m = 0)]
        have h := Cvs.WeilForm.ShiftSumModeDiagonal.integral_shift_mode hL hm 0
        simp only [mul_zero, Real.cos_zero, mul_one] at h
        refine Eq.trans ?_ h
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [add_zero]
      · rw [if_neg hmn]
        have h := Cvs.WeilForm.ShiftSumModeDiagonal.integral_shift_cross hL hm hn hmn 0 0
        refine Eq.trans ?_ h
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [add_zero]

/-- **The norm of a mode sum, constant mode included.**  The `n = 0` coefficient is weighted
twice, which is exactly why `∑ aₙ²` is not the `L²` norm. -/
theorem integral_modeSum_sq {L : ℝ} (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in (0:ℝ)..L, (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x) ^ 2)
      = L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * a n ^ 2 := by
  classical
  have hpt : ∀ x : ℝ, (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x) ^ 2
      = ∑ m ∈ s, ∑ n ∈ s, (a m * a n)
          * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * x)) := by
    intro x
    unfold Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hisum : ∀ m : ℕ, IntervalIntegrable
      (fun x : ℝ => ∑ n ∈ s, (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * x)))
      MeasureTheory.volume 0 L := by
    intro m; apply Continuous.intervalIntegrable; fun_prop
  have hi : ∀ m n : ℕ, IntervalIntegrable
      (fun x : ℝ => (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * x)))
      MeasureTheory.volume 0 L := by
    intro m n; apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_finsetSum (fun m _ => hisum m)]
  have hinner : ∀ m ∈ s, (∫ x in (0:ℝ)..L, ∑ n ∈ s, (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * x)))
      = L / 2 * ((if m = 0 then 2 else 1) * a m ^ 2) := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi m n)]
    have hterm : ∀ n ∈ s, (∫ x in (0:ℝ)..L, (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * x)))
        = if n = m then L / 2 * ((if m = 0 then 2 else 1) * a m ^ 2) else 0 := by
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_mode_pair hL m n]
      by_cases h : m = n
      · subst h
        rw [if_pos rfl, if_pos rfl]
        by_cases h0 : m = 0
        · rw [if_pos h0, if_pos h0]; ring
        · rw [if_neg h0, if_neg h0]; ring
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s m]
    rw [if_pos hm]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

end Cvs.Finite.ModePairingTable
