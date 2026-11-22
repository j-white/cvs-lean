import Mathlib
import Cvs.Finite.ConstantModeCarriesL
import Cvs.Finite.ConstantModeOrthogonal
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.ShiftSumModeDiagonal

/-!
# The shifted pairing table, and the shift sum on a mode sum

    ∫₀^L cos(ωₘx)·cos(ωₙ(x+v)) dx = if m = n then (if m = 0 then L else L/2)·cos(ωₘ v) else 0

so the shift sum on `modeSum` is diagonal with the constant mode weighted twice, exactly as
the norm is.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.Finite.ShiftedModePairingTable

/-- **The pairing at a displacement, all cases.** -/
theorem integral_mode_pair_shift {L : ℝ} (hL : 0 < L) (m n : ℕ) (v : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * (x + v)))
      = if m = n then (if m = 0 then L else L / 2) * Real.cos (2 * π * m / L * v) else 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [if_pos rfl, if_pos rfl]
      have h := Cvs.Finite.ConstantModeCarriesL.integral_mode_zero L v
      refine Eq.trans h ?_
      norm_num
    · rw [if_neg (by omega : ¬ (0:ℕ) = n)]
      have h := Cvs.Finite.ConstantModeOrthogonal.integral_mode_cross_zero hL hn v 0
      refine Eq.trans ?_ h
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [add_zero]
      ring
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [if_neg (by omega : ¬ m = 0)]
      have h := Cvs.Finite.ConstantModeOrthogonal.integral_mode_cross_zero hL hm 0 v
      refine Eq.trans ?_ h
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [add_zero]
    · by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, if_neg (by omega : ¬ m = 0)]
        exact Cvs.WeilForm.ShiftSumModeDiagonal.integral_shift_mode hL hm v
      · rw [if_neg hmn]
        have h := Cvs.WeilForm.ShiftSumModeDiagonal.integral_shift_cross hL hm hn hmn 0 v
        refine Eq.trans ?_ h
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [add_zero]

/-- **The shift sum on a mode sum is diagonal**, with the constant mode weighted twice. -/
theorem integral_modeSum_shift {L : ℝ} (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) (v : ℝ) :
    (∫ x in (0:ℝ)..L, Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x
        * Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a (x + v))
      = L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * a n ^ 2
          * Real.cos (2 * π * n / L * v) := by
  classical
  have hpt : ∀ x : ℝ, Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x
      * Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a (x + v)
      = ∑ m ∈ s, ∑ n ∈ s, (a m * a n)
          * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * (x + v))) := by
    intro x
    unfold Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hisum : ∀ m : ℕ, IntervalIntegrable
      (fun x : ℝ => ∑ n ∈ s, (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * (x + v))))
      MeasureTheory.volume 0 L := by
    intro m; apply Continuous.intervalIntegrable; fun_prop
  have hi : ∀ m n : ℕ, IntervalIntegrable
      (fun x : ℝ => (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * (x + v))))
      MeasureTheory.volume 0 L := by
    intro m n; apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_finsetSum (fun m _ => hisum m)]
  have hinner : ∀ m ∈ s, (∫ x in (0:ℝ)..L, ∑ n ∈ s, (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * (x + v))))
      = L / 2 * ((if m = 0 then 2 else 1) * a m ^ 2
          * Real.cos (2 * π * m / L * v)) := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi m n)]
    have hterm : ∀ n ∈ s, (∫ x in (0:ℝ)..L, (a m * a n)
        * (Real.cos (2 * π * m / L * x) * Real.cos (2 * π * n / L * (x + v))))
        = if n = m then L / 2 * ((if m = 0 then 2 else 1) * a m ^ 2
            * Real.cos (2 * π * m / L * v)) else 0 := by
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_mode_pair_shift hL m n v]
      by_cases h : m = n
      · subst h
        rw [if_pos rfl, if_pos rfl]
        by_cases h0 : m = 0
        · rw [if_pos h0, if_pos h0]; ring
        · rw [if_neg h0, if_neg h0]; ring
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s m, if_pos hm]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

end Cvs.Finite.ShiftedModePairingTable
