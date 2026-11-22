import Mathlib
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

/-!
# The mode sum's derivative, and its energy

    (∑ aₙ cos(2πnx/L))' = −∑ aₙ(2πn/L) sin(2πnx/L),
    ∫₀ᴸ of its square = (L/2)·∑ (2πn/L)²aₙ²

the sine modes being orthogonal, so the derivative energy is a sum of nonnegative terms.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Finite.ModeSumDerivativeEnergy

/-- The mode sum's derivative. -/
def modeSumDeriv (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑ n ∈ s, -(a n * (2 * π * n / L)) * Real.sin (2 * π * n / L * x)

theorem continuous_modeSumDeriv (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    Continuous (modeSumDeriv L s a) := by
  show Continuous (fun x : ℝ => ∑ n ∈ s, -(a n * (2 * π * n / L)) * Real.sin (2 * π * n / L * x))
  exact continuous_finsetSum _ (fun n _ => by fun_prop)

/-- **The sine modes are orthogonal.** -/
theorem integral_sin_sin {L : ℝ} (hL : 0 < L) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∫ x in (0:ℝ)..L, Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x))
      = if m = n then L / 2 else 0 := by
  set km : ℤ := (m : ℤ) - (n : ℤ) with hkm
  set kp : ℤ := (m : ℤ) + (n : ℤ) with hkp
  have hprod : ∀ x : ℝ, Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x)
      = Real.cos (2 * π * (km : ℝ) / L * x + 0) / 2
        - Real.cos (2 * π * (kp : ℝ) / L * x + 0) / 2 := by
    intro x
    have h1 : (2:ℝ) * π * (km : ℝ) / L * x + 0
        = 2 * π * m / L * x - 2 * π * n / L * x := by rw [hkm]; push_cast; ring
    have h2 : (2:ℝ) * π * (kp : ℝ) / L * x + 0
        = 2 * π * m / L * x + 2 * π * n / L * x := by rw [hkp]; push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hi1 : IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * π * (km : ℝ) / L * x + 0) / 2) volume 0 L := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * π * (kp : ℝ) / L * x + 0) / 2) volume 0 L := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_congr (fun x _ => hprod x),
    intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_div,
    intervalIntegral.integral_div]
  have hsum : kp ≠ 0 := by
    rw [hkp]
    have hm' : (0:ℤ) < (m : ℤ) := by exact_mod_cast hm
    have hn' : (0:ℤ) < (n : ℤ) := by exact_mod_cast hn
    omega
  rw [Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.integral_cos_turns hL hsum 0]
  by_cases hmn : m = n
  · have hzero : km = 0 := by rw [hkm, hmn]; ring
    rw [hzero]
    simp only [if_pos hmn, Int.cast_zero]
    norm_num
  · have hdiff : km ≠ 0 := by
      rw [hkm]
      intro hc
      exact hmn (by exact_mod_cast sub_eq_zero.mp hc)
    rw [Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.integral_cos_turns hL hdiff 0, if_neg hmn]
    norm_num

/-- **The derivative energy of a mode sum.** -/
theorem integral_modeSumDeriv_sq {L : ℝ} (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in (0:ℝ)..L, (modeSumDeriv L s a x) ^ 2)
      = L / 2 * ∑ n ∈ s, (2 * π * n / L) ^ 2 * a n ^ 2 := by
  classical
  set b : ℕ → ℝ := fun n => -(a n * (2 * π * n / L)) with hb
  have hb0 : b 0 = 0 := by rw [hb]; simp
  have hpt : ∀ x : ℝ, (modeSumDeriv L s a x) ^ 2
      = ∑ m ∈ s, ∑ n ∈ s, (b m * b n)
          * (Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x)) := by
    intro x
    show (∑ n ∈ s, b n * Real.sin (2 * π * n / L * x)) ^ 2 = _
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hisum : ∀ m : ℕ, IntervalIntegrable
      (fun x : ℝ => ∑ n ∈ s, (b m * b n)
        * (Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x)))
      MeasureTheory.volume 0 L := by
    intro m; apply Continuous.intervalIntegrable; fun_prop
  have hi : ∀ m n : ℕ, IntervalIntegrable
      (fun x : ℝ => (b m * b n)
        * (Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x)))
      MeasureTheory.volume 0 L := by
    intro m n; apply Continuous.intervalIntegrable; fun_prop
  have hval : ∀ m n : ℕ, (∫ x in (0:ℝ)..L, (b m * b n)
      * (Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x)))
      = if m = n then b m ^ 2 * (L / 2) else 0 := by
    intro m n
    rw [intervalIntegral.integral_const_mul]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hb0, zero_mul, zero_mul]
      by_cases h : 0 = n
      · rw [if_pos h]; norm_num
      · rw [if_neg h]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hb0, mul_zero, zero_mul]
      by_cases h : m = 0
      · exact absurd h (by omega)
      · rw [if_neg h]
    rw [integral_sin_sin hL hm hn]
    by_cases h : m = n
    · subst h
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_finsetSum (fun m _ => hisum m)]
  have hinner : ∀ m ∈ s, (∫ x in (0:ℝ)..L, ∑ n ∈ s, (b m * b n)
      * (Real.sin (2 * π * m / L * x) * Real.sin (2 * π * n / L * x)))
      = if m ∈ s then b m ^ 2 * (L / 2) else 0 := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n _ => hi m n),
      Finset.sum_congr rfl (fun n _ => hval m n),
      Finset.sum_ite_eq s m (fun _ => b m ^ 2 * (L / 2)), if_pos hm]
  rw [Finset.sum_congr rfl hinner, Finset.sum_congr rfl (fun m hm => if_pos hm),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hb]
  ring

end Cvs.Finite.ModeSumDerivativeEnergy
