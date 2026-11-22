import Mathlib
import Cvs.Finite.ModeSumDerivativeEnergy
import Cvs.Finite.PartialSumDerivEnergyBound
import Cvs.Finite.WindowCosineBessel

/-!
# The coefficient mass is finite

    ∑ |aₙ| < ∞,  because ∑ n²aₙ² < ∞ and ∑ 1/n² < ∞

so the partial sums are uniformly bounded, which is the last of the three coefficient data.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Finite.CoefficientMassFinite

variable {L : ℝ}

/-- **The weighted coefficient square series converges.** -/
theorem summable_sq (hL : 0 < L) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g') :
    Summable (fun n : ℕ => (2 * π * n / L) ^ 2 * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2) := by
  refine summable_of_sum_range_le (c := (2 / L) * ∫ x in (0:ℝ)..L, g' x ^ 2)
    (fun n => by positivity) (fun N => ?_)
  have h1 := Cvs.Finite.ModeSumDerivativeEnergy.integral_modeSumDeriv_sq hL (Finset.range N)
    (Cvs.Finite.WindowCosineBessel.coef L g)
  have h2 := Cvs.Finite.PartialSumDerivEnergyBound.integral_modeSumDeriv_sq_le hL hgd hg'c (Finset.range N)
  rw [h1] at h2
  have hL0 : L ≠ 0 := hL.ne'
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (by positivity : (0:ℝ) < 2 / L))
  rw [show (2:ℝ) / L * (L / 2 * ∑ n ∈ Finset.range N, (2 * π * (n:ℝ) / L) ^ 2
      * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2)
      = ∑ n ∈ Finset.range N, (2 * π * (n:ℝ) / L) ^ 2
        * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2 from by field_simp] at h3
  exact h3

/-- **The coefficient mass converges.** -/
theorem summable_abs (hL : 0 < L) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g') :
    Summable (fun n : ℕ => |Cvs.Finite.WindowCosineBessel.coef L g n|) := by
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  have hsq := summable_sq hL hgd hg'c
  rw [← ha] at hsq
  -- shift past the constant mode, where the weight vanishes
  refine (summable_nat_add_iff 1).mp ?_
  have hpser : Summable (fun n : ℕ => (L / (2 * π * (n + 1))) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h := (summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      refine ((summable_nat_add_iff 1).mpr h).congr (fun n => ?_)
      push_cast
      ring
    have := hbase.mul_left ((L / (2 * π)) ^ 2)
    refine this.congr (fun n => ?_)
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp
  have hshift : Summable (fun n : ℕ => (2 * π * ((n : ℕ) + 1) / L) ^ 2 * a (n + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr hsq
    refine this.congr (fun n => ?_)
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (((hshift.add hpser)).mul_left (1 / 2))
  -- the arithmetic-geometric mean bound
  have hω : (0:ℝ) < 2 * π * ((n : ℕ) + 1) / L := by
    have : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hpi := Real.pi_pos
    positivity
  have hprod : |a (n + 1)| = (2 * π * ((n : ℕ) + 1) / L * |a (n + 1)|)
      * (L / (2 * π * ((n : ℕ) + 1))) := by
    field_simp
  rw [hprod]
  have hamgm := two_mul_le_add_sq (2 * π * ((n : ℕ) + 1) / L * |a (n + 1)|)
    (L / (2 * π * ((n : ℕ) + 1)))
  have hsq1 : (2 * π * ((n : ℕ) + 1) / L * |a (n + 1)|) ^ 2
      = (2 * π * ((n : ℕ) + 1) / L) ^ 2 * a (n + 1) ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [hsq1] at hamgm
  linarith

end Cvs.Finite.CoefficientMassFinite
