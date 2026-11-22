import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# The integral term, bounded below
-/

namespace Cvs.Deficit

open MeasureTheory

theorem measurable_psi : Measurable Chebyshev.psi :=
  Chebyshev.psi_mono.measurable

/-- The weighted `ψ` is integrable on `[1,x]`: monotone hence measurable,
bounded by `ψ(x)`. -/
theorem integrableOn_psi_weighted (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (-(3:ℝ)/2) * Chebyshev.psi t) (Set.Ioc 1 x) := by
  refine Measure.integrableOn_of_bounded (M := Chebyshev.psi x) measure_Ioc_lt_top.ne ?_ ?_
  · have hm : Measurable (fun t : ℝ => t ^ (-(3:ℝ)/2) * Chebyshev.psi t) := by
      refine Measurable.mul ?_ measurable_psi
      fun_prop
    exact hm.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    obtain ⟨ht1, ht2⟩ := ht
    have ht0 : (0:ℝ) < t := by linarith
    have hpsi : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have hmono : Chebyshev.psi t ≤ Chebyshev.psi x := Chebyshev.psi_mono ht2
    have hrpow : t ^ (-(3:ℝ)/2) ≤ 1 := by
      rw [show (-(3:ℝ)/2) = -((3:ℝ)/2) by ring, Real.rpow_neg ht0.le]
      rw [inv_le_one_iff₀]
      right
      exact Real.one_le_rpow (by linarith) (by norm_num)
    have hrpow0 : 0 ≤ t ^ (-(3:ℝ)/2) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith

end Cvs.Deficit
