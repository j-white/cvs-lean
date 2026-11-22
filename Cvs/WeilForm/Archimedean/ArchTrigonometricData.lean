import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged

/-!
# The window form's archimedean term, on trigonometric data

    archSymbol 0 · g 0 + ∫₀^∞ ρ(u)·(g 0 − g (u/2)) du = ∑ⱼ cⱼ · archSymbol tⱼ

for `g v = ∑ⱼ cⱼ cos (tⱼ v)`: the position-space Lévy energy of `Cvs.WeilForm.SelfConvolutionFunctional`'s form is the
explicit formula's archimedean weight, read at each frequency the data carries.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.Archimedean.ArchTrigonometricData

open Cvs.WeilForm.Archimedean.LevyDensity Cvs.WeilForm.Archimedean.LevyMeasure

/-- The Lévy integrand at frequency `t`. -/
def levyIntegrand (t u : ℝ) : ℝ := (1 - Real.cos (t / 2 * u)) * densityU u

/-- **The cosine deficit obeys the Lévy condition.**  Quadratic at the origin, bounded
away from it, so the same `min 1 u²` dominates it at every frequency. -/
theorem one_sub_cos_le (t u : ℝ) :
    1 - Real.cos (t / 2 * u) ≤ (2 + t ^ 2 / 8) * min 1 (u ^ 2) := by
  have hq : 1 - Real.cos (t / 2 * u) ≤ (t / 2 * u) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := t / 2 * u); linarith
  have h2 : 1 - Real.cos (t / 2 * u) ≤ 2 := by
    have := Real.neg_one_le_cos (t / 2 * u); linarith
  rcases le_or_gt 1 (u ^ 2) with h | h
  · rw [min_eq_left h]
    nlinarith [sq_nonneg t]
  · rw [min_eq_right h.le]
    have hq' : 1 - Real.cos (t / 2 * u) ≤ t ^ 2 * u ^ 2 / 8 := by
      have hexp : (t / 2 * u) ^ 2 / 2 = t ^ 2 * u ^ 2 / 8 := by ring
      rw [hexp] at hq; exact hq
    nlinarith [sq_nonneg u]

/-- **The integrand is integrable at every frequency.** -/
theorem integrableOn_levyIntegrand (t : ℝ) :
    IntegrableOn (levyIntegrand t) (Ioi (0:ℝ)) := by
  have hdom : IntegrableOn
      (fun u => (2 + t ^ 2 / 8) * (min 1 (u ^ 2) * densityU u)) (Ioi (0:ℝ)) :=
    integrableOn_min_mul_densityU.const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · have hmeas : Measurable (levyIntegrand t) := by
      unfold levyIntegrand
      exact (measurable_const.sub
        (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id))).mul
        measurable_densityU
    exact hmeas.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : (0:ℝ) < u := hu
    have hd : 0 ≤ densityU u := (densityU_pos hu0).le
    have hnn : 0 ≤ levyIntegrand t u := by
      have h1 : 0 ≤ 1 - Real.cos (t / 2 * u) := by
        have := Real.cos_le_one (t / 2 * u); linarith
      exact mul_nonneg h1 hd
    rw [Real.norm_of_nonneg hnn]
    unfold levyIntegrand
    calc (1 - Real.cos (t / 2 * u)) * densityU u
        ≤ ((2 + t ^ 2 / 8) * min 1 (u ^ 2)) * densityU u :=
          mul_le_mul_of_nonneg_right (one_sub_cos_le t u) hd
      _ = (2 + t ^ 2 / 8) * (min 1 (u ^ 2) * densityU u) := by ring

/-- **The integral is the symbol's increment.**  `Cvs.Zeta.DigammaLimitDischarged`, in the form the window form uses. -/
theorem integral_levyIntegrand (t : ℝ) :
    (∫ u in Ioi (0:ℝ), levyIntegrand t u)
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 := by
  unfold levyIntegrand Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  rw [Cvs.Zeta.DigammaLimitDischarged.integral_rep t]
  ring

variable {ι : Type*}

end Cvs.WeilForm.Archimedean.ArchTrigonometricData
