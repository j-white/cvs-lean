import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.CompactTestModulusSquared
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.NonnegTestPoleChannel
import Cvs.Zeta.ExplicitFormula.PoleTermsCancelCritical
import Cvs.Zeta.ExplicitFormula.PrimeChannelFiniteSum

/-!
# The pole channel of a real window test, as a product of two exponential moments

    ofCritical (sqTransform L f) 1 = (∫₀^L e^{−s/2}f)·(∫₀^L e^{s/2}f)

together with the evenness of `‖Ŵ‖²` in the frequency and the passage from the interval
integral to an integral of the truncation over the line.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments
open Cvs.Detection

/-- **The density is even in the frequency.** -/
theorem norm_windowTransform_sq_neg (L : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    ‖Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (-(y : ℝ))‖ ^ 2
      = ‖Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) ((y : ℝ))‖ ^ 2 := by
  rw [← Cvs.Detection.windowTransform_conj]
  simp

/-- **The pole channel's residue is the product of the two exponential moments.** -/
theorem ofCritical_sqTransform_one (L : ℝ) (f : ℝ → ℝ) :
    Cvs.Zeta.ofCritical (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))) 1
      = (((∫ s in (0 : ℝ)..L, Real.exp (-s / 2) * f s)
            * (∫ s in (0 : ℝ)..L, Real.exp (s / 2) * f s) : ℝ) : ℂ) := by
  rw [Cvs.Detection.ofCritical_one, show (-I * (1 / 2 : ℂ)) = -(I / 2) from by ring,
    Cvs.Detection.sqTransform, show -(-(I / 2)) = I / 2 from by ring,
    Cvs.Detection.windowTransform_at_neg_half, Cvs.Detection.windowTransform_at_pos_half,
    ← Complex.ofReal_mul]

/-- A weight against the truncation is the weight against the test, on the window. -/
theorem integral_truncate_mul (L : ℝ) (hL : 0 ≤ L) (w f : ℝ → ℝ) :
    (∫ s : ℝ, w s * Set.indicator (Set.Ioc 0 L) f s)
      = ∫ s in (0 : ℝ)..L, w s * f s := by
  have hpt : (fun s : ℝ => w s * Set.indicator (Set.Ioc 0 L) f s)
      = Set.indicator (Set.Ioc 0 L) (fun s => w s * f s) := by
    funext s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) L
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  rw [hpt, MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le hL]

end Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments
