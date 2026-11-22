import Mathlib
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.PrimeChannelFiniteSum
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine
import Cvs.Zeta.FourierShift

/-!
# The prime side is a finite sum
-/

namespace Cvs.Detection

open Complex MeasureTheory ArithmeticFunction FourierTransform
open scoped Real

/-- **The prime side is a finite sum.** -/
theorem primeSide_eq_sum {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2) :
    Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.primeSide (Cvs.Detection.sqTransform L f)
      = ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
          (Λ n : ℂ) * (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
            * Cvs.Zeta.fourierReal (Cvs.Detection.sqTransform L f) (Real.log n) := by
  rw [Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.primeSide]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hge : Real.exp L ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hn
  rw [Cvs.Detection.fourierReal_log_eq_zero hL hf h0 hLz hC hbd hge, mul_zero]

end Cvs.Detection
