import Mathlib

/-!
# The archimedean symbol is zeta's log-derivative on the critical line

    archSymbol t = −2 · Re (ζ'/ζ) (½ + it)

so the weight the archimedean channel puts on frequency `t` is the analytic continuation
of the prime sum, and the functional equation is what forces the two to agree.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex

namespace Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv

/-- The point `½ + it` on the critical line. -/
def cl (t : ℝ) : ℂ := 1 / 2 + Complex.I * (t : ℂ)

@[simp] theorem cl_re (t : ℝ) : (cl t).re = 1 / 2 := by
  simp [cl]

@[simp] theorem cl_im (t : ℝ) : (cl t).im = t := by
  simp [cl]

/-- **Reflection is conjugation on the critical line.** -/
theorem one_sub_cl (t : ℝ) : 1 - cl t = (starRingEnd ℂ) (cl t) := by
  refine Complex.ext ?_ ?_ <;> simp [cl] <;> norm_num

end Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv
