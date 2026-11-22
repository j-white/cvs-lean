import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.CriticalLineDensity
import Cvs.Zeta.ExplicitFormula.FirstPoleContourShift

/-!
# On the critical line the two pole terms cancel in real part

`an earlier result` and `Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly` bound the second pole term below by discarding the residue at `z = 1`, and
`an earlier result` measured what that costs: `−277.85` against a true `+4.079`, 68× too big and the wrong
sign.
-/

namespace Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- `Re (1/((½+iy)−1)) = −(½)/(¼+y²)` — the mirror of `Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.re_one_div_half`. -/
theorem re_one_div_half_sub_one (y : ℝ) :
    ((1 : ℂ) / (1 / 2 + (y : ℝ) * I - 1)).re = -((1 / 2) / (1 / 4 + y ^ 2)) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  norm_num
  ring

theorem re_poleTwo_critical {h : ℂ → ℂ} {ρ : ℝ → ℝ}
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) (y : ℝ) :
    (Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)).re
      = -((1 / 2) / (1 / 4 + y ^ 2)) * ρ y := by
  rw [Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo, hrho y, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    re_one_div_half_sub_one]
  ring

/-- **The two pole terms cancel in real part on the critical line.**  Their sum
there is `−2iy/(¼+y²)` times a real density — purely imaginary. -/
theorem re_poleSum_critical {h : ℂ → ℂ} {ρ : ℝ → ℝ}
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) (y : ℝ) :
    (Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand h (1 / 2 + (y : ℝ) * I)
        + Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)).re = 0 := by
  rw [Complex.add_re, Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.re_poleIntegrand_critical hrho y, re_poleTwo_critical hrho y]
  ring

/-- The residue the rectangle would pick up, named: `ofCritical h 1 = h(−i/2)`. -/
theorem ofCritical_one (h : ℂ → ℂ) : Cvs.Zeta.ofCritical h 1 = h (-I * (1 / 2)) := by
  rw [Cvs.Zeta.ofCritical]
  congr 1
  ring

end Cvs.Detection
