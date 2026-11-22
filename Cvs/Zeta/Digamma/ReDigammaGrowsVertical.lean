import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Digamma.DigammaProductDerivative
import Cvs.Zeta.Digamma.ReDigammaVerticalDominates

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Complex Filter Topology Real

namespace Cvs.GaussKernel

/-!
# `Re ψ` grows on a vertical line
-/

/-- The real part of the `n`-th term of `B95`'s series at `x + iy`. -/
theorem term_re (x y : ℝ) (n : ℕ) :
    (1 / ((n : ℂ) + 1) - 1 / (((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ) + 1)).re
      = 1 / ((n : ℝ) + 1) - (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y ^ 2) := by
  rw [Complex.sub_re]
  congr 1
  · rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring]
    exact Cvs.Digamma.re_inv_ofReal
  · rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have hre : (((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ) + 1).re = x + (n : ℝ) + 1 := by
      simp
    have him : (((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ) + 1).im = y := by
      simp
    rw [hre, him]
    ring_nf

/-- **The series at `x + iy`, with real terms.** -/
theorem hasSum_re_line {x y : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)
        - (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y ^ 2))
      ((Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)).re
        + Real.eulerMascheroniConstant + x / (x ^ 2 + y ^ 2)) := by
  have hzre : (((x : ℂ) + (y : ℂ) * Complex.I)).re = x := by simp
  have hz : (0 : ℝ) < (((x : ℂ) + (y : ℂ) * Complex.I)).re := by rw [hzre]; exact hx
  have h := Complex.hasSum_re (Cvs.Digamma.hasSum_digamma hz)
  have hval : (Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)
      + (Real.eulerMascheroniConstant : ℂ) + 1 / ((x : ℂ) + (y : ℂ) * Complex.I)).re
      = (Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)).re
        + Real.eulerMascheroniConstant + x / (x ^ 2 + y ^ 2) := by
    rw [Complex.add_re, Complex.add_re, Complex.ofReal_re, one_div, Complex.inv_re,
      Complex.normSq_apply]
    congr 1
    rw [hzre]
    have him : (((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
    rw [him]
    ring_nf
  rw [hval] at h
  have hfun : (fun n : ℕ => 1 / ((n : ℝ) + 1)
        - (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y ^ 2))
      = fun n : ℕ => (1 / ((n : ℂ) + 1)
        - 1 / (((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ) + 1)).re :=
    funext fun n => (term_re x y n).symm
  rw [hfun]
  exact h

end Cvs.GaussKernel
