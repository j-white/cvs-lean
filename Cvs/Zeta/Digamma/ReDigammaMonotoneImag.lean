import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Digamma.ReDigammaGrowsVertical

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
# `Re ψ` is monotone in `|y|`

`B96` compares `Re ψ(x+iy)` with its value on the axis; `ReDigammaGrowsVertical` gives a growing lower bound at
a free truncation.
-/

/-- **`Re ψ(x+iy)` increases in `|y|`.** -/
theorem re_digamma_mono {x y₁ y₂ : ℝ} (hx : 0 < x) (hy : y₁ ^ 2 ≤ y₂ ^ 2) :
    (Complex.digamma ((x : ℂ) + (y₁ : ℂ) * Complex.I)).re
      ≤ (Complex.digamma ((x : ℂ) + (y₂ : ℂ) * Complex.I)).re := by
  have h1 := Cvs.GaussKernel.hasSum_re_line (x := x) (y := y₁) hx
  have h2 := Cvs.GaussKernel.hasSum_re_line (x := x) (y := y₂) hx
  have hterm : ∀ n : ℕ,
      1 / ((n : ℝ) + 1) - (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y₁ ^ 2)
        ≤ 1 / ((n : ℝ) + 1) - (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y₂ ^ 2) := by
    intro n
    have hp : (0 : ℝ) < x + (n : ℝ) + 1 := by positivity
    have hd1 : (0 : ℝ) < (x + (n : ℝ) + 1) ^ 2 + y₁ ^ 2 := by positivity
    have hd2 : (0 : ℝ) < (x + (n : ℝ) + 1) ^ 2 + y₂ ^ 2 := by positivity
    have hkey : (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y₂ ^ 2)
        ≤ (x + (n : ℝ) + 1) / ((x + (n : ℝ) + 1) ^ 2 + y₁ ^ 2) := by
      rw [div_le_div_iff₀ hd2 hd1]
      nlinarith
    linarith
  have hle := hasSum_le hterm h1 h2
  have hpre : x / (x ^ 2 + y₂ ^ 2) ≤ x / (x ^ 2 + y₁ ^ 2) := by
    have hd1 : (0 : ℝ) < x ^ 2 + y₁ ^ 2 := by positivity
    have hd2 : (0 : ℝ) < x ^ 2 + y₂ ^ 2 := by positivity
    rw [div_le_div_iff₀ hd2 hd1]
    nlinarith
  linarith

end Cvs.GaussKernel
