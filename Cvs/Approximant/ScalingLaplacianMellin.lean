import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The scaling Laplacian `−(θ + ½)²` against the Mellin kernel `V^{−1/2−z}`

With `θ = V d/dV`, `(θ + ½)V^{−1/2−z} = −z V^{−1/2−z}`, so on `[a, b] ⊂ (0, ∞)` and for `G` twice differentiable
with integrable second derivative, `∫ ((θ + ½)²G − z²G) V^{−1/2−z} dV = B(b) − B(a)` with the boundary form
`B(V) = V^{1/2−z}((θ + ½)G + zG)(V)`. At `z = iω` this is `ω² ∫ G V^{−1/2−iω} = ∫ (−(θ + ½)²G) V^{−1/2−iω} + B(b) − B(a)`.
-/

noncomputable section

open Complex MeasureTheory Set intervalIntegral

namespace Cvs.Approximant.ScalingLaplacianMellin

/-- `(θ + ½)G = V G′ + G/2`, with `G₁` standing for `G′`. -/
def scal (G G₁ : ℝ → ℂ) (V : ℝ) : ℂ := (V : ℂ) * G₁ V + G V / 2

/-- `(θ + ½)²G = V²G″ + 2V G′ + G/4`, with `G₁, G₂` standing for `G′, G″`. -/
def scal2 (G G₁ G₂ : ℝ → ℂ) (V : ℝ) : ℂ := (V : ℂ) ^ 2 * G₂ V + 2 * (V : ℂ) * G₁ V + G V / 4

/-! ### The cell transform of the E-window -/

end Cvs.Approximant.ScalingLaplacianMellin
