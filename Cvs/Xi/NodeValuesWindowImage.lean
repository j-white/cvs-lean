import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `Ξ` at the nodes is the window image of `θ(θ + 1)e^{−πxv²}`

`QuarticHermiteWindowPhi`'s quartic Hermite profile is `16 G_Ξ`, `G_Ξ = θ(θ + 1)e^{−πxv²}`, so by Cvs.Xi.XiCosineTransformPhi the cosine coefficient of
`Cvs.Approximant.StripApproxFromHermite.kOf x G_Ξ` at `ω_k = 2πk/log x` is `ν_k x^{−3/4}(−1)^k Ξ(ω_k)` up to two explicit `x^{9/4}e^{−πx}`-size
integrals, and `ω_k^{2j}` times it is the coefficient of `(−(θ + ½)²)^j G_Ξ` plus `WindowCoefficientIntertwining`'s boundary defects.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Xi.NodeValuesWindowImage


/-- The `Ξ` profile `G_Ξ(v) = (4π²x²v⁴ − 6πxv²) e^{−πxv²}`. -/
def GXi (x v : ℝ) : ℝ := (4 * (π * x) ^ 2 * v ^ 4 - 6 * (π * x) * v ^ 2) * exp (-(π * x * v ^ 2))

/-! ### Riemann's cosine integral on the window -/

/-! ### The corrections are `O(x^{9/4} e^{−πx})` -/

end Cvs.Xi.NodeValuesWindowImage
