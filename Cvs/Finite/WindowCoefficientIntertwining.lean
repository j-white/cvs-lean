import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window coefficients as cell transforms, and the intertwining of `diag(ω²)` with `−(θ + ½)²`

`WindowCosineBessel`'s cosine coefficients of the window test `Cvs.Approximant.StripApproxFromHermite.kOf x G` at `ω_k = 2πk/log x` are `ν_k x^{−1/2} Re C_{iω_k}(G)`,
so `ω_k² coef_k(kOf G) − coef_k(kOf(−(θ + ½)²G))` is `γ(G)e₀ + (G′(1) + G(1)/2)J₀ + G(1)J₁` for three fixed vectors,
for every `G` with continuous second derivative on `[1/x, 1]`, and iterating gives the `diag(ω²)^j` ladder.
-/

noncomputable section

open Complex MeasureTheory Set intervalIntegral

namespace Cvs.Finite.WindowCoefficientIntertwining


/-! ### The window integral as a cell transform -/

/-! ### The intertwining in `WindowCosineBessel`'s cosine coefficients -/

/-- `WindowCosineBessel`'s coefficient normalisation: `ν_0 = 1/L`, `ν_k = 2/L` for `k ≥ 1`. -/
def nu (L : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 / L else 2 / L

/-! ### The spine tests of Cvs.Approximant.SpineSubspace -/

/-! ### The defect lies in a fixed three-dimensional span -/

/-! ### Smooth profiles and the ladder -/

/-- `−(θ + ½)²G = −(V²G″ + 2VG′ + G/4)`, with `G′, G″` the derivatives of `G`. -/
def negScal2 (G : ℝ → ℝ) : ℝ → ℝ := fun V => -(V ^ 2 * deriv (deriv G) V + 2 * V * deriv G V + G V / 4)

end Cvs.Finite.WindowCoefficientIntertwining
