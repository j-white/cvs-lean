import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two factors `p_i/D⁰` of the hierarchy for mode pairs `≥ 2`, and their derivatives

For the pair `(m, m')` with `s = m²`, `t = m'²`, the `χ`-free cross coefficient is
`D⁰ = c²θ²(t − s)(t + s − stθ²)`, and the two factors are `g₁ = (sθ² − 1)/D⁰`, `g₂ = (tθ² − 1)/D⁰`. On `θ ≥ 1` with
`s ≥ 4`, `t ≥ s + 5`: `|g₁| ≤ s/(c²(t − s)(st − t − s))`, and `g₁' = 2θ(s²tθ⁴ − 2stθ² + t + s)/(c²(t − s)θ⁴(t + s − stθ²)²)`
with `|g₁'| ≤ 2(s²t + t + s)/(c²(t − s)(st − t − s)²)`; the same for `g₂` with `t` in place of the leading `s`.
-/

namespace Cvs.L2a.HierarchyModePairFactors

open Real

/-- The `χ`-free cross coefficient, `D⁰ = c²θ²(t − s)(t + s − stθ²)`. -/
def D0 (c s t θ : ℝ) : ℝ := c ^ 2 * θ ^ 2 * (t - s) * (t + s - s * t * θ ^ 2)

end Cvs.L2a.HierarchyModePairFactors
