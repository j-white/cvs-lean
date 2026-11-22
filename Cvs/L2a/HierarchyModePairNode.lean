import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyModePairFactors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The node of the hierarchy for a mode pair `≥ 2`, in absolute value

For the dilated systems of a mode pair `(m, m')`, `s = m²`, `t = m'²` (`f₁' = u₁/(sθ² − 1)`,
`u₁' = −c²s²θ²f₁ + r₁`, and the same with `t`), and a `C¹` weight `σ` on `[1, b]`, the cross identity with sources
(Cvs.Upstream.SturmCrossIdentitySources, Cvs.L2a.CrossIntegralAbsBound) holds with `D = D⁰`, `α = σ'g₁ + σg₁'`, `β = σ'g₂ + σg₂'` (the factors of Cvs.L2a.HierarchyModePairFactors, an earlier result):
`|∫₁ᵇ σ f₁f₂|` is at most the boundary term, the two `fu` terms and the source term, all explicit.
-/

namespace Cvs.L2a.HierarchyModePairNode

open Real Set intervalIntegral Cvs.L2a.HierarchyModePairFactors

/-- The first factor `g₁ = (sθ² − 1)/D⁰` and its derivative, as functions. -/
noncomputable def g₁ (c s t θ : ℝ) : ℝ := (s * θ ^ 2 - 1) / D0 c s t θ
noncomputable def g₁' (c s t θ : ℝ) : ℝ :=
  2 * θ * (s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s) / (c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2)
/-- The second factor `g₂ = (tθ² − 1)/D⁰` and its derivative. -/
noncomputable def g₂ (c s t θ : ℝ) : ℝ := (t * θ ^ 2 - 1) / D0 c s t θ
noncomputable def g₂' (c s t θ : ℝ) : ℝ :=
  2 * θ * (s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s) / (c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2)

end Cvs.L2a.HierarchyModePairNode
