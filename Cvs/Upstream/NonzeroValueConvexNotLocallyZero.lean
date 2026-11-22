import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One non-zero value rules out local vanishing on a convex piece

A function differentiable on a convex open subset of the plane and vanishing on a neighbourhood of
one of its points vanishes on the whole subset, so a single point where it does not vanish rules
local vanishing out everywhere on that subset.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Upstream.NonzeroValueConvexNotLocallyZero

/-- **A convex open set carrying one non-zero value carries no local vanishing.** -/
theorem not_eventually_zero_of_convex {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U)
    (hfw : f w ≠ 0) : ¬ (∀ᶠ v in 𝓝 z, f v = 0) := fun h =>
  hfw ((hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconv.isPreconnected hz h hw)

end Cvs.Upstream.NonzeroValueConvexNotLocallyZero
