import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Route.GroundRouteJointGap

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH from the joint gap at Connes' vectors

Connes' vectors are strip approximable for every truncation eventually at least `⌈x^{1/4}⌉`, so
the joint gap at `K = √x log x` against them, for such a truncation and arbitrarily large `x`,
gives RH.
-/

noncomputable section

open Filter

namespace Cvs.Route.JointGapAtConnesVectors
open Cvs.ZeroCounting

/-- The truncation threshold `⌈x^{1/4}⌉` for Connes' vectors. -/
def connesThreshold (x : ℝ) : ℕ := ⌈x ^ (1 / 4 : ℝ)⌉₊

/-- Every truncation eventually at least `connesThreshold` gives strip approximable Connes'
vectors. -/
theorem stripApproximable_connesVec_of_threshold_le (N : ℝ → ℕ)
    (hN : ∀ᶠ x in atTop, connesThreshold x ≤ N x) :
    Cvs.Route.GroundRouteJointGap.StripApproximable N (Cvs.Approximant.ConnesVectorRealScale.connesVec N) :=
  Cvs.Approximant.SpineNearQuarticHermite.stripApproximable_connesVec N hN

/-- **Strip approximability of Connes' vectors**: some threshold `N₀` makes every truncation
eventually at least `N₀` strip approximable. -/
theorem stripApproximable_connesVec : ∃ N₀ : ℝ → ℕ, ∀ N : ℝ → ℕ,
    (∀ᶠ x in atTop, N₀ x ≤ N x) → Cvs.Route.GroundRouteJointGap.StripApproximable N (Cvs.Approximant.ConnesVectorRealScale.connesVec N) :=
  ⟨connesThreshold, stripApproximable_connesVec_of_threshold_le⟩

/-- **RH from the joint gap at Connes' vectors**: a truncation eventually at least
`connesThreshold` with the joint gap at `K = √x log x` against Connes' vector for arbitrarily
large `x` gives RH. -/
theorem riemannHypothesis_of_jointGap_connes (P R : ℝ → ℕ)
    (hgap : ∃ N : ℝ → ℕ, (∀ᶠ x in atTop, connesThreshold x ≤ N x) ∧
      ∃ᶠ x in atTop, Cvs.Route.GroundRouteJointGap.JointGap (P x) (R x) (Real.log x) (N x) (√x * Real.log x)
        (Cvs.Approximant.ConnesVectorRealScale.connesVec N x)) :
    RiemannHypothesis := by
  obtain ⟨N, hN, hJ⟩ := hgap
  exact Cvs.Route.GroundRouteJointGap.riemannHypothesis_of_frequently_jointGap P R N (Cvs.Approximant.ConnesVectorRealScale.connesVec N)
    (stripApproximable_connesVec_of_threshold_le N hN) hJ

end Cvs.Route.JointGapAtConnesVectors
