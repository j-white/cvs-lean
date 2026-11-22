import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ModeTailFromEquationBelowPlunge
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a for the tail of an angular prolate, for every `χ ≤ (1 − ℓ)c²`

If `g` solves the angular equation on `[−1, 1]`, its cosine transform `ψ(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds` solves the
radial one (Cvs.Prolate.SlepianCommutingRelation), so Cvs.L2a.ModeTailFromEquationBelowPlunge applies: for fixed `0 < ℓ ≤ 1`, `0 ≤ χ`, `ℓc² ≤ c² − χ` and `ψ(1) ≠ 0`, the Weil form
of every tail of `M` modes of `ψ` is eventually positive.
-/

namespace Cvs.L2a.AngularTailPositiveBelowPlunge

open Real Set MeasureTheory Filter Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes
open Cvs.L2a.AngularProlateTailPositive (psi psi_system)

/-- **L2a for the tail of an angular prolate, for every `χ ≤ (1 − ℓ)c²`.** -/
theorem weilForm_eventually_pos (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (Kf : ℕ) (hKf : 1 ≤ Kf) :
    ∀ᶠ c in atTop, ∀ (χ Ξ : ℝ) (g g₁ g₂ : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → ℓ * c ^ 2 ≤ c ^ 2 - χ →
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) → (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) →
      ContinuousOn g₂ (uIcc (-1) 1) →
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) →
      psi c g 1 ≠ 0 →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (psi c g) M (2 ^ (J + 1)))) := by
  filter_upwards [Cvs.L2a.ModeTailFromEquationBelowPlunge.weilForm_tailF_eventually_pos ℓ hℓ0 hℓ1 Kf hKf] with c hc
  intro χ Ξ g g₁ g₂ P R N M J hχ0 hχs hg hg₁ hg₂c hang hψ1 hJ hM hΞ hidx hrb
  obtain ⟨h1, h2, h3⟩ := psi_system hg hg₁ hg₂c hang
  exact hc χ Ξ (psi c g) _ _ P R N M J hχ0 hχs (fun r _ => h1 r) (fun r _ => h2 r) (fun r _ => h3 r) hψ1
    hJ hM hΞ hidx hrb

end Cvs.L2a.AngularTailPositiveBelowPlunge
