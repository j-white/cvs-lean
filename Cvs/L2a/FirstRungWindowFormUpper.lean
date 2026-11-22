import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.JointGapConnesFromL1

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form of the first rung is at most `1/(10x)`

For `c = 2πx ≥ c₀^W` and `r₁ = rungs x ⟨1, _⟩` (the class of `h₄ − α₁h₀`):
`QW(r₁, r₁) = weilForm x ⌈log₂ x⌉ (logScale (window (1/x) (h₄ − α₁h₀))) ≤ qFactor x · h₄(1)²`,
`h₄(1)² ≤ 100c⁴e^{−c/16}`, and `qFactor x · 100c⁴e^{−c/16} ≤ 1/(10x)`.
-/

noncomputable section

open Real

namespace Cvs.L2a.FirstRungWindowFormUpper
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.L2a.ProlateFamilySpine (kOf)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.JointGapConnesFromL1 (one₁)

/-- The spine profile of the coordinate vector at `1 ∈ SF x` is the spine profile of `one₁` on `{1}`. -/
theorem spineG_single_one (c : ℝ) {x : ℕ} (h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x) :
    spineG c (Pi.single (⟨1, h1⟩ : Cvs.Approximant.SpineSubspace.SF x) (1 : ℝ)) = spineG c (S := {1}) one₁ := by
  funext s
  rw [show spineG c (S := {1}) one₁ s = _ from Cvs.Approximant.SpineNearQuarticHermite.spineG_one c s]
  unfold spineG
  rw [Finset.sum_eq_single (⟨1, h1⟩ : Cvs.Approximant.SpineSubspace.SF x)]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Cvs.L2a.FirstRungWindowFormUpper
