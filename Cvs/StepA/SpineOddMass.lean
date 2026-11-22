import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The odd mass of a spine class, and the odd-defect floor in tail form

For `v_a = spineMap x a` with spine window `W_a` and its reciprocal reflection `R W_a(θ) = (√a/θ)W_a(a/θ)`,
`a = 1/x`, the odd part has the zero- and prime-free mass `‖o_a‖² = ¼∫(W_a − RW_a)²`. With `EvenSectorReflectionBound`'s
`Q(e_a) = (tailQ + reflQ)/2`, the odd-defect floor `c₁‖o_a‖² ≤ Q(e_a)` is the explicit tail inequality
`c₁∫(W_a − RW_a)² ≤ 2(tailQ x a + reflQ x a)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.StepA.SpineOddMass
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)

/-- The spine window `W_a = window(1/x)(G_a)`. -/
abbrev spineW (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ → ℝ :=
  window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)

/-- The odd window `W_a − R_{1/x}W_a`. -/
def oddW (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) : ℝ :=
  spineW x a θ - reciprocal (1 / x) (spineW x a) θ

end Cvs.StepA.SpineOddMass
