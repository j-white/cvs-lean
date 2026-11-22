import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.RecentredTransformClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisWitnessSymmetry
import Cvs.Limit.SpineWithoutSimplicity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The recentred transform is even off the axes

Off both coordinate axes the recentred ground-state transform takes the same value at `z` and at
`-z`, since in the closed form of `Cvs.Finite.RecentredTransformClosed` the factor `-2 z` and the sine are each odd while the
rational factor of `Cvs.Finite.UniversalFunctionPairing` depends on `z` through `z ^ 2`.
-/

noncomputable section

open Complex

namespace Cvs.Finite.RecentredTransformEven
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit

/-- A real frequency never cancels a point off the axes, the imaginary part surviving. -/
theorem omega_add_ne_zero {ι : Type*} {L : ℝ} {mode : ι → ℤ} {z : ℂ} (hz : z ∈ offAxes) (i : ι) :
    ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z ≠ 0 := by
  intro h
  refine hz.2 ?_
  have him := congrArg Complex.im h
  simpa using him

/-- **The recentred ground-state transform is even off the axes.** -/
theorem cgtransform_neg (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {z : ℂ} (hz : z ∈ offAxes) :
    Cvs.Finite.RecentredTransform.cgtransform P R hL N (-z)
      = Cvs.Finite.RecentredTransform.cgtransform P R hL N z := by
  rw [Cvs.Finite.RecentredTransformClosed.cgtransform_eq_sin P R hL N
      (fun i => omega_add_ne_zero (Cvs.Limit.OffAxisWitnessSymmetry.neg_mem_offAxes hz) i),
    Cvs.Finite.RecentredTransformClosed.cgtransform_eq_sin P R hL N (fun i => omega_add_ne_zero hz i),
    show (-z) * (L : ℂ) / 2 = -(z * (L : ℂ) / 2) by ring,
    Complex.sin_neg, Cvs.Finite.UniversalFunctionPairing.S_neg]
  ring

end Cvs.Finite.RecentredTransformEven
