import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form of a spine vector is minus its own tail pairing

At `80 ≤ 2πx`, `Q(k_G) = −weilθ(τ_reg, G_x)`, with `G_x` the spine window at `1/x` and `τ_reg` the
regularised full tail of the spine profile: `SpineCouplingTailPairing`'s coupling identity on the diagonal.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.Approximant.SpineFormOwnTailPairing

open Cvs.WeilForm.ThetaSpaceParseval (weilθ)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.WindowFormTailLimit (Tame regProfile)

theorem scale_inv {x : ℕ} (hx : 80 ≤ 2 * π * x) : 2 * π / (2 * π * x) = 1 / (x : ℝ) := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  field_simp

/-- The spine window at `1/x` is tame on `[1/x, 1]`. -/
theorem tame_spineWindow {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Tame (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (1 / x) 1 := by
  have h := Cvs.Approximant.SpineSubspace.tame_spine hx (Cvs.Approximant.SpineSubspace.SF_lt x) a
  rwa [scale_inv hx] at h

/-- The spine class is the translated class of its own window. -/
theorem spineMap_eq_wv {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.Approximant.SpineSubspace.spineMap x a = Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (tame_spineWindow hx a) := by
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  refine (Cvs.Approximant.SpineSubspace.coe_spineMap_ae x hx a).trans (Filter.EventuallyEq.trans ?_
    (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (tame_spineWindow hx a)).symm)
  refine Filter.Eventually.of_forall fun s => ?_
  simp only [Cvs.Approximant.SpineSubspace.kG, Cvs.Approximant.SpineCouplingTailPairing.fv, scale_inv hx]

/-- **The window form of a spine vector is minus its own tail pairing**:
`Q(k_G) = −weilθ(τ_reg, G_x)` at `80 ≤ 2πx`, with `P = x`, `R = ⌈log₂ x⌉`. -/
theorem Q_spineMap_eq_neg_tail {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a)
      = -weilθ (fullTail (psi (2 * π * x)
          (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
          (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  conv_lhs => arg 2; rw [spineMap_eq_wv hx a]
  exact Cvs.Approximant.SpineCouplingTailPairing.QWbil_spineMap_eq_neg_tail hx a (tame_spineWindow hx a)

end Cvs.Approximant.SpineFormOwnTailPairing
