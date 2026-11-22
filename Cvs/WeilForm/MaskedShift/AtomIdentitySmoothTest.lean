import Mathlib
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped InnerProductSpace NNReal ContDiff

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.Operator Cvs.Operator

/-!
# The identity at a genuine smooth test function

B47 states the identity for every `f ∈ L²(𝕋)`, but its test function `weilTest c f` is built
from `lift`, an indicator, so it is not `ContDiff` and is not admissible in
`Cvs.Zeta.Explicit.Weil.WeilPositivity`.
-/

variable {g : ℝ → ℝ}

/-- A test function on the interval, read on the circle through `rep`. -/
noncomputable def circleVal (g : ℝ → ℝ) : T1 → ℝ := fun z => g (rep z)

/-- The self-convolution depends only on the almost-everywhere class. -/
theorem selfConvolution_congr_ae {h h' : ℝ → ℝ} (hae : h =ᵐ[volume] h') :
    selfConvolution h = selfConvolution h' := by
  funext t
  refine integral_congr_ae ?_
  have hshift : (fun x : ℝ => h (x + t)) =ᵐ[volume] fun x : ℝ => h' (x + t) :=
    (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae_eq_comp hae
  filter_upwards [hae, hshift] with x hx hxt
  rw [hx, hxt]

/-! ## The smooth test function -/

/-- The rescaled test function: literally smooth, literally compactly
supported. -/
noncomputable def smoothTest (c : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun y => g (y / Real.log c) / Real.sqrt (Real.log c)

end Cvs.PrimeOperator
