import Mathlib
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-!
# A simple ground state is even or odd, and even when a minimiser has a sign

    simple   ⟹   `reflD η = η ∨ reflD η = −η`
    simple, some minimiser `ψ ≠ 0` with `ψ ≥ 0` a.e.   ⟹   `reflD η = η`

the reflection being an isometric involution that preserves the form.
-/

noncomputable section

open MeasureTheory Measure

namespace Cvs.WeilForm.SimpleGroundEvenOrOdd

theorem reflD_smul {L : ℝ} (hL : 0 ≤ L) (c : ℝ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (c • φ) = c • Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ := by
  apply Subtype.ext; apply Subtype.ext
  exact Cvs.WeilForm.WindowReflectionSymmetry.refl_smul L c _

end Cvs.WeilForm.SimpleGroundEvenOrOdd
