import Mathlib
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-!
# The second value of the even sector, and the plane hypothesis

Restricting the kernel operator to the even classes orthogonal to an eigenvector bounds the
truncated form on a subspace of codimension one, and a dimension count turns that bound into the
plane hypothesis that step (a) consumes.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Cvs.WeilForm.EvenSectorSecondValue

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

variable {L : ℝ}

/-! ### The even classes orthogonal to a vector -/

/-! ### The restricted operator -/

/-! ### The form on the orthogonal complement -/

/-! ### The plane hypothesis -/

/-- **A plane of even classes meets the orthogonal complement of any vector.** -/
theorem exists_mem_perp {hL : 0 ≤ L} (ζ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    (V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL))
    (h2 : Module.finrank ℝ V = 2) :
    ∃ v ∈ V, v ≠ 0 ∧
      (inner ℝ ζ ((v : Cvs.WeilForm.FormDomain.formDomain hL) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ) = 0 := by
  let instG : AddCommGroup ↥V :=
    @Submodule.addCommGroup ℝ _ _ (Submodule.addCommGroup _) _ V
  have : FiniteDimensional ℝ ↥V := FiniteDimensional.of_finrank_pos (by rw [h2]; norm_num)
  set f : ↥V →ₗ[ℝ] ℝ :=
    ((innerSL ℝ ζ).toLinearMap.comp (Cvs.WeilForm.FormDomain.formDomain hL).subtype).comp V.subtype
    with hf
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    have h := Submodule.finrank_le (LinearMap.range f)
    simpa using h
  have hker : 0 < Module.finrank ℝ (LinearMap.ker f) := by
    rw [h2] at hrk
    omega
  have hbot : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h] at hker
    simp at hker
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨(x : Cvs.WeilForm.FormDomain.formDomain hL), x.2, ?_, ?_⟩
  · intro h0
    exact hx0 (Subtype.ext h0)
  · have hfx : f x = 0 := LinearMap.mem_ker.mp hx
    simpa [hf] using hfx

/-- **The plane hypothesis of step (a) from a bound on one orthogonal complement.** -/
theorem hplane_of_perp_bound {hL : 0 ≤ L} (N P R : ℕ) {mu2 : ℝ}
    (ζ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    (hbd : ∀ χ : Cvs.WeilForm.WeilFormOnWindowL2.window L, Cvs.WeilForm.WindowReflectionSymmetry.reflW χ = χ →
      (inner ℝ ζ χ : ℝ) = 0 →
      mu2 * ‖χ‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R χ)
    (V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL))
    (h2 : Module.finrank ℝ V = 2)
    (hV : V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R
      (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
  obtain ⟨v, hvV, hv0, hperp⟩ := exists_mem_perp (hL := hL) ζ V h2
  refine ⟨v, hvV, hv0, ?_⟩
  have heven : Cvs.WeilForm.WindowReflectionSymmetry.reflW (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
    have hmem : v ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL := hV hvV
    have hD : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL v = v := hmem
    exact congrArg (fun w : Cvs.WeilForm.FormDomain.formDomain hL =>
      (w : Cvs.WeilForm.WeilFormOnWindowL2.window L)) hD
  have hnorm : ‖v‖ = ‖(v : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ := (Submodule.norm_coe v).symm
  rw [hnorm]
  exact hbd _ heven hperp

end Cvs.WeilForm.EvenSectorSecondValue
