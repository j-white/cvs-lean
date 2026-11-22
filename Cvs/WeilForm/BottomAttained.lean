import Mathlib
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.HatInFormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The bottom of the Weil form on the form domain is attained

    `∃ lam η`, `lam ‖v‖² ≤ weilQW v` for every `v` in the domain, `weilQW η = lam ‖η‖²`, `η ≠ 0`

for `0 < L`: the form is homogeneous of degree two, so its infimum on the sphere bounds it
everywhere, and the sphere minimiser attains that bound.
-/

noncomputable section

open MeasureTheory

namespace Cvs.WeilForm.BottomAttained

/-- **The form is homogeneous of degree two.** -/
theorem weilQW_smul {L : ℝ} (P R : ℕ) (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.weilQW P R (c • φ) = c ^ 2 * Cvs.WeilForm.WindowRepresentative.weilQW P R φ := by
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (c • φ)).1, (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R φ).1,
    Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R (Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae c φ),
    Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul]

theorem weilQW_zero {L : ℝ} (P R : ℕ) :
    Cvs.WeilForm.WindowRepresentative.weilQW P R (0 : Cvs.WeilForm.WeilFormOnWindowL2.window L) = 0 := by
  have h := weilQW_smul P R 0 (0 : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  rw [zero_smul] at h
  simp only [zero_pow two_ne_zero, zero_mul] at h
  exact h

/-- The infimum of the form on the sphere. -/
def lam {L : ℝ} (hL : 0 < L) (P R : ℕ) : ℝ :=
  sInf (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' Cvs.WeilForm.InfimumAttainedSphere.sphere hL.le)

/-- The norm of the zero class, through the coercions. -/
theorem norm_zero' {L : ℝ} (hL : 0 < L) :
    ‖(0 : Cvs.WeilForm.FormDomain.formDomain hL.le)‖ = 0 := by
  show ‖(((0 : Cvs.WeilForm.FormDomain.formDomain hL.le) : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Lp ℝ 2 (volume : Measure ℝ))‖ = 0
  rw [Submodule.coe_zero, Submodule.coe_zero, norm_zero]

/-- **The sphere infimum bounds the form everywhere on the domain**, by homogeneity. -/
theorem bottom {L : ℝ} (hL : 0 < L) (P R : ℕ) (v : Cvs.WeilForm.FormDomain.formDomain hL.le) :
    lam hL P R * ‖v‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v := by
  have hbdd : BddBelow (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' Cvs.WeilForm.InfimumAttainedSphere.sphere hL.le) :=
    ⟨Cvs.WeilForm.WindowFormNormFloor.floorConst L P R, by
      rintro _ ⟨φ, hφ, rfl⟩; exact Cvs.WeilForm.InfimumAttainedSphere.floor_le_Q hL.le P R hφ⟩
  by_cases hv : v = 0
  · subst hv
    rw [norm_zero' hL, zero_pow two_ne_zero, mul_zero]
    show 0 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R ((0 : Cvs.WeilForm.FormDomain.formDomain hL.le) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L)
    rw [Submodule.coe_zero, weilQW_zero]
  · have hn : ‖((v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ≠ 0 :=
      (norm_pos_iff.mpr (by simpa [Submodule.coe_eq_zero] using hv)).ne'
    have hw : (‖v‖⁻¹ • v) ∈ Cvs.WeilForm.InfimumAttainedSphere.sphere hL.le := by
      show ‖((((‖v‖⁻¹) • v : Cvs.WeilForm.FormDomain.formDomain hL.le) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = 1
      rw [Submodule.coe_smul, Submodule.coe_smul, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg v)]
      exact inv_mul_cancel₀ hn
    have hQw : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R (‖v‖⁻¹ • v)
        = ‖v‖⁻¹ ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v := by
      show Cvs.WeilForm.WindowRepresentative.weilQW P R (((‖v‖⁻¹ • v : Cvs.WeilForm.FormDomain.formDomain hL.le) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L)) = _
      rw [Submodule.coe_smul, weilQW_smul]
    have hlam : lam hL P R ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R (‖v‖⁻¹ • v) :=
      csInf_le hbdd ⟨_, hw, rfl⟩
    rw [hQw] at hlam
    have hne : ‖v‖ ≠ 0 := hn
    have hpos : 0 < ‖v‖ ^ 2 := by positivity
    calc lam hL P R * ‖v‖ ^ 2
        ≤ (‖v‖⁻¹ ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hlam hpos.le
      _ = Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v := by field_simp

/-- **The bottom of the form is attained by a nonzero class.** -/
theorem exists_bottom_attained {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    ∃ (l : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain hL.le),
      (∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, l * ‖v‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v)
      ∧ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η = l * ‖η‖ ^ 2 ∧ η ≠ 0 := by
  obtain ⟨η, hη, hQ⟩ := Cvs.WeilForm.HatInFormDomain.exists_min hL P R
  have hn : ‖η‖ = 1 := hη
  refine ⟨lam hL P R, η, bottom hL P R, ?_, ?_⟩
  · rw [hn, one_pow, mul_one]; exact hQ
  · intro h
    rw [h, norm_zero' hL] at hn
    exact zero_ne_one hn

end Cvs.WeilForm.BottomAttained
