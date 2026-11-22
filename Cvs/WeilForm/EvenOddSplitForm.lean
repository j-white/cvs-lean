import Mathlib
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.HatInFormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.IsolationFromSimplicity
import Cvs.WeilForm.ParallelogramLaw
import Cvs.WeilForm.SimpleGroundEvenOrOdd
import Cvs.WeilForm.TwoIndependentClasses
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# The even/odd split of the Weil form, and evenness from the odd/even gap

    `φ = e + o`,  `Q φ = Q e + Q o`,  `‖φ‖² = ‖e‖² + ‖o‖²`,
    odd sector strictly above the bottom   ⟹   every minimiser is even

on the form domain, with `e`, `o` the reflection-even and reflection-odd parts.
-/

noncomputable section

open MeasureTheory

namespace Cvs.WeilForm.EvenOddSplitForm

theorem refl_add (L : ℝ) (φ ψ : Lp ℝ 2 (volume : Measure ℝ)) :
    Cvs.WeilForm.WindowReflectionSymmetry.refl L (φ + ψ)
      = Cvs.WeilForm.WindowReflectionSymmetry.refl L φ + Cvs.WeilForm.WindowReflectionSymmetry.refl L ψ := by
  apply Lp.ext
  filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.refl_ae L (φ + ψ), Cvs.WeilForm.WindowReflectionSymmetry.refl_ae L φ,
    Cvs.WeilForm.WindowReflectionSymmetry.refl_ae L ψ,
    Lp.coeFn_add (Cvs.WeilForm.WindowReflectionSymmetry.refl L φ) (Cvs.WeilForm.WindowReflectionSymmetry.refl L ψ),
    (Measure.measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_add φ ψ)] with s h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3]
  exact h5

theorem reflD_add {L : ℝ} (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (φ + ψ)
      = Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ + Cvs.WeilForm.WindowReflectionSymmetry.reflD hL ψ := by
  apply Subtype.ext; apply Subtype.ext
  exact refl_add L _ _

theorem reflD_sub {L : ℝ} (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (φ - ψ)
      = Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ - Cvs.WeilForm.WindowReflectionSymmetry.reflD hL ψ := by
  apply Subtype.ext; apply Subtype.ext
  exact Cvs.WeilForm.WindowReflectionSymmetry.refl_sub L _ _

/-- **The reflection preserves inner products.** -/
theorem inner_reflD {L : ℝ} (hL : 0 ≤ L) (x y : Cvs.WeilForm.FormDomain.formDomain hL) :
    (inner ℝ (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL x) (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL y) : ℝ)
      = inner ℝ x y := by
  rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe, Cvs.WeilForm.TwoIndependentClasses.inner_coe]
  show (inner ℝ (Cvs.WeilForm.WindowReflectionSymmetry.refl L ((x : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
    (Cvs.WeilForm.WindowReflectionSymmetry.refl L ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) : ℝ) = _
  have h1 := norm_add_sq_real
    (Cvs.WeilForm.WindowReflectionSymmetry.refl L ((x : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
    (Cvs.WeilForm.WindowReflectionSymmetry.refl L ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
  have h2 := norm_add_sq_real ((x : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
    ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
  rw [← refl_add, Cvs.WeilForm.WindowReflectionSymmetry.norm_refl, Cvs.WeilForm.WindowReflectionSymmetry.norm_refl,
    Cvs.WeilForm.WindowReflectionSymmetry.norm_refl] at h1
  linarith

/-- The even part. -/
def evenPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.FormDomain.formDomain hL :=
  (1 / 2 : ℝ) • (φ + Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ)

/-- The odd part. -/
def oddPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.FormDomain.formDomain hL :=
  (1 / 2 : ℝ) • (φ - Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ)

theorem evenPart_add_oddPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    evenPart hL φ + oddPart hL φ = φ := by
  unfold evenPart oddPart
  rw [← smul_add]
  have : (φ + Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ) + (φ - Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ)
      = (2 : ℝ) • φ := by rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

theorem evenPart_sub_oddPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    evenPart hL φ - oddPart hL φ = Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ := by
  unfold evenPart oddPart
  apply Subtype.ext; apply Subtype.ext
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add]
  rw [← smul_sub]
  have : (((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        + ((Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      - (((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        - ((Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      = (2 : ℝ) • ((Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
          Lp ℝ 2 (volume : Measure ℝ)) := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

theorem reflD_evenPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (evenPart hL φ) = evenPart hL φ := by
  unfold evenPart
  rw [Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, reflD_add, Cvs.WeilForm.WindowReflectionSymmetry.reflD_reflD, add_comm]

theorem reflD_oddPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (oddPart hL φ) = -oddPart hL φ := by
  unfold oddPart
  rw [Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, reflD_sub, Cvs.WeilForm.WindowReflectionSymmetry.reflD_reflD]
  apply Subtype.ext; apply Subtype.ext
  simp only [Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_sub]
  rw [← smul_neg, neg_sub]

/-- **Even and odd parts are orthogonal.** -/
theorem inner_evenPart_oddPart {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    (inner ℝ (evenPart hL φ) (oddPart hL φ) : ℝ) = 0 := by
  have h := inner_reflD hL (evenPart hL φ) (oddPart hL φ)
  rw [reflD_evenPart, reflD_oddPart, Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_neg,
    Submodule.coe_neg, inner_neg_right, ← Cvs.WeilForm.TwoIndependentClasses.inner_coe] at h
  linarith

/-- **The norm splits.** -/
theorem norm_sq_split {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ‖φ‖ ^ 2 = ‖evenPart hL φ‖ ^ 2 + ‖oddPart hL φ‖ ^ 2 := by
  conv_lhs => rw [← evenPart_add_oddPart hL φ]
  show ‖(((evenPart hL φ + oddPart hL φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2 = _
  rw [Submodule.coe_add, Submodule.coe_add, norm_add_sq_real, ← Cvs.WeilForm.TwoIndependentClasses.inner_coe,
    inner_evenPart_oddPart]
  have h1 : ‖((evenPart hL φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖
      = ‖evenPart hL φ‖ := rfl
  have h2 : ‖((oddPart hL φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖
      = ‖oddPart hL φ‖ := rfl
  rw [h1, h2]
  ring

/-- **The form splits.** -/
theorem weilQW_split {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = Cvs.WeilForm.WindowRepresentative.weilQW P R ((evenPart hL φ : Cvs.WeilForm.FormDomain.formDomain hL) :
          Cvs.WeilForm.WeilFormOnWindowL2.window L)
        + Cvs.WeilForm.WindowRepresentative.weilQW P R ((oddPart hL φ : Cvs.WeilForm.FormDomain.formDomain hL) :
          Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
  have h := Cvs.WeilForm.ParallelogramLaw.weilQW_parallelogram hL P R (evenPart hL φ) (oddPart hL φ)
  rw [evenPart_add_oddPart, evenPart_sub_oddPart, Cvs.WeilForm.WindowReflectionSymmetry.weilQW_reflD] at h
  linarith

/-- **Every minimiser is even when the odd sector sits strictly above the bottom.** -/
theorem even_of_odd_gap {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {lam : ℝ}
    (hbot : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL,
      lam * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (hgap : ∀ o : Cvs.WeilForm.FormDomain.formDomain hL, Cvs.WeilForm.WindowReflectionSymmetry.reflD hL o = -o → o ≠ 0 →
      lam * ‖o‖ ^ 2 < Cvs.WeilForm.WindowRepresentative.weilQW P R (o : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    {η : Cvs.WeilForm.FormDomain.formDomain hL}
    (hmin : Cvs.WeilForm.WindowRepresentative.weilQW P R (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) = lam * ‖η‖ ^ 2) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL η = η := by
  have hsplit := weilQW_split hL P R η
  have hnorm := norm_sq_split hL η
  have he := hbot (evenPart hL η)
  by_cases ho : oddPart hL η = 0
  · have hη : η = evenPart hL η := by
      conv_lhs => rw [← evenPart_add_oddPart hL η]
      rw [ho, add_zero]
    conv_lhs => rw [hη]
    rw [reflD_evenPart]
    exact hη.symm
  · have hodd := hgap (oddPart hL η) (reflD_oddPart hL η) ho
    have hl : lam * ‖η‖ ^ 2 = lam * ‖evenPart hL η‖ ^ 2 + lam * ‖oddPart hL η‖ ^ 2 := by
      rw [hnorm]; ring
    exfalso
    linarith

/-- **Step (a) from the odd/even gap and simplicity on the even sector.** -/
theorem stepA_of_odd_gap {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (hgap : ∀ o : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le o = -o → o ≠ 0 →
      Cvs.WeilForm.BottomAttained.lam hL P R * ‖o‖ ^ 2 < Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R o)
    (hsimpleEven : ∀ v w : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le v = v → Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le w = w →
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v = Cvs.WeilForm.BottomAttained.lam hL P R * ‖v‖ ^ 2 →
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R w = Cvs.WeilForm.BottomAttained.lam hL P R * ‖w‖ ^ 2 →
      v ≠ 0 → ∃ c : ℝ, w = c • v) :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) (Cvs.WeilForm.BottomAttained.lam hL P R) η := by
  obtain ⟨η, hη, hQ⟩ := Cvs.WeilForm.HatInFormDomain.exists_min hL P R
  have hn : ‖η‖ = 1 := hη
  have hatt : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η = Cvs.WeilForm.BottomAttained.lam hL P R * ‖η‖ ^ 2 := by
    rw [hn, one_pow, mul_one]; exact hQ
  have hne : η ≠ 0 := by
    intro h; rw [h, Cvs.WeilForm.BottomAttained.norm_zero' hL] at hn; exact zero_ne_one hn
  have hbot := Cvs.WeilForm.BottomAttained.bottom hL P R
  have heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η := even_of_odd_gap hL.le P R hbot hgap hatt
  have hsimple' : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v = Cvs.WeilForm.BottomAttained.lam hL P R * ‖v‖ ^ 2 →
        ∃ c : ℝ, v = c • η := fun v hv =>
    hsimpleEven η v heven (even_of_odd_gap hL.le P R hbot hgap hv) hatt hv hne
  obtain ⟨mu, hgap', hperp⟩ := Cvs.WeilForm.IsolationFromSimplicity.isolated_of_simple hL P R hbot hne hsimple'
  exact ⟨η, Cvs.WeilForm.FormDomain.stepA_weil hL.le P R hbot hatt hne hsimple' hgap' hperp heven⟩

end Cvs.WeilForm.EvenOddSplitForm
