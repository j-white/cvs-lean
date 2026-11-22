import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WeilFormReflection
import Cvs.WeilForm.WindowFormTranslationInvariant
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The reflection of the window is a symmetry of the Weil form on its domain

    `reflD φ = φ(L − ·)`,   `‖reflD φ‖ = ‖φ‖`,   `reflD (reflD φ) = φ`,   `weilQW (reflD φ) = weilQW φ`

on the form domain: the reflection preserves Lebesgue measure, the window, the Lévy
integrability, and the form.
-/

noncomputable section

open MeasureTheory Measure Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowReflectionSymmetry

/-- **Reflection of an `L²` class** through `L/2`. -/
def refl (L : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun s => L - s) (measurePreserving_sub_left volume L) φ

theorem refl_ae (L : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    ((refl L φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume] fun s => (φ : ℝ → ℝ) (L - s) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem norm_refl (L : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : ‖refl L φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving _ _

theorem refl_sub (L : ℝ) (φ ψ : Lp ℝ 2 (volume : Measure ℝ)) :
    refl L (φ - ψ) = refl L φ - refl L ψ := by
  apply Lp.ext
  filter_upwards [refl_ae L (φ - ψ), refl_ae L φ, refl_ae L ψ, Lp.coeFn_sub (refl L φ) (refl L ψ),
    (measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_sub φ ψ)] with s h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3]
  exact h5

theorem refl_smul (L c : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : refl L (c • φ) = c • refl L φ := by
  apply Lp.ext
  filter_upwards [refl_ae L (c • φ), refl_ae L φ, Lp.coeFn_smul c (refl L φ),
    (measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_smul c φ)] with s h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2]
  exact h4

/-- **Reflection is an involution.** -/
theorem refl_refl (L : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : refl L (refl L φ) = φ := by
  apply Lp.ext
  filter_upwards [refl_ae L (refl L φ),
    (measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp (refl_ae L φ)]
    with s h1 h2
  rw [h1]
  have : (φ : ℝ → ℝ) (L - (L - s)) = (φ : ℝ → ℝ) s := by rw [sub_sub_cancel]
  exact h2.trans this

/-- **The reflection preserves the window.** -/
theorem refl_mem_window {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    refl L (φ : Lp ℝ 2 (volume : Measure ℝ)) ∈ Cvs.WeilForm.WeilFormOnWindowL2.window L := by
  show ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (0:ℝ) L →
    ((refl L (φ : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x = 0
  have hrep : (fun x => ((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) (L - x))
      =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep φ (L - x) :=
    (measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
      (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ)
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [refl_ae L (φ : Lp ℝ 2 (volume : Measure ℝ)), hrep, hne] with x h1 h2 h3 hx
  rw [h1, h2]
  refine Cvs.WeilForm.WindowRepresentative.rep_supp φ _ fun h => hx ?_
  rcases not_and_or.mp hx with h0 | hL
  · push_neg at h0
    exact absurd h.2 (by linarith [lt_of_le_of_ne h0 h3])
  · push_neg at hL
    exact absurd h.1 (by linarith)

/-- **Reflection on the window.** -/
def reflW {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨refl L φ, refl_mem_window φ⟩

/-- The representative of the reflection is the reflected representative, almost everywhere. -/
theorem rep_reflW_ae {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (reflW φ) =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep φ (L - x) := by
  have hrep : (fun x => ((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) (L - x))
      =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep φ (L - x) :=
    (measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
      (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ)
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [refl_ae L (φ : Lp ℝ 2 (volume : Measure ℝ)), hrep, hne] with x h1 h2 h3
  show (Set.Ioc (0:ℝ) L).indicator (Cvs.WeilForm.WindowRepresentative.fn (reflW φ)) x = _
  rw [Set.indicator_apply]
  split_ifs with hx
  · show ((refl L (φ : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x = _
    rw [h1, h2]
  · symm
    refine Cvs.WeilForm.WindowRepresentative.rep_supp φ _ fun h => hx ?_
    rcases not_and_or.mp hx with h0 | hL
    · push_neg at h0
      exact absurd h.2 (by linarith [lt_of_le_of_ne h0 h3])
    · push_neg at hL
      exact absurd h.1 (by linarith)

/-- The reflected function is a translate of the negated one. -/
theorem reflect_eq_translate (f : ℝ → ℝ) (L : ℝ) :
    (fun x => f (L - x)) = fun x => (fun y => f (-y)) (x + -L) := by
  funext x; congr 1; ring

/-- **The self-convolution is reflection-invariant**, on the window. -/
theorem selfConvolution_reflW {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (v : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (reflW φ)) v
      = selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v := by
  have h1 : selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (reflW φ)) v
      = selfConvolution (fun x => Cvs.WeilForm.WindowRepresentative.rep φ (L - x)) v := by
    unfold selfConvolution
    refine integral_congr_ae ?_
    have h := rep_reflW_ae φ
    have h' := (measurePreserving_add_right volume v).quasiMeasurePreserving.ae_eq_comp h
    filter_upwards [h, h'] with s hs1 hs2
    rw [hs1]
    exact congrArg _ hs2
  rw [h1, reflect_eq_translate,
    Cvs.WeilForm.WindowFormTranslationInvariant.selfConvolution_translate (fun y => Cvs.WeilForm.WindowRepresentative.rep φ (-y)) (-L),
    Cvs.WeilForm.WeilFormReflection.selfConvolution_reflect]

/-- **The reflection preserves the form domain.** -/
theorem reflW_mem_formDomain {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    reflW (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ∈ Cvs.WeilForm.FormDomain.formDomain hL := by
  show IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (reflW _))) _ _
  have : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (reflW (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
    funext u
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [selfConvolution_reflW, selfConvolution_reflW]
  rw [this]
  exact Cvs.WeilForm.FormDomain.hdom_of_mem φ

/-- **Reflection on the form domain.** -/
def reflD {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.FormDomain.formDomain hL :=
  ⟨reflW φ, reflW_mem_formDomain hL φ⟩

theorem norm_reflD {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ‖reflD hL φ‖ = ‖φ‖ :=
  norm_refl L _

theorem reflD_reflD {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    reflD hL (reflD hL φ) = φ := by
  apply Subtype.ext; apply Subtype.ext
  exact refl_refl L _

/-- **The form is reflection-invariant on its domain.** -/
theorem weilQW_reflD {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowRepresentative.weilQW P R ((reflD hL φ : Cvs.WeilForm.FormDomain.formDomain hL) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P R (reflW _) = _
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R _).1, (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R _).1,
    Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R (rep_reflW_ae _), reflect_eq_translate,
    Cvs.WeilForm.WindowFormTranslationInvariant.weilForm_translate P R (fun y => Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (-y)) (-L),
    Cvs.WeilForm.WeilFormReflection.weilForm_reflect]

end Cvs.WeilForm.WindowReflectionSymmetry
