import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ParallelogramLaw
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window Weil form is the diagonal of a symmetric bilinear form

The parallelogram law (Cvs.WeilForm.ParallelogramLaw), homogeneity and the expansion along a line give the polar through
`QuadraticMap.ofPolar`, so `Cvs.WeilForm.InfimumAttainedSphere.Q` on the form domain is `QWbil φ φ` for a symmetric `QWbil`.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.SymmetricBilinearForm

/-! ### A quadratic form from the parallelogram law and a line expansion -/

section Generic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

omit [Module ℝ E] in
/-- **The polar is additive** for any `Q` satisfying the parallelogram law. -/
theorem polar_add_left_of_par {Q : E → ℝ}
    (hpar : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) (x x' y : E) :
    QuadraticMap.polar Q (x + x') y = QuadraticMap.polar Q x y + QuadraticMap.polar Q x' y := by
  have h0 : Q 0 = 0 := by have := hpar 0 0; simp at this; linarith
  have hneg : ∀ z, Q (-z) = Q z := fun z => by
    have := hpar 0 z; simp [h0] at this; linarith
  have a1 := hpar (x + y) (x' + y)
  have a2 := hpar (x - y) (x' - y)
  have b1 := hpar (x + x' + y) y
  have b2 := hpar (x + x' - y) (-y)
  have c1 := hpar x y
  have c2 := hpar x' y
  have c3 := hpar (x + x') y
  have hny := hneg y
  simp only [QuadraticMap.polar]
  have e1 : x + y + (x' + y) = x + x' + y + y := by abel
  have e2 : x + y - (x' + y) = x - x' := by abel
  have e3 : x - y + (x' - y) = x + x' - y + -y := by abel
  have e4 : x - y - (x' - y) = x - x' := by abel
  have e5 : x + x' + y - y = x + x' := by abel
  have e6 : x + x' - y - -y = x + x' := by abel
  rw [e1, e2] at a1; rw [e3, e4] at a2; rw [e5] at b1; rw [e6] at b2
  linarith

/-- **The polar is homogeneous** when `Q` is `2`-homogeneous and quadratic along every line. -/
theorem polar_smul_left_of_exp {Q : E → ℝ}
    (hsmul : ∀ (a : ℝ) x, Q (a • x) = a * a * Q x)
    (hexp : ∀ x y : E, ∃ c : ℝ, ∀ a : ℝ, Q (y + a • x) = Q y + 2 * a * c + a ^ 2 * Q x)
    (a : ℝ) (x y : E) :
    QuadraticMap.polar Q (a • x) y = a • QuadraticMap.polar Q x y := by
  obtain ⟨c, hc⟩ := hexp x y
  simp only [QuadraticMap.polar, smul_eq_mul]
  have h1 := hc a
  have h2 := hc 1
  rw [one_smul] at h2
  rw [add_comm (a • x) y, add_comm x y, h1, h2, hsmul]
  ring

/-- The quadratic form with diagonal `Q`, built by `QuadraticMap.ofPolar`. -/
def ofParExp (Q : E → ℝ) (hsmul : ∀ (a : ℝ) x, Q (a • x) = a * a * Q x)
    (hpar : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hexp : ∀ x y : E, ∃ c : ℝ, ∀ a : ℝ, Q (y + a • x) = Q y + 2 * a * c + a ^ 2 * Q x) :
    QuadraticForm ℝ E :=
  QuadraticMap.ofPolar Q (fun a x => by rw [hsmul, smul_eq_mul])
    (polar_add_left_of_par hpar) (polar_smul_left_of_exp hsmul hexp)

end Generic

/-! ### The window Weil form -/

/-- The cross term of the window Weil form: pole, archimedean and prime-power parts. -/
def crossW (P R : ℕ) (f g : ℝ → ℝ) : ℝ :=
  Cvs.WeilForm.TruncatedFormPolarised.poleF f * Cvs.WeilForm.TruncatedFormPolarised.poleG g + Cvs.WeilForm.TruncatedFormPolarised.poleF g * Cvs.WeilForm.TruncatedFormPolarised.poleG f
    + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * (∫ x, f x * g x)
    + Cvs.L2a.FullTailPolarisation.archFullBil f g
    - Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.WeilForm.TruncatedFormPolarised.polar f g) / 2

/-- **The expansion along a line**: `Q(φ + tψ) = Q(φ) + 2t·crossW + t²Q(ψ)`. -/
theorem weilQW_expand {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) (t : ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (φ + t • ψ)
      = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ
        + 2 * t * crossW P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        + t ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R ψ := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P R ((φ + t • ψ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    = Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) + _ + t ^ 2 * Cvs.WeilForm.WindowRepresentative.weilQW P R (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  rw [Submodule.coe_add, Submodule.coe_smul]
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R _).1, (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).1,
    (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).1]
  have hae := Cvs.WeilForm.TruncatedFormPolarised.rep_add_smul_ae (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) t
  rw [Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R hae]
  have hfm := Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hgm := Cvs.WeilForm.WindowRepresentative.memLp_rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hlf := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  have hlg := Cvs.WeilForm.FormDomain.hdom_of_mem ψ
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) with hf
  set g := Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) with hg
  have hF : (∫ x, (f x + t * g x) * Real.exp (x / 2)) = Cvs.WeilForm.TruncatedFormPolarised.poleF f + t * Cvs.WeilForm.TruncatedFormPolarised.poleF g := by
    unfold Cvs.WeilForm.TruncatedFormPolarised.poleF
    have : (∫ x, (f x + t * g x) * Real.exp (x / 2))
        = ∫ x, f x * Real.exp (x / 2) + t * (g x * Real.exp (x / 2)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [this, integral_add (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep_mul _ (by fun_prop))
      ((Cvs.WeilForm.TruncatedFormPolarised.integrable_rep_mul _ (by fun_prop)).const_mul t), integral_const_mul]
  have hG : (∫ x, (f x + t * g x) * Real.exp (-(x / 2))) = Cvs.WeilForm.TruncatedFormPolarised.poleG f + t * Cvs.WeilForm.TruncatedFormPolarised.poleG g := by
    unfold Cvs.WeilForm.TruncatedFormPolarised.poleG
    have : (∫ x, (f x + t * g x) * Real.exp (-(x / 2)))
        = ∫ x, f x * Real.exp (-(x / 2)) + t * (g x * Real.exp (-(x / 2))) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [this, integral_add (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep_mul _ (by fun_prop))
      ((Cvs.WeilForm.TruncatedFormPolarised.integrable_rep_mul _ (by fun_prop)).const_mul t), integral_const_mul]
  have hS : ∀ v, Cvs.Zeta.Explicit.Weil.selfConvolution (fun x => f x + t * g x) v
      = Cvs.Zeta.Explicit.Weil.selfConvolution f v + t * Cvs.WeilForm.TruncatedFormPolarised.polar f g v
        + t ^ 2 * Cvs.Zeta.Explicit.Weil.selfConvolution g v :=
    fun v => Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_add_smul hfm hgm t v
  have hS0 : Cvs.Zeta.Explicit.Weil.selfConvolution f 0 = ∫ x, f x * f x := by
    unfold Cvs.Zeta.Explicit.Weil.selfConvolution
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hP0 : Cvs.WeilForm.TruncatedFormPolarised.polar f g 0 = 2 * ∫ x, f x * g x := by
    unfold Cvs.WeilForm.TruncatedFormPolarised.polar Cvs.WeilForm.TruncatedFormPolarised.crossConv
    simp only [add_zero]
    rw [two_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hG0 : Cvs.Zeta.Explicit.Weil.selfConvolution g 0 = ∫ x, g x * g x := by
    unfold Cvs.Zeta.Explicit.Weil.selfConvolution
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hA := Cvs.L2a.FullTailPolarisation.archFull_add_smul hfm hgm hlf hlg t
  have hPr : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (fun x => f x + t * g x))
      = Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution f)
        + t * Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.WeilForm.TruncatedFormPolarised.polar f g)
        + t ^ 2 * Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
            (Cvs.Zeta.Explicit.Weil.selfConvolution g) := by
    have : Cvs.Zeta.Explicit.Weil.selfConvolution (fun x => f x + t * g x)
        = fun v => (Cvs.Zeta.Explicit.Weil.selfConvolution f v + t * Cvs.WeilForm.TruncatedFormPolarised.polar f g v)
          + t ^ 2 * Cvs.Zeta.Explicit.Weil.selfConvolution g v := funext hS
    rw [this, Cvs.WeilForm.TruncatedFormPolarised.primePowerSideTruncated_add, Cvs.WeilForm.TruncatedFormPolarised.primePowerSideTruncated_add,
      Cvs.WeilForm.TruncatedFormPolarised.primePowerSideTruncated_smul, Cvs.WeilForm.TruncatedFormPolarised.primePowerSideTruncated_smul]
  have hW : ∀ h : ℝ → ℝ, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R h
      = 2 * (∫ s, h s * Real.exp (s / 2)) * (∫ s, h s * Real.exp (-(s / 2)))
        + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * Cvs.Zeta.Explicit.Weil.selfConvolution h 0 + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull h)
        - Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution h) :=
    fun h => rfl
  rw [hW, hW f, hW g, hF, hG, hS 0, hA, hPr, hS0, hP0, hG0]
  unfold crossW Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG
  ring

/-- **Homogeneity**: `Q(aφ) = a²Q(φ)`. -/
theorem Q_smul {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (a : ℝ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (a • φ) = a * a * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P R ((a • φ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) = _
  rw [Submodule.coe_smul, Cvs.WeilForm.BottomAttained.weilQW_smul]; ring

/-- The window Weil form vanishes at the zero class. -/
theorem Q_zero {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) : Cvs.WeilForm.InfimumAttainedSphere.Q hL P R 0 = 0 := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P R ((0 : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) = 0
  rw [Submodule.coe_zero, Cvs.WeilForm.BottomAttained.weilQW_zero]

/-- The window Weil form as a `QuadraticForm` on the form domain. -/
def QWquad {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) : QuadraticForm ℝ (Cvs.WeilForm.FormDomain.formDomain hL) :=
  ofParExp (Cvs.WeilForm.InfimumAttainedSphere.Q hL P R) (Q_smul hL P R) (Cvs.WeilForm.ParallelogramLaw.weilQW_parallelogram hL P R)
    (fun x y => ⟨crossW P R (Cvs.WeilForm.WindowRepresentative.rep (y : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.rep (x : Cvs.WeilForm.WeilFormOnWindowL2.window L)),
      fun a => weilQW_expand hL P R y x a⟩)

/-- The symmetric bilinear form associated with `QWquad`. -/
def QWbil {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) : LinearMap.BilinForm ℝ (Cvs.WeilForm.FormDomain.formDomain hL) :=
  QuadraticMap.associatedHom (R := ℝ) (N := ℝ) (M := Cvs.WeilForm.FormDomain.formDomain hL) ℝ (QWquad hL P R)

/-- `QWbil` is symmetric. -/
theorem QWbil_isSymm {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) : (QWbil hL P R).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y => ?_
  unfold QWbil
  rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply, add_comm y x, sub_right_comm]

/-- **The diagonal of `QWbil` is the window Weil form**: `QWbil φ φ = Q(φ)`. -/
theorem QWbil_self {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    QWbil hL P R φ φ = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ := by
  unfold QWbil
  rw [QuadraticMap.associated_eq_self_apply]
  rfl

end Cvs.WeilForm.SymmetricBilinearForm
