import Mathlib
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormAeClass
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Weil form as a form on the window's `L²`

    window L = classes vanishing a.e. off `(0, L]`,   weilQ P R φ = weilForm P R φ

`Cvs.WeilForm.BottomLineFromLowerForm` and `an earlier result` ask for a form on an inner product space; this is it.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormOnWindowL2

/-- **The window's `L²`**, as a subspace of `L²(ℝ)`: the classes vanishing a.e. off `(0, L]`.
`Submodule.innerProductSpace` makes it an inner product space in its own right. -/
def window (L : ℝ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) where
  carrier := {φ | ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (0:ℝ) L → (φ : ℝ → ℝ) x = 0}
  add_mem' := by
    intro φ ψ hφ hψ
    filter_upwards [hφ, hψ, Lp.coeFn_add φ ψ] with x hx hy hadd hmem
    rw [hadd]; simp [hx hmem, hy hmem]
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure ℝ))] with x hx _
    rw [hx]; rfl
  smul_mem' := by
    intro c φ hφ
    filter_upwards [hφ, Lp.coeFn_smul c φ] with x hx hsmul hmem
    rw [hsmul]; simp [hx hmem]

/-- **The Weil form on `L²`.** -/
def weilQ (P R : ℕ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ :=
  Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (φ : ℝ → ℝ)

/-- **Computed on any representative.**  This is what `Cvs.WeilForm.WeilFormAeClass` buys: the form may be evaluated on
a smooth representative rather than on the chosen one. -/
theorem weilQ_eq {P R : ℕ} {φ : Lp ℝ 2 (volume : Measure ℝ)} {f : ℝ → ℝ}
    (h : (φ : ℝ → ℝ) =ᵐ[volume] f) :
    weilQ P R φ = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f :=
  Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R h

/-- **The self-convolution at `0` is the norm squared.**  This is the identity that lets the
`‖v‖²` of `Cvs.WeilForm.BottomLineFromLowerForm` and `an earlier result` be read off the same `g` as the rest of the form. -/
theorem selfConvolution_zero (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    selfConvolution (φ : ℝ → ℝ) 0 = ‖φ‖ ^ 2 := by
  have hconv : selfConvolution (φ : ℝ → ℝ) 0
      = ∫ x : ℝ, (φ : ℝ → ℝ) x * (φ : ℝ → ℝ) x := by
    unfold selfConvolution
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hin : (inner ℝ φ φ : ℝ) = ∫ x : ℝ, (φ : ℝ → ℝ) x * (φ : ℝ → ℝ) x := by
    rw [MeasureTheory.L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [pow_two])
  rw [hconv, ← hin, real_inner_self_eq_norm_sq]

end Cvs.WeilForm.WeilFormOnWindowL2
