import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The self-convolution of a window class is Lipschitz in the class

    `|selfConvolution (rep φ) v − selfConvolution (rep ψ) v| ≤ ‖φ − ψ‖ (‖φ‖ + ‖ψ‖)`

because the self-convolution at `v` is the inner product of the class with its translate by `v`.
-/

noncomputable section

open MeasureTheory Filter Topology Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SelfConvolutionClassLipschitz

/-- Translation of an `L²` class by `v`. -/
def tr (v : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun s => s + v) (measurePreserving_add_right volume v) φ

theorem tr_ae (v : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    ((tr v φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume] fun s => (φ : ℝ → ℝ) (s + v) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem norm_tr (v : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : ‖tr v φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving _ _

theorem tr_sub (v : ℝ) (φ ψ : Lp ℝ 2 (volume : Measure ℝ)) : tr v (φ - ψ) = tr v φ - tr v ψ := by
  apply Lp.ext
  filter_upwards [tr_ae v (φ - ψ), tr_ae v φ, tr_ae v ψ, Lp.coeFn_sub (tr v φ) (tr v ψ),
    (measurePreserving_add_right volume v).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_sub φ ψ)] with s h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3]
  exact h5

/-- **The self-convolution is the inner product with the translate.** -/
theorem selfConvolution_eq_inner {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (v : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v
      = inner ℝ (φ : Lp ℝ 2 (volume : Measure ℝ)) (tr v (φ : Lp ℝ 2 (volume : Measure ℝ))) := by
  rw [L2.inner_def]
  unfold selfConvolution
  refine integral_congr_ae ?_
  have h1 : ((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep φ :=
    Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ
  have h3 : (fun s => Cvs.WeilForm.WindowRepresentative.rep φ (s + v))
      =ᵐ[volume] fun s => ((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) (s + v) :=
    (measurePreserving_add_right volume v).quasiMeasurePreserving.ae_eq_comp h1.symm
  filter_upwards [h1, tr_ae v (φ : Lp ℝ 2 (volume : Measure ℝ)), h3] with s hs1 hs2 hs3
  simp [hs1, hs2, hs3, mul_comm]

/-- **The self-convolution is Lipschitz in the class**, by Cauchy–Schwarz. -/
theorem abs_selfConvolution_sub_le {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (v : ℝ) :
    |selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v
        - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep ψ) v|
      ≤ ‖(φ : Lp ℝ 2 (volume : Measure ℝ)) - ψ‖
          * (‖(φ : Lp ℝ 2 (volume : Measure ℝ))‖ + ‖(ψ : Lp ℝ 2 (volume : Measure ℝ))‖) := by
  rw [selfConvolution_eq_inner, selfConvolution_eq_inner]
  set a : Lp ℝ 2 (volume : Measure ℝ) :=
    ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
  set b : Lp ℝ 2 (volume : Measure ℝ) :=
    ((ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
  have hsplit : inner ℝ a (tr v a) - inner ℝ b (tr v b)
      = inner ℝ (a - b) (tr v a) + inner ℝ b (tr v (a - b)) := by
    rw [tr_sub, inner_sub_left, inner_sub_right]; ring
  rw [hsplit]
  calc |inner ℝ (a - b) (tr v a) + inner ℝ b (tr v (a - b))|
      ≤ |inner ℝ (a - b) (tr v a)| + |inner ℝ b (tr v (a - b))| := abs_add_le _ _
    _ ≤ ‖a - b‖ * ‖tr v a‖ + ‖b‖ * ‖tr v (a - b)‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = ‖a - b‖ * (‖a‖ + ‖b‖) := by rw [norm_tr, norm_tr]; ring

/-- **The self-convolution converges along `L²` convergence in the window.** -/
theorem tendsto_selfConvolution {L : ℝ} {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) (v : ℝ) :
    Tendsto (fun k => selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (x k)) v) atTop
      (𝓝 (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep y) v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun k => ‖((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      - (y : Lp ℝ 2 (volume : Measure ℝ))‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h2 : Tendsto (fun k => ‖((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖
      + ‖(y : Lp ℝ 2 (volume : Measure ℝ))‖) atTop
      (𝓝 (‖(y : Lp ℝ 2 (volume : Measure ℝ))‖ + ‖(y : Lp ℝ 2 (volume : Measure ℝ))‖)) :=
    hx.norm.add tendsto_const_nhds
  have hprod := h1.mul h2
  rw [zero_mul] at hprod
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hprod
  rw [Real.norm_eq_abs]
  exact abs_selfConvolution_sub_le (x k) y v

end Cvs.WeilForm.SelfConvolutionClassLipschitz
