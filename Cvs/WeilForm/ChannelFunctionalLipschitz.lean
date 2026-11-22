import Mathlib
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.SelfConvolutionClassLipschitz
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The channel functional is Lipschitz on the window

    `|chanInt b (rep φ) − chanInt b (rep ψ)| ≤ (2/b)·‖φ−ψ‖·(‖φ‖+‖ψ‖)`   (`b > 0`).
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ChannelFunctionalLipschitz

/-- `∫_{v>0} e^{−bv} = 1/b`. -/
theorem integral_exp_neg (b : ℝ) (hb : 0 < b) :
    ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) = 1 / b := by
  have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hb
  simp only [mul_zero] at h
  rw [show (fun v => Real.exp (-(b * v))) = (fun v => (fun x => Real.exp (-x)) (b * v)) from rfl, h,
    integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, one_div]

/-- **The channel functional is Lipschitz on the window.** -/
theorem abs_chanInt_sub_le {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {b : ℝ} (hb : 0 < b) :
    |Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep φ)
        - Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep ψ)|
      ≤ (2 / b) * ‖(φ : Lp ℝ 2 (volume : Measure ℝ)) - ψ‖ * (‖φ‖ + ‖ψ‖) := by
  set M := ‖(φ : Lp ℝ 2 (volume : Measure ℝ)) - ψ‖ * (‖φ‖ + ‖ψ‖) with hM
  have hiφ := Cvs.WeilForm.ChannelFunctionalL2.integrable_exp_self φ hb
  have hiψ := Cvs.WeilForm.ChannelFunctionalL2.integrable_exp_self ψ hb
  have he : Integrable (fun v => Real.exp (-(b * v))) (volume.restrict (Ioi 0)) := by
    have h0 := exp_neg_integrableOn_Ioi (a := 0) (b := b) hb
    exact h0.congr (Filter.Eventually.of_forall fun v => by simp only [neg_mul])
  have hdiff : Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep φ)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep ψ)
      = 2 * ∫ v in Ioi (0:ℝ), (Real.exp (-(b * v)) * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v
          - Real.exp (-(b * v)) * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep ψ) v) := by
    unfold Cvs.WeilForm.ChannelFunctionalL2.chanInt
    rw [← mul_sub, ← integral_sub hiφ hiψ]
  rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hbound : |∫ v in Ioi (0:ℝ), (Real.exp (-(b * v)) * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v
        - Real.exp (-(b * v)) * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep ψ) v)|
      ≤ ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) * M := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (he.mul_const M) (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (Cvs.WeilForm.SelfConvolutionClassLipschitz.abs_selfConvolution_sub_le φ ψ v) (Real.exp_pos _).le
  refine (mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 2)).trans ?_
  rw [integral_mul_const, integral_exp_neg b hb]
  apply le_of_eq
  rw [hM]; ring

end Cvs.WeilForm.ChannelFunctionalLipschitz
