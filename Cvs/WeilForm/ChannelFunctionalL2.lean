import Mathlib
import Cvs.WeilForm.ChannelLevyIntegrand
import Cvs.WeilForm.HalfLineKernelDoubleIntegral
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The L²-continuous channel functional

    `chanInt b h := 2 ∫_{v>0} e^{−bv} · selfConvolution h v`

equals the channel double integral for continuous compactly supported `f`, and is `L²`-continuous.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ChannelFunctionalL2

/-- The channel functional, in half-line form. -/
def chanInt (b : ℝ) (h : ℝ → ℝ) : ℝ := 2 * ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) * selfConvolution h v

/-- **It is the channel double integral**, for continuous compactly supported `f`. -/
theorem chanInt_eq_double {f : ℝ → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) {b : ℝ}
    (hb : 0 < b) :
    chanInt b f = ∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)) :=
  (Cvs.WeilForm.HalfLineKernelDoubleIntegral.kernel_eq_half_line hf hcf b hb).symm

/-- `e^{−bv}·selfConvolution (rep φ)` is integrable on `(0,∞)`. -/
theorem integrable_exp_self {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {b : ℝ} (hb : 0 < b) :
    Integrable (fun v => Real.exp (-(b * v)) * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v)
      (volume.restrict (Ioi 0)) := by
  have hg := Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)
  have hcrep : HasCompactSupport (Cvs.WeilForm.WindowRepresentative.rep φ) :=
    HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := L)) fun x hx =>
      Cvs.WeilForm.WindowRepresentative.rep_supp φ x fun h => hx (Set.Ioc_subset_Icc_self h)
  have hcg := Cvs.WeilForm.ChannelLevyIntegrand.hasCompactSupport_selfConvolution hcrep
  · obtain ⟨x0, hx0⟩ := (hg.abs).exists_forall_ge_of_hasCompactSupport hcg.abs
    have he : Integrable (fun v => Real.exp (-(b * v))) (volume.restrict (Ioi 0)) := by
      have h0 := exp_neg_integrableOn_Ioi (a := 0) (b := b) hb
      exact h0.congr (Filter.Eventually.of_forall fun v => by simp only [neg_mul])
    have hb2 : Integrable (fun v => selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v
        * Real.exp (-(b * v))) (volume.restrict (Ioi 0)) :=
      he.bdd_mul (c := |selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) x0|)
        hg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hx0 v)
    exact hb2.congr (Filter.Eventually.of_forall fun v => mul_comm _ _)

end Cvs.WeilForm.ChannelFunctionalL2
