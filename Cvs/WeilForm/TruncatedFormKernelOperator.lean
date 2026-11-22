import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.ChannelKernelBoundedOperator
import Cvs.WeilForm.PoleTermOperator
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncOperatorQuadForm
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCutBoundedBridge
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated form as the kernel operator's quadratic form

    weilQWTrunc N P R φ = truncConst N ‖φ‖² − ⟪kernelCLM N L φ, φ⟫ − primeSide

`Cvs.WeilForm.ChannelKernelBoundedOperator`'s operator pairs against the window's inner product, so at an eigenvector the form's
Rayleigh value is the constant less the eigenvalue, and an operator bound is a form bound.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil
open Cvs.Finite.ExponentialKernelLocalises (convSplit)
open Cvs.WeilForm.Archimedean.OffWindowDefect (bIdx)

namespace Cvs.WeilForm.TruncatedFormKernelOperator

variable {L b : ℝ}

/-! ### Homogeneity -/

/-! ### The polarisation at equal arguments -/

/-- The self-convolution of a window representative at the origin is the squared norm. -/
theorem selfConv_rep_zero (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 = ‖φ‖ ^ 2 := by
  rw [← Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ) 0]
  exact Cvs.WeilForm.WindowRepresentative.selfConvolution_zero φ

/-- **The polarisation at equal arguments doubles the self-convolution.** -/
theorem polar_self (f : ℝ → ℝ) (v : ℝ) :
    Cvs.WeilForm.TruncatedFormPolarised.polar f f v = 2 * selfConvolution f v := by
  unfold Cvs.WeilForm.TruncatedFormPolarised.polar
  rw [Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_eq_crossConv]
  ring

/-- **The channel cross term at equal arguments is the channel integral.** -/
theorem chanCross_self (b : ℝ) (f : ℝ → ℝ) :
    Cvs.WeilForm.TruncatedFormPolarised.chanCross b f f = Cvs.WeilForm.ChannelFunctionalL2.chanInt b f := by
  unfold Cvs.WeilForm.TruncatedFormPolarised.chanCross Cvs.WeilForm.ChannelFunctionalL2.chanInt
  rw [← integral_const_mul]
  refine setIntegral_congr_ae measurableSet_Ioi
    (Filter.Eventually.of_forall fun v _ => ?_)
  rw [polar_self]
  ring

/-! ### The operator's quadratic form -/

/-- **The channel operator's quadratic form is the channel integral.** -/
theorem inner_chanMap_self (hL : 0 ≤ L) (hb : 0 ≤ b)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.chanMap b L φ) φ : ℝ)
      = Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  have hlhs : (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.chanMap b L φ) φ : ℝ)
      = ∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep φ s
          * convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) s := by
    rw [Cvs.WeilForm.TruncatedFormPolarised.inner_eq_integral hL]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Cvs.WeilForm.ChannelKernelBoundedOperator.rep_chanMap b φ] with x hx _
    rw [hx]
    rcases le_or_gt x 0 with h0 | h0
    · have hxn : x ∉ Ioc (0:ℝ) L := fun hmem => absurd hmem.1 (not_lt.2 h0)
      rw [Cvs.WeilForm.ChannelKernelBoundedOperator.chanFn, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hxn,
        Cvs.WeilForm.WindowRepresentative.rep_supp φ x hxn]
      ring
    · rcases le_or_gt x L with hxL | hxL
      · rw [Cvs.WeilForm.ChannelKernelBoundedOperator.chanFn, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_mem ⟨h0, hxL⟩]
        ring
      · have hxn : x ∉ Ioc (0:ℝ) L := fun hmem => absurd hmem.2 (not_le.2 hxL)
        rw [Cvs.WeilForm.ChannelKernelBoundedOperator.chanFn, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hxn,
          Cvs.WeilForm.WindowRepresentative.rep_supp φ x hxn]
        ring
  rw [hlhs, ← Cvs.WeilForm.TruncatedFormPolarised.chanCross_eq hL φ φ hb, chanCross_self]

/-- **The pole operator's quadratic form is twice the product of the pole moments.** -/
theorem inner_poleMap_self (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.poleMap L φ) φ : ℝ)
      = 2 * Cvs.WeilForm.TruncatedFormPolarised.poleF (Cvs.WeilForm.WindowRepresentative.rep φ)
        * Cvs.WeilForm.TruncatedFormPolarised.poleG (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  have hlhs : (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.poleMap L φ) φ : ℝ)
      = ∫ s in (0:ℝ)..L, Cvs.WeilForm.PoleTermOperator.poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ) s
          * Cvs.WeilForm.WindowRepresentative.rep φ s := by
    rw [Cvs.WeilForm.TruncatedFormPolarised.inner_eq_integral hL]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Cvs.WeilForm.ChannelKernelBoundedOperator.rep_poleMap φ] with x hx _
    rw [hx]
    by_cases hmem : x ∈ Ioc (0:ℝ) L
    · rw [Cvs.WeilForm.ChannelKernelBoundedOperator.poleFn, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_mem hmem]
    · rw [Cvs.WeilForm.ChannelKernelBoundedOperator.poleFn, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hmem,
        Cvs.WeilForm.WindowRepresentative.rep_supp φ x hmem]
      ring
  rw [hlhs, ← Cvs.WeilForm.TruncatedFormPolarised.pole_cross hL φ φ]
  ring

/-- **The kernel operator's quadratic form is the channel sum less the pole term.** -/
theorem inner_kernelCLM_self (N : ℕ) (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.kernelCLM N L hL φ) φ : ℝ)
      = (∑ k ∈ Finset.range N,
          Cvs.WeilForm.ChannelFunctionalL2.chanInt (bIdx k) (Cvs.WeilForm.WindowRepresentative.rep φ))
        - 2 * Cvs.WeilForm.TruncatedFormPolarised.poleF (Cvs.WeilForm.WindowRepresentative.rep φ)
          * Cvs.WeilForm.TruncatedFormPolarised.poleG (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  rw [Cvs.WeilForm.ChannelKernelBoundedOperator.kernelCLM_apply N hL φ, inner_sub_left, sum_inner,
    inner_poleMap_self hL]
  congr 1
  exact Finset.sum_congr rfl fun k _ =>
    inner_chanMap_self hL (Cvs.WeilForm.TruncOperatorQuadForm.bIdx_pos k).le φ

/-- **The truncated form is the constant times the squared norm, less the operator's quadratic
form and the prime side.** -/
theorem weilQWTrunc_eq_inner (hL : 0 ≤ L) (N P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R φ
      = Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N * ‖φ‖ ^ 2
        - (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.kernelCLM N L hL φ) φ : ℝ)
        - primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ)) := by
  rw [Cvs.WeilForm.TruncatedFormPolarised.weilQWTrunc_channel, inner_kernelCLM_self N hL φ,
    selfConv_rep_zero]
  ring

end Cvs.WeilForm.TruncatedFormKernelOperator
