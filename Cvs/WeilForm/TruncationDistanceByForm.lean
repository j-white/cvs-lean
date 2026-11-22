import Mathlib
import Cvs.Upstream.ComplexificationIsometryL2
import Cvs.Upstream.FrequencyTruncationL2
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralTailMassByForm
import Cvs.WeilForm.SpectralTailTransformVariable
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative

/-!
# The distance to the truncation is controlled by the form

    `‖emb φ − cut (T/2π) (emb φ)‖² ≤ (weilQW φ − floorConst · ‖φ‖²) / tailConst T`

on the form domain: the truncation error is the spectral tail, and the tail is bounded by
the form.  On a sublevel set with bounded norm the error is therefore uniformly small.
-/

noncomputable section

open MeasureTheory FourierTransform Real

namespace Cvs.WeilForm.TruncationDistanceByForm

/-- **The truncation error of the embedded class is its spectral tail**, in the project's
frequency variable. -/
theorem norm_sub_cut_sq_eq {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (T : ℝ) :
    ‖Cvs.Upstream.ComplexificationIsometryL2.emb (φ : Lp ℝ 2 (volume : Measure ℝ))
        - Cvs.Upstream.FrequencyTruncationL2.cut (T / (2 * π))
            (Cvs.Upstream.ComplexificationIsometryL2.emb (φ : Lp ℝ 2 (volume : Measure ℝ)))‖ ^ 2
      = ∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T,
          Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep φ) t := by
  rw [Cvs.Upstream.FrequencyTruncationL2.norm_sub_cut_sq, Cvs.WeilForm.SpectralTailTransformVariable.integral_tail_specDensity]
  refine setIntegral_congr_ae (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet _) ?_
  filter_upwards [Cvs.Upstream.ComplexificationIsometryL2.fourier_emb_window hL φ] with ξ hξ _
  rw [hξ]

/-- **The truncation error is controlled by the form**, on the form domain. -/
theorem norm_sub_cut_sq_le {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) {T : ℝ} (hT : 2 ≤ T)
    (hpos : 0 < Cvs.WeilForm.SpectralTailMassByForm.tailConst T) :
    ‖Cvs.Upstream.ComplexificationIsometryL2.emb ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        - Cvs.Upstream.FrequencyTruncationL2.cut (T / (2 * π))
            (Cvs.Upstream.ComplexificationIsometryL2.emb
              ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))‖ ^ 2
      ≤ (Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
          - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * ‖φ‖ ^ 2)
        / Cvs.WeilForm.SpectralTailMassByForm.tailConst T := by
  rw [norm_sub_cut_sq_eq hL]
  exact Cvs.WeilForm.SpectralTailMassByForm.tailMass_le_div_window hL P R _ hT hpos
    (Cvs.WeilForm.FormDomain.hdom_of_mem φ)

/-- **Uniformly on a sublevel set of the form with bounded norm.** -/
theorem norm_sub_cut_sq_le_of_le {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {c : ℝ}
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) (hn : ‖φ‖ ≤ 1)
    (hQ : Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ≤ c)
    {T : ℝ} (hT : 2 ≤ T) (hpos : 0 < Cvs.WeilForm.SpectralTailMassByForm.tailConst T) :
    ‖Cvs.Upstream.ComplexificationIsometryL2.emb ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        - Cvs.Upstream.FrequencyTruncationL2.cut (T / (2 * π))
            (Cvs.Upstream.ComplexificationIsometryL2.emb
              ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))‖ ^ 2
      ≤ (c + |Cvs.WeilForm.WindowFormNormFloor.floorConst L P R|) / Cvs.WeilForm.SpectralTailMassByForm.tailConst T := by
  refine (norm_sub_cut_sq_le hL P R φ hT hpos).trans ?_
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have h1 : ‖φ‖ ^ 2 ≤ 1 := by
    have := norm_nonneg φ
    nlinarith
  have h2 := neg_abs_le (Cvs.WeilForm.WindowFormNormFloor.floorConst L P R)
  have h3 : -|Cvs.WeilForm.WindowFormNormFloor.floorConst L P R| * ‖φ‖ ^ 2
      ≤ Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * ‖φ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have h4 : -|Cvs.WeilForm.WindowFormNormFloor.floorConst L P R|
      ≤ -|Cvs.WeilForm.WindowFormNormFloor.floorConst L P R| * ‖φ‖ ^ 2 := by
    have := abs_nonneg (Cvs.WeilForm.WindowFormNormFloor.floorConst L P R)
    nlinarith
  linarith

end Cvs.WeilForm.TruncationDistanceByForm
