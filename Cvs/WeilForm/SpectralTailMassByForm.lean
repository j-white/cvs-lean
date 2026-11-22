import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.PrimeSideBoundedBelow
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The spectral mass beyond frequency `T` is controlled by the form

    `tailConst T · ∫_{|t| ≥ T} specDensity f ≤ weilForm f − floorConst · ‖f‖²`

with `tailConst T = log(T/2) − 57/T − log π − archSymbol 0`, which exceeds any level for `T`
large.  On a sublevel set of the form the spectral tails are therefore uniformly small.
-/

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SpectralTailMassByForm

/-- The archimedean symbol's excess over its minimum, at the edge of the tail. -/
def tailConst (T : ℝ) : ℝ :=
  Real.log (T / 2) - 57 / T - Real.log Real.pi - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0

/-- **On the tail the symbol is at least its value at the edge**, which grows like `log T`. -/
theorem tail_lower {T : ℝ} (hT : 2 ≤ T) :
    ∀ t ∈ Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T,
      Real.log (T / 2) - 57 / T - Real.log Real.pi ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  intro t ht
  have hTt : T ≤ |t| := ht
  have hsq : T ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (by linarith) hTt 2
  exact (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge hT).trans (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono hsq)

/-- **The tail mass is controlled by the form.** -/
theorem tailMass_le {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {f : ℝ → ℝ} {T : ℝ} (hT : 2 ≤ T)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    tailConst T * ∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
        - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * selfConvolution f 0 := by
  have h := Cvs.WeilForm.TailBoundOnWindow.tailMass_le_window hL P R hf hsupp hdom (T := T)
    (c := Real.log (T / 2) - 57 / T - Real.log Real.pi) (tail_lower hT)
  unfold tailConst Cvs.WeilForm.WindowFormNormFloor.floorConst
  linarith

/-- **Divided through**, once the tail constant is positive. -/
theorem tailMass_le_div {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {f : ℝ → ℝ} {T : ℝ} (hT : 2 ≤ T)
    (hpos : 0 < tailConst T)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    ∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      ≤ (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
          - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * selfConvolution f 0) / tailConst T := by
  rw [le_div_iff₀ hpos, mul_comm]
  exact tailMass_le hL P R hT hf hsupp hdom

/-- **The tail constant exceeds any level**: `T = 2·exp(M⁺ + log π + 29)` does it, because the
logarithm returns the exponent and `57/T ≤ 57/2`. -/
theorem exists_tailConst_ge (M : ℝ) : ∃ T : ℝ, 2 ≤ T ∧ M ≤ tailConst T := by
  set y : ℝ := max M 0 + Real.log Real.pi + 29 + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
    + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| with hy
  have hy0 : 0 ≤ y := by
    have := le_max_right M 0
    have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have := neg_abs_le (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
    linarith
  refine ⟨2 * Real.exp y, ?_, ?_⟩
  · have := Real.add_one_le_exp y
    linarith
  · have hT2 : 2 ≤ 2 * Real.exp y := by have := Real.add_one_le_exp y; linarith
    have hlog : Real.log (2 * Real.exp y / 2) = y := by
      rw [show 2 * Real.exp y / 2 = Real.exp y by ring, Real.log_exp]
    have hdiv : 57 / (2 * Real.exp y) ≤ 57 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT2
    have hM := le_max_left M 0
    have := abs_nonneg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
    unfold tailConst
    rw [hlog]
    linarith

/-- **On the `L²` window.**  The form and norm of `φ` control the spectral tail of its
representative. -/
theorem tailMass_le_div_window {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {T : ℝ} (hT : 2 ≤ T) (hpos : 0 < tailConst T)
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ))
      (Set.Ioi 0) (volume : Measure ℝ)) :
    ∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T,
        Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep φ) t
      ≤ (Cvs.WeilForm.WindowRepresentative.weilQW P R φ
          - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * ‖φ‖ ^ 2) / tailConst T := by
  obtain ⟨hQ, hn⟩ := Cvs.WeilForm.WindowRepresentative.weilQW_rep P R φ
  rw [hQ, ← hn]
  exact tailMass_le_div hL P R hT hpos (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)
    (Cvs.WeilForm.WindowRepresentative.rep_supp φ) hdom

end Cvs.WeilForm.SpectralTailMassByForm
