import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.PrimeSideBoundedBelow
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's form is bounded below by a constant times the norm

    (archSymbol 0 − 2·primeWeightTotal − 4·sinh(L/2))·‖φ‖² ≤ weilQW P R φ

which is the `lam` of `an earlier result.le_of_trial`, with no limiting argument anywhere.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowFormNormFloor

/-- The constant the window's form cannot fall below. -/
def floorConst (L : ℝ) (P R : ℕ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 - 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R
    - 4 * Real.sinh (L / 2)

/-- **The form is bounded below.**  `Cvs.WeilForm.TailBoundOnWindow` carries the bound already; taking the comparison
level at `archSymbol 0` makes its left side vanish, because the symbol is monotone in `t²` and
so never drops below its value at the origin. -/
theorem weilForm_ge_floor {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    floorConst L P R * selfConvolution f 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have h := Cvs.WeilForm.TailBoundOnWindow.tailMass_le_window hL P R hf hsupp hdom
    (T := 0) (c := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
    (fun t _ => Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by simpa using sq_nonneg t))
  rw [sub_self, zero_mul] at h
  unfold floorConst
  linarith

/-- **The same, on `L²`.**  This is `hbot`: the eigenvalue hypothesis the simplicity criteria
consume, for the window's form. -/
theorem weilQW_ge_floor {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    {φ : Cvs.WeilForm.WeilFormOnWindowL2.window L} {f : ℝ → ℝ}
    (hae : Cvs.WeilForm.WindowRepresentative.fn φ =ᵐ[volume] f)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    floorConst L P R * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R φ := by
  have hnorm : selfConvolution f 0 = ‖φ‖ ^ 2 := by
    rw [← Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae hae 0,
      Cvs.WeilForm.WindowRepresentative.selfConvolution_zero]
  have hform : Cvs.WeilForm.WindowRepresentative.weilQW P R φ = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f :=
    Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq hae
  rw [hform, ← hnorm]
  exact weilForm_ge_floor hL P R hf hsupp hdom

end Cvs.WeilForm.WindowFormNormFloor
