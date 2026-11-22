import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated form on `L²`, lying below

    weilQTrunc N P R φ ≤ weilQ P R φ

`Cvs.WeilForm.BottomLineFromLowerForm` asks for a form lying below the one whose bottom is in question; `Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow` proves the
inequality for a raw `f`, and this carries it to the class.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.TruncatedFormL2Below

/-- **The window's form with `N` Lévy terms retained**, as a functional of `f`. -/
def weilFormTrunc (N P R : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))
    + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
      + ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
          * (selfConvolution f 0 - selfConvolution f (u / 2)))
    - primePowerSideTruncated P R (selfConvolution f)

/-- **The truncation, too, sees only the a.e. class.** -/
theorem weilFormTrunc_congr_ae (N P R : ℕ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    weilFormTrunc N P R f = weilFormTrunc N P R g := by
  unfold weilFormTrunc
  rw [Cvs.WeilForm.WeilFormAeClass.integral_mul_congr_ae h (fun s => Real.exp (s / 2)),
    Cvs.WeilForm.WeilFormAeClass.integral_mul_congr_ae h (fun s => Real.exp (-(s / 2))),
    Cvs.WeilForm.WeilFormAeClass.selfConvolution_eq_of_ae h]

/-- **The truncated form on `L²`.** -/
def weilQTrunc (N P R : ℕ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ :=
  weilFormTrunc N P R (φ : ℝ → ℝ)

/-- Computed on any representative. -/
theorem weilQTrunc_eq {N P R : ℕ} {φ : Lp ℝ 2 (volume : Measure ℝ)} {f : ℝ → ℝ}
    (h : (φ : ℝ → ℝ) =ᵐ[volume] f) : weilQTrunc N P R φ = weilFormTrunc N P R f :=
  weilFormTrunc_congr_ae N P R h

/-- **The truncation lies below**, on `L²`.  This is `Cvs.WeilForm.BottomLineFromLowerForm`'s `hle` for the Weil form: the
integrability hypotheses are carried on a representative, which `Cvs.WeilForm.WindowRepresentative.exists_rep` supplies. -/
theorem weilQTrunc_le (N P R : ℕ) {φ : Lp ℝ 2 (volume : Measure ℝ)} {f : ℝ → ℝ}
    (hae : (φ : ℝ → ℝ) =ᵐ[volume] f)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    (hint₁ : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0))
    (hint₂ : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0)) :
    weilQTrunc N P R φ ≤ Cvs.WeilForm.WeilFormOnWindowL2.weilQ P R φ := by
  rw [weilQTrunc_eq hae, Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq hae]
  exact Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.weilForm_ge_trunc N P R hsq hcross hint₁ hint₂

end Cvs.WeilForm.TruncatedFormL2Below
