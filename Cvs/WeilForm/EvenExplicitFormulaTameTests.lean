import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.ReflectedSpineTame
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.StepA.NegativeIndexQuadruples
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even explicit formula on tame even tests and on `R₁`

For `2 ≤ x`, `L = log x` and `v` tame on `[1/x, 1]` whose class `fv x v` is the centred profile `g` shifted by
`L/2`, with `g` even: `Q(w_v) = Σ_ρ m_ρ((∫ g ue_ρ)² − (∫ g ve_ρ)²)`, the family summable. Every `r ∈ R₁` (at
`80 ≤ 2πx`) is `w_v` for a tame `v` with `fv x v (L − s) = fv x v s`, and so is `w_v − r` for any such `v`.
Around a quadruple `σ` the sum is `W_σ` times `σ`'s term plus the sums over the zeros outside `quad σ`.
-/

noncomputable section

open Real MeasureTheory

namespace Cvs.WeilForm.EvenExplicitFormulaTameTests
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.StepA.TopQuadruple (quad quadWeight offLine)
open Cvs.StepA.NegativeIndexQuadruples (InQuad)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)

/-! ### F4: the even explicit formula on a tame even test -/

/-- The class profile of a tame test is integrable. -/
theorem integrable_fv {x : ℕ} {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) : Integrable (Cvs.Approximant.SpineCouplingTailPairing.fv x v) := by
  have h := hv.log.1.comp_sub_right (Real.log x)
  exact h

/-! ### F3: `R₁` consists of classes of reflection-symmetric tame tests -/

/-- The class profile of an average is the average of the class profiles. -/
theorem fv_avg (x : ℕ) (v w : ℝ → ℝ) (s : ℝ) :
    Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.StepA.LowEigenvalueCountSpine.avg v w) s = (Cvs.Approximant.SpineCouplingTailPairing.fv x v s + Cvs.Approximant.SpineCouplingTailPairing.fv x w s) / 2 := by
  simp only [Cvs.Approximant.SpineCouplingTailPairing.fv, Cvs.L2a.TailLogScaleTest.logScale, Cvs.StepA.LowEigenvalueCountSpine.avg]
  ring

/-- The even spine window's class profile is symmetric about `L/2`. -/
theorem fv_evenWin_refl {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) :
    Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.StepA.LowEigenvalueCountSpine.evenWin x a) (Real.log x - s)
      = Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.StepA.LowEigenvalueCountSpine.evenWin x a) s := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hsupp := (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a).supp
  unfold Cvs.StepA.LowEigenvalueCountSpine.evenWin
  rw [fv_avg, fv_avg, Cvs.L2a.ReflectedSpineTame.fv_reciprocal hx0 hsupp, Cvs.L2a.ReflectedSpineTame.fv_reciprocal hx0 hsupp, sub_sub_cancel]
  ring

/-- **Every `r ∈ R₁` is the class of a reflection-symmetric tame test**: at `80 ≤ 2πx`,
`r = w_v` with `v` tame on `[1/x, 1]` and `fv x v (L − s) = fv x v s`. -/
theorem exists_tame_of_mem_R1 {x : ℕ} (hx : 80 ≤ 2 * π * x) {r : Cvs.Route.L1FloorFromBulkD0.Dom x}
    (hr : r ∈ Cvs.L2a.EvenSectorReflectionBound.R1 x) :
    ∃ (v : ℝ → ℝ) (hv : Tame v (1 / x) 1), r = Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hv
      ∧ ∀ s, Cvs.Approximant.SpineCouplingTailPairing.fv x v (Real.log x - s) = Cvs.Approximant.SpineCouplingTailPairing.fv x v s := by
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  exact ⟨_, Cvs.StepA.LowEigenvalueCountSpine.tame_evenWin hx a,
    Cvs.StepA.LowEigenvalueCountSpine.evenPart_spineMap_eq_wv hx a, fv_evenWin_refl hx a⟩

/-! ### F5: the quadruple collapse -/

/-- **The quadruple collapse**: for `f` constant on `quad σ` with `m_ρ f(ρ)` summable,
`Σ_ρ m_ρ f(ρ) = W_σ f(σ) + Σ_{ρ ∉ quad σ} m_ρ f(ρ)`. -/
theorem tsum_quad_split (σ : nonTrivialZeroSet) {f : nonTrivialZeroSet → ℝ}
    (hf : Summable fun ρ => (Cvs.Criterion.divisorWeight ρ : ℝ) * f ρ)
    (hq : ∀ ρ, InQuad ρ σ → f ρ = f σ) :
    ∑' ρ, (Cvs.Criterion.divisorWeight ρ : ℝ) * f ρ
      = quadWeight σ * f σ
        + ∑' ρ : ↥((quad σ : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight ρ : ℝ) * f ρ := by
  rw [← hf.sum_add_tsum_compl, Cvs.StepA.TopQuadruple.sum_quad_mul σ hq]

end Cvs.WeilForm.EvenExplicitFormulaTameTests
