import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.MellinZeroSum
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowTestOperators
import Cvs.WeilForm.ZeroSidePolarized
import Cvs.WeilForm.ZeroSideSampleMellin
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Weil form on the window's test functions: zero side, `D` skew, `1/4 − d²/du²` self-adjoint
For `2 ≤ x`, `L = log x`, the window form at `P = x`, `R = ⌈log₂ x⌉` restricted to `𝓓((0, L), ℝ)` is
`W(f, g) = Σ_ρ (m_ρ/2) Re(f̂(1 − ρ) ĝ(ρ) + ĝ(1 − ρ) f̂(ρ))`. As `D` multiplies `f̂(s)` by `1/2 − s`, each
term changes sign when `D` moves across, so `W(Df, g) = −W(f, Dg)` and `W(Tf, g) = W(f, Tg)` for `T = 1/4 − D²`.
-/

noncomputable section

open scoped Distributions
open Set MeasureTheory Complex

namespace Cvs.WeilForm.WindowTestSelfAdjoint
open Cvs.ZeroCounting

open Cvs.WeilForm.WindowTestOperators
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.WeilForm.MellinZeroSum (Z)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)

/-! ### Test functions in the form domain -/

theorem contDiff_one {x : ℕ} (f : 𝓓(win (Real.log x), ℝ)) : ContDiff ℝ 1 f :=
  f.contDiff.of_le (by simp)

/-- The class in the form domain at `x` of a test function on the window `(0, log x)`. -/
def toDom {x : ℕ} (hx0 : (0 : ℝ) < x) : 𝓓(win (Real.log x), ℝ) →ₗ[ℝ] Dom x where
  toFun f := Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one f))
  map_add' f g := by
    apply Subtype.ext; apply Subtype.ext; apply Lp.ext
    refine (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans ?_
    simp only [Submodule.coe_add]
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
    filter_upwards [Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one f)),
      Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one g))] with s h1 h2
    rw [Pi.add_apply, h1, h2, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]
  map_smul' a f := by
    apply Subtype.ext; apply Subtype.ext; apply Lp.ext
    refine (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans ?_
    simp only [Submodule.coe_smul, RingHom.id_apply]
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
    filter_upwards [Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one f))] with s h1
    rw [Pi.smul_apply, h1, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-- The window Weil form on test functions, `W(f, g) = Q(w_f, w_g)` at `P = x`, `R = ⌈log₂ x⌉`. -/
def weil {x : ℕ} (hx0 : (0 : ℝ) < x) : LinearMap.BilinForm ℝ 𝓓(win (Real.log x), ℝ) :=
  (Bx x).compl₁₂ (toDom hx0) (toDom hx0)

theorem weil_apply {x : ℕ} (hx0 : (0 : ℝ) < x) (f g : 𝓓(win (Real.log x), ℝ)) :
    weil hx0 f g = Bx x (toDom hx0 f) (toDom hx0 g) := rfl

/-! ### The Mellin transform of a window test function -/

/-- **`M[ofWin x f](s) = x^{1/2 − s} f̂(s)`** for a test function `f` on `(0, log x)`. -/
theorem mellinR_ofWin {x : ℕ} (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)) (s : ℂ) :
    mellinR (Cvs.WeilForm.TameClassesFormDense.ofWin x f) s = cexp (Real.log x * (1 / 2 - s)) * hat (Real.log x) f s := by
  have hL0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hv : ∀ θ ∉ Icc (Real.exp (-Real.log x)) 1, Cvs.WeilForm.TameClassesFormDense.ofWin x f θ = 0 := by
    intro θ hθ
    have he : Real.exp (-Real.log x) = 1 / (x : ℝ) := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
    rw [he] at hθ
    exact indicator_of_notMem (fun h => hθ (Ico_subset_Icc_self h)) _
  set ξ : ℂ := -I * (1 / 2 - s) with hξ
  have hs : 1 / 2 - ξ * I = s := by rw [hξ]; linear_combination (1 / 2 - s) * I_sq
  have hW := Cvs.WeilForm.ZeroSideSampleMellin.windowTransform_logWin hL0 hv ξ
  rw [hs] at hW
  have hwin : Cvs.Detection.windowTransform (Real.log x)
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.WeilForm.ZeroSideSampleMellin.logWin (Real.log x) (Cvs.WeilForm.TameClassesFormDense.ofWin x f))) ξ = hat (Real.log x) f s := by
    rw [← hs, ← windowTransform_eq_hat]
    unfold Cvs.Detection.windowTransform
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hL0] at hu
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf]
    rw [← Cvs.WeilForm.ZeroSideSampleMellin.fv_eq_logWin, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0]
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h, indicator_of_notMem (by simp), apply_L]
    · rw [indicator_of_mem (show u ∈ Ico 0 (Real.log x) from ⟨hu.1, h⟩)]
  rw [hwin] at hW
  have h0 : ((Real.log x : ℝ) : ℂ) * (1 / 2 - s) + -(((Real.log x : ℝ) : ℂ) * ξ) * I = 0 := by
    rw [hξ]; linear_combination (((Real.log x : ℝ) : ℂ) * (1 / 2 - s)) * I_sq
  rw [hW, ← mul_assoc, ← Complex.exp_add, h0, Complex.exp_zero, one_mul]

/-- `D` in the Mellin picture: `M[ofWin x (Df)](s) = (1/2 − s) M[ofWin x f](s)`. -/
theorem mellinR_ofWin_opD {x : ℕ} (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)) (s : ℂ) :
    mellinR (Cvs.WeilForm.TameClassesFormDense.ofWin x (opD _ f)) s = (1 / 2 - s) * mellinR (Cvs.WeilForm.TameClassesFormDense.ofWin x f) s := by
  rw [mellinR_ofWin hx0, mellinR_ofWin hx0, hat_opD]
  ring

/-- `T` in the Mellin picture: `M[ofWin x (Tf)](s) = s(1 − s) M[ofWin x f](s)`. -/
theorem mellinR_ofWin_opT {x : ℕ} (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)) (s : ℂ) :
    mellinR (Cvs.WeilForm.TameClassesFormDense.ofWin x (opT _ f)) s = s * (1 - s) * mellinR (Cvs.WeilForm.TameClassesFormDense.ofWin x f) s := by
  rw [mellinR_ofWin hx0, mellinR_ofWin hx0, hat_opT]
  ring

/-! ### The explicit formula on test functions -/

/-- The polarized zero-side term `(m_ρ/2) Re(f̂(1 − ρ) ĝ(ρ) + ĝ(1 − ρ) f̂(ρ))`. -/
def term (L : ℝ) (f g : ℝ → ℝ) (ρ : Z) : ℝ :=
  (Cvs.Criterion.divisorWeight ρ : ℝ)
    * (hat L f (1 - ρ) * hat L g ρ + hat L g (1 - ρ) * hat L f ρ).re / 2

theorem crossTerm_ofWin {x : ℕ} (hx0 : (0 : ℝ) < x) (f g : 𝓓(win (Real.log x), ℝ)) (ρ : Z) :
    Cvs.WeilForm.ZeroSidePolarized.crossTerm (Cvs.WeilForm.TameClassesFormDense.ofWin x f) (Cvs.WeilForm.TameClassesFormDense.ofWin x g) ρ = term (Real.log x) f g ρ := by
  have he : cexp (((Real.log x : ℝ) : ℂ) * (1 / 2 - (1 - (ρ : ℂ))))
      * cexp (((Real.log x : ℝ) : ℂ) * (1 / 2 - (ρ : ℂ))) = 1 := by
    rw [← Complex.exp_add, show ((Real.log x : ℝ) : ℂ) * (1 / 2 - (1 - (ρ : ℂ)))
      + ((Real.log x : ℝ) : ℂ) * (1 / 2 - (ρ : ℂ)) = 0 by ring, Complex.exp_zero]
  unfold Cvs.WeilForm.ZeroSidePolarized.crossTerm term
  rw [mellinR_ofWin hx0, mellinR_ofWin hx0, mellinR_ofWin hx0, mellinR_ofWin hx0]
  congr 3
  linear_combination (hat (Real.log x) f (1 - ρ) * hat (Real.log x) g ρ
    + hat (Real.log x) g (1 - ρ) * hat (Real.log x) f ρ) * he

/-- **The explicit formula on test functions**: for `2 ≤ x`,
`W(f, g) = Σ_ρ (m_ρ/2) Re(f̂(1 − ρ) ĝ(ρ) + ĝ(1 − ρ) f̂(ρ))`. -/
theorem hasSum_weil {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x) (f g : 𝓓(win (Real.log x), ℝ)) :
    HasSum (term (Real.log x) f g) (weil hx0 f g) := by
  obtain ⟨h1, h2⟩ := Cvs.WeilForm.ZeroSidePolarized.QWbil_wv_eq_zeroSum hx (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one f))
    (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one g))
  have hs : Summable (term (Real.log x) f g) := h2.congr (crossTerm_ofWin hx0 f g)
  convert hs.hasSum using 1
  rw [weil_apply]
  exact h1.trans (tsum_congr (crossTerm_ofWin hx0 f g))

/-! ### `D` is skew and `T = 1/4 − D²` is self-adjoint for the Weil form -/

/-- Moving `D` across a zero-side term changes its sign. -/
theorem term_opD {L : ℝ} (f g : 𝓓(win L, ℝ)) (ρ : Z) :
    term L (opD L f) g ρ = -term L f (opD L g) ρ := by
  unfold term
  rw [hat_opD, hat_opD, hat_opD, hat_opD]
  have : (1 / 2 - (1 - (ρ : ℂ))) * hat L f (1 - ρ) * hat L g ρ + hat L g (1 - ρ) * ((1 / 2 - ρ) * hat L f ρ)
      = -(hat L f (1 - ρ) * ((1 / 2 - ρ) * hat L g ρ)
        + (1 / 2 - (1 - (ρ : ℂ))) * hat L g (1 - ρ) * hat L f ρ) := by ring
  rw [this, Complex.neg_re]
  ring

/-- **`D = d/du` is skew for the Weil form**: `W(Df, g) = −W(f, Dg)`. -/
theorem isSkewAdjoint_opD {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x) :
    (weil hx0).IsSkewAdjoint (opD (Real.log x)) := fun f g => by
  have h1 := hasSum_weil hx0 hx (opD _ f) g
  have h2 := (hasSum_weil hx0 hx f (opD _ g)).neg
  simp only [← term_opD] at h2
  rw [Pi.neg_apply, map_neg, h1.unique h2]

/-- `W(Df, g) = −W(f, Dg)`. -/
theorem weil_opD {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x) (f g : 𝓓(win (Real.log x), ℝ)) :
    weil hx0 (opD _ f) g = -weil hx0 f (opD _ g) := by
  rw [isSkewAdjoint_opD hx0 hx f g, Pi.neg_apply, map_neg]

/-- **`T = 1/4 − d²/du²` is self-adjoint for the Weil form**: `W(Tf, g) = W(f, Tg)`. -/
theorem isSelfAdjoint_opT {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x) :
    (weil hx0).IsSelfAdjoint (opT (Real.log x)) := fun f g => by
  have hT : ∀ h : 𝓓(win (Real.log x), ℝ), opT _ h = (1 / 4 : ℝ) • h - opD _ (opD _ h) := fun h => by
    simp [opT]
  rw [hT, hT, LinearMap.map_sub₂, LinearMap.map_smul₂, map_sub, map_smul, weil_opD hx0 hx,
    weil_opD hx0 hx f (opD _ g)]
  ring

/-- For any point `p` and weight `c`, `D` is skew for the pairing of `p` with `1 − p`. -/
theorem pair_opD_any {L : ℝ} (f g : 𝓓(win L, ℝ)) (c : ℝ) (p : ℂ) :
    c * (hat L (opD L f) (1 - p) * hat L g p + hat L g (1 - p) * hat L (opD L f) p).re / 2
      = -(c * (hat L f (1 - p) * hat L (opD L g) p + hat L (opD L g) (1 - p) * hat L f p).re / 2) := by
  rw [hat_opD, hat_opD, hat_opD, hat_opD]
  have : (1 / 2 - (1 - p)) * hat L f (1 - p) * hat L g p + hat L g (1 - p) * ((1 / 2 - p) * hat L f p)
      = -(hat L f (1 - p) * ((1 / 2 - p) * hat L g p) + (1 / 2 - (1 - p)) * hat L g (1 - p) * hat L f p) := by
    ring
  rw [this, Complex.neg_re]
  ring

end Cvs.WeilForm.WindowTestSelfAdjoint
