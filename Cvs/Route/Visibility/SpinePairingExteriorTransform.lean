import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.ReflectedSpineTame
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.EvenExplicitFormulaTameTests
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.ZeroSideSampleMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pairing of a spine vector with a zero's pairing vector is the planted exterior transform

For `80 ≤ 2πx`, `L = log x`, `G` the spine profile, `X = M[1_{(1,∞)}E_G]` at `a = 1/x`, a nontrivial zero `ρ` and
`Φ = x^{(ρ−½)/2} X(ρ) + x^{(½−ρ)/2} X(1 − ρ)`: the centred spine profile `g` has `∫ g ue − i∫ g ve = −Φ/2`, so
`⟪spineMap x a, pairVec(zPoint ρ)⟫ = Im Φ/2`, the same for its even part (every `r ∈ R₁`), and the even pairing
of the even spine window at `ρ` is `Re(Φ²)/4`.
-/

noncomputable section

open Real MeasureTheory Set
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.SpinePairingExteriorTransform
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo ctr)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.WeilForm.SelfConvolutionTransform (cf)

/-- The planted exterior combination `x^{(ρ−½)/2} X(ρ) + x^{(½−ρ)/2} X(1 − ρ)`, `X = M[1_{(1,∞)}E_G]` at `a = 1/x`. -/
def extComb (x : ℕ) (G : ℝ → ℝ) (ρ : ℂ) : ℂ :=
  (x : ℂ) ^ ((ρ - 1 / 2) / 2) * mellinR (ext (1 / x) G) ρ
    + (x : ℂ) ^ ((1 / 2 - ρ) / 2) * mellinR (ext (1 / x) G) (1 - ρ)

/-! ### The even weights -/

/-- **The even weights from the centred transform**: `∫ g ue_z − i ∫ g ve_z = (ctr g z + ctr g (−z))/2`. -/
theorem ue_sub_I_ve_eq_ctr (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (z : ℂ) :
    ((∫ t in -(L / 2)..L / 2, g t * ue z t : ℝ) : ℂ)
        - Complex.I * ((∫ t in -(L / 2)..L / 2, g t * ve z t : ℝ) : ℂ)
      = (ctr L g z + ctr L g (-z)) / 2 := by
  have hi : ∀ w : ℝ → ℝ, Continuous w →
      IntervalIntegrable (fun t => g t * w t) volume (-(L / 2)) (L / 2) :=
    fun w hw => hg.mul_continuousOn hw.continuousOn
  have hue := hi _ (Cvs.StepA.OneZeroParitySectors.continuous_ue z)
  have hve := hi _ (Cvs.StepA.OneZeroParitySectors.continuous_ve z)
  have huo := hi _ (Cvs.StepA.OneZeroParitySectors.continuous_uo z)
  have hvo := hi _ (Cvs.StepA.OneZeroParitySectors.continuous_vo z)
  have hu : ∀ t, ue (-z) t = ue z t := fun t => (Cvs.StepA.OneZeroParitySectors.weights_neg z t).1
  have hv : ∀ t, ve (-z) t = ve z t := fun t => (Cvs.StepA.OneZeroParitySectors.weights_neg z t).2.1
  have huo' : ∀ t, uo (-z) t = -uo z t := fun t => (Cvs.StepA.OneZeroParitySectors.weights_neg z t).2.2.1
  have hvo' : ∀ t, vo (-z) t = -vo z t := fun t => (Cvs.StepA.OneZeroParitySectors.weights_neg z t).2.2.2
  rw [Cvs.StepA.OneZeroParitySectors.ctr_eq L hg z, Cvs.StepA.OneZeroParitySectors.ctr_eq L hg (-z)]
  simp only [hu, hv, huo', hvo', mul_add, mul_neg]
  have hvon : IntervalIntegrable (fun t => -(g t * vo z t)) volume (-(L / 2)) (L / 2) := hvo.neg
  have huon : IntervalIntegrable (fun t => -(g t * uo z t)) volume (-(L / 2)) (L / 2) := huo.neg
  rw [intervalIntegral.integral_add hue hvo, intervalIntegral.integral_add hue hvon,
    intervalIntegral.integral_add huo hve, intervalIntegral.integral_add huon hve,
    intervalIntegral.integral_neg, intervalIntegral.integral_neg]
  push_cast; ring

/-- **The centred transform of a shifted profile**: `ctr_L (f(· + L/2))(ξ) = e^{iξL/2} W_L f(ξ)`. -/
theorem ctr_shift (L : ℝ) (f : ℝ → ℝ) (ξ : ℂ) :
    ctr L (fun t => f (t + L / 2)) ξ
      = Complex.exp ((((L / 2 : ℝ)) : ℂ) * ξ * Complex.I) * Cvs.Detection.windowTransform L (cf f) ξ := by
  have h := Cvs.StepA.OneZeroParitySectors.windowTransform_eq_ctr L (fun t => f (t + L / 2)) ξ
  simp only [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← Complex.exp_add]
  have : (((L / 2 : ℝ)) : ℂ) * ξ * Complex.I + -((((L / 2 : ℝ)) : ℂ) * ξ) * Complex.I = 0 := by ring
  rw [this, Complex.exp_zero, one_mul]

/-- `x^s = e^{s log x}` for `x ≥ 1`. -/
theorem natCast_cpow_eq_exp {x : ℕ} (hx : 1 ≤ x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.ofReal_log (Nat.cast_nonneg x), Complex.ofReal_natCast]

/-! ### At a zero -/

/-- **The centred window transform at a zero**: for `x ≥ 1`, `G` `C¹` on `[0, 1]` with `∫₀¹ G = 0` and
`g = fv x k_G (· + L/2)`, `ctr g (zPoint ρ) = −x^{(½−ρ)/2} X(1 − ρ)` and `ctr g (−zPoint ρ) = −x^{(ρ−½)/2} X(ρ)`. -/
theorem ctr_fv_window_zPoint {x : ℕ} (hx : 1 ≤ x) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) (ρ : nonTrivialZeroSet) :
    ctr (Real.log x) (fun t => Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2))
        (Cvs.ZeroCounting.zPoint ρ)
      = -((x : ℂ) ^ ((1 / 2 - (ρ : ℂ)) / 2) * mellinR (ext (1 / x) G) (1 - ρ))
    ∧ ctr (Real.log x) (fun t => Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2))
        (-Cvs.ZeroCounting.zPoint ρ)
      = -((x : ℂ) ^ (((ρ : ℂ) - 1 / 2) / 2) * mellinR (ext (1 / x) G) ρ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have ha : Real.exp (-Real.log x) = 1 / x := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
  have hL := Real.log_natCast_nonneg x
  have hw := Cvs.Xi.WindowTransformExterior.mellinR_window_eq_neg_ext_of_zero (Real.exp_pos (-Real.log x)) hG hG₁
    hGi ρ.2.2.1 ρ.2.2.2 ρ.2.1
  rw [ha] at hw
  have hv : ∀ θ ∉ Icc (Real.exp (-Real.log x)) 1, window (1 / x) G θ = 0 := by
    rw [ha]; exact fun θ h => Cvs.Xi.EImageWindowPoisson.window_of_notMem G h
  rw [natCast_cpow_eq_exp hx, natCast_cpow_eq_exp hx, ctr_shift, ctr_shift, Cvs.WeilForm.ZeroSideSampleMellin.fv_eq_logWin]
  unfold Cvs.ZeroCounting.zPoint
  rw [Cvs.WeilForm.ZeroSideSampleMellin.windowTransform_logWin_zPoint hL hv, Cvs.WeilForm.ZeroSideSampleMellin.windowTransform_logWin_neg_zPoint hL hv, hw.1, hw.2]
  constructor
  · rw [show ∀ A B C : ℂ, A * (B * -C) = -((A * B) * C) from fun A B C => by ring, ← Complex.exp_add]
    congr 3
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  · rw [show ∀ A B C : ℂ, A * (B * -C) = -((A * B) * C) from fun A B C => by ring, ← Complex.exp_add]
    congr 3
    push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- **The even weights of a window profile at a zero**: under the same hypotheses,
`∫ g ue_{zPoint ρ} − i ∫ g ve_{zPoint ρ} = −Φ/2` with `Φ = x^{(ρ−½)/2} X(ρ) + x^{(½−ρ)/2} X(1 − ρ)`. -/
theorem ue_sub_I_ve_fv_window {x : ℕ} (hx : 1 ≤ x) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    (hg : IntervalIntegrable (fun t => Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2)) volume
      (-(Real.log x / 2)) (Real.log x / 2)) (ρ : nonTrivialZeroSet) :
    ((∫ t in -(Real.log x / 2)..Real.log x / 2,
          Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2) * ue (Cvs.ZeroCounting.zPoint ρ) t : ℝ) : ℂ)
        - Complex.I * ((∫ t in -(Real.log x / 2)..Real.log x / 2,
          Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2) * ve (Cvs.ZeroCounting.zPoint ρ) t : ℝ) : ℂ)
      = -extComb x G ρ / 2 := by
  rw [ue_sub_I_ve_eq_ctr _ hg, (ctr_fv_window_zPoint hx hG hG₁ hGi ρ).1,
    (ctr_fv_window_zPoint hx hG hG₁ hGi ρ).2, extComb]
  ring

/-- The `ue` integral at a zero is `−Re Φ/2`, and the `ve` integral is `Im Φ/2`. -/
theorem integral_ue_ve_fv_window {x : ℕ} (hx : 1 ≤ x) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    (hg : IntervalIntegrable (fun t => Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2)) volume
      (-(Real.log x / 2)) (Real.log x / 2)) (ρ : nonTrivialZeroSet) :
    (∫ t in -(Real.log x / 2)..Real.log x / 2,
        Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2) * ue (Cvs.ZeroCounting.zPoint ρ) t)
        = -(extComb x G ρ).re / 2
    ∧ (∫ t in -(Real.log x / 2)..Real.log x / 2,
        Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) G) (t + Real.log x / 2) * ve (Cvs.ZeroCounting.zPoint ρ) t)
        = (extComb x G ρ).im / 2 := by
  have h := ue_sub_I_ve_fv_window hx hG hG₁ hGi hg ρ
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im] at hre him
  constructor <;> linarith

/-! ### Reflection-symmetrised profiles -/

/-- For an even weight, the symmetrised profile has the same centred pairing. -/
theorem integral_symm_mul {L : ℝ} {g w : ℝ → ℝ} (hg : Integrable g) (hw : Continuous w)
    (hwe : ∀ t, w (-t) = w t) :
    ∫ t in -(L / 2)..L / 2, (g t + g (-t)) / 2 * w t = ∫ t in -(L / 2)..L / 2, g t * w t := by
  have h1 : IntervalIntegrable (fun t => g t * w t) volume (-(L / 2)) (L / 2) :=
    hg.intervalIntegrable.mul_continuousOn hw.continuousOn
  have h2 : IntervalIntegrable (fun t => g (-t) * w t) volume (-(L / 2)) (L / 2) :=
    hg.comp_neg.intervalIntegrable.mul_continuousOn hw.continuousOn
  have hneg : ∫ t in -(L / 2)..L / 2, g (-t) * w t = ∫ t in -(L / 2)..L / 2, g t * w t := by
    have := intervalIntegral.integral_comp_neg (a := -(L / 2)) (b := L / 2) (fun t => g t * w t)
    simp only [neg_neg] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t _ => by simp only [hwe]
  have e : (fun t => (g t + g (-t)) / 2 * w t) = fun t => (g t * w t + g (-t) * w t) / 2 := by
    funext t; ring
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add h1 h2, hneg]
  ring

/-! ### The spine vector and its even part -/

/-- The centred spine profile is integrable. -/
theorem integrable_spine_centred {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Integrable fun t =>
      Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (t + Real.log x / 2) :=
  (Cvs.WeilForm.EvenExplicitFormulaTameTests.integrable_fv (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a)).comp_add_right _

/-- The centred profile of the even spine window is the symmetrised centred spine profile. -/
theorem fv_evenWin_centred {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (t : ℝ) :
    Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.StepA.LowEigenvalueCountSpine.evenWin x a) (t + Real.log x / 2)
      = (Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (t + Real.log x / 2)
          + Cvs.Approximant.SpineCouplingTailPairing.fv x (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (-t + Real.log x / 2)) / 2 := by
  rw [Cvs.StepA.LowEigenvalueCountSpine.evenWin, Cvs.WeilForm.EvenExplicitFormulaTameTests.fv_avg, Cvs.L2a.ReflectedSpineTame.fv_reciprocal (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
    (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a).supp]
  congr 3; ring

/-- **The even spine window's even weights at a zero**: with `g` its centred profile,
`∫ g ue_{zPoint ρ} = −Re Φ/2` and `∫ g ve_{zPoint ρ} = Im Φ/2`. -/
theorem integral_ue_ve_evenWin {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (ρ : nonTrivialZeroSet) :
    (∫ t in -(Real.log x / 2)..Real.log x / 2,
        Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.StepA.LowEigenvalueCountSpine.evenWin x a) (t + Real.log x / 2) * ue (Cvs.ZeroCounting.zPoint ρ) t)
        = -(extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).re / 2
    ∧ (∫ t in -(Real.log x / 2)..Real.log x / 2,
        Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.StepA.LowEigenvalueCountSpine.evenWin x a) (t + Real.log x / 2) * ve (Cvs.ZeroCounting.zPoint ρ) t)
        = (extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).im / 2 := by
  have hx1 : 1 ≤ x := by have := Cvs.StepA.LowEigenvalueCountSpine.two_le hx; omega
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx a
  have hgi := integrable_spine_centred hx a
  have h := integral_ue_ve_fv_window hx1 hG hG₁ hGi hgi.intervalIntegrable ρ
  simp only [fv_evenWin_centred hx a]
  rw [integral_symm_mul hgi (Cvs.StepA.OneZeroParitySectors.continuous_ue _) (Cvs.StepA.OneZeroParitySectors.ue_neg _),
    integral_symm_mul hgi (Cvs.StepA.OneZeroParitySectors.continuous_ve _) (Cvs.StepA.OneZeroParitySectors.ve_neg _)]
  exact h

/-- **The pairing of an even spine class with a zero's pairing vector**: for `80 ≤ 2πx` and a nontrivial zero
`ρ`, `⟪evenPart(spineMap x a), pairVec(zPoint ρ)⟫ = Im Φ/2`. -/
theorem inner_evenPart_spineMap_pairVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx0 : (0 : ℝ) < x)
    (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (ρ : nonTrivialZeroSet) :
    ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
        Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ
      = (extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).im / 2 := by
  rw [Cvs.StepA.LowEigenvalueCountSpine.evenPart_spineMap_eq_wv hx a,
    Cvs.Route.Visibility.ZeroPairingVector.inner_pairVec hx0 _ _ (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.StepA.LowEigenvalueCountSpine.tame_evenWin hx a))]
  exact (integral_ue_ve_evenWin hx a ρ).2

/-- **Every `r ∈ R₁` pairs with a zero's pairing vector through its spine coefficients**: at `80 ≤ 2πx`,
`r = evenPart(spineMap x a)` for some `a` with `⟪r, pairVec(zPoint ρ)⟫ = Im Φ/2`. -/
theorem inner_R1_pairVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx0 : (0 : ℝ) < x) {r : Cvs.Route.L1FloorFromBulkD0.Dom x}
    (hr : r ∈ Cvs.L2a.EvenSectorReflectionBound.R1 x) :
    ∃ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, r = Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)
      ∧ ∀ ρ : nonTrivialZeroSet, ⟪r, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ
          = (extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).im / 2 := by
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  exact ⟨a, rfl, fun ρ => inner_evenPart_spineMap_pairVec hx hx0 a ρ⟩

end Cvs.Route.Visibility.SpinePairingExteriorTransform
