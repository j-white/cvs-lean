import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierNegativeFreqRate
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipPhaseDecay
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Prolate.Hardy.ReflectedWaveSplit
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Upstream.ConfocalEllipseDeformation
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyHalvesFourier
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.JordanArcIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The carrier bound for `J_c` with a holomorphic phase on a confocal half-ellipse

For `f = Re F` on `I`, `F` holomorphic on the half-ellipse `cosh(η + iθ)/2`, `η ≤ η₀`, with `|F| ≤ M₀` on `[−L, L]` and
`|F e^{−i(c/2)S}| ≤ M₁e^{−t sin θ}` on its arc (`L = cosh η₀/2`, `B = sinh η₀/2`):
`‖J_c f‖ ≤ M₀ + 2(M₁Lπ(2πtB)^{−1/2} + M₀√(2(L − ½)))`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform
open Complex (I)
open scoped Interval

namespace Cvs.Prolate.Hardy.CarrierBoundHolomorphicPhase
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R)
open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C posProj mulOp reLp ofRealLp ext0 wR wInvI hardyJ)
open Cvs.Upstream.FourierLpConjReflect (conjLp)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH Qrect qF)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (toL2)

/-- The amplitude `A = Fe^{−icz}`, so that the carrier `Ae^{icx}/w` is `F/w`. -/
def ampF (c : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ := F z * Complex.exp (-(I * c * z))

/-- `k = 1_{(−L, L]} F/w`. -/
def kL (c L : ℝ) (F : ℂ → ℂ) : ℝ → ℂ := (Ioc (-L) L).indicator (carH c (ampF c F))

theorem ampF_mul_exp (c : ℝ) (F : ℂ → ℂ) (z : ℂ) : ampF c F z * Complex.exp (I * c * z) = F z := by
  unfold ampF; rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem carH_ampF (c : ℝ) (F : ℂ → ℂ) (x : ℝ) : carH c (ampF c F) x = F (x : ℂ) * (wR (c / 2) x)⁻¹ := by
  unfold carH; rw [ampF_mul_exp]

theorem continuousOn_carH_ampF (c : ℝ) {F : ℂ → ℂ} {L : ℝ} (hF : ∀ x : ℝ, |x| ≤ L → ContinuousAt F x) :
    ContinuousOn (carH c (ampF c F)) (Icc (-L) L) := by
  have hFr : ContinuousOn (fun x : ℝ => F x) (Icc (-L) L) := fun x hx =>
    ((hF x (abs_le.2 hx)).comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have e : carH c (ampF c F) = fun x : ℝ => F (x : ℂ) * (wR (c / 2) x)⁻¹ := funext (carH_ampF c F)
  rw [e]
  exact hFr.mul ((Cvs.Prolate.Hardy.CarrierUpperHalfPlane.continuous_wR (c / 2)).continuousOn.inv₀ fun x _ => Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_ne_zero _ x)

/-- `𝓕k(ξ) = ∫_{−L}^{L} e^{−2πixξ}F(x)/w(x) dx`. -/
theorem fourier_kL {c L : ℝ} (ξ : ℝ) (F : ℂ → ℂ) (hL : -L ≤ L) :
    𝓕 (kL c L F) ξ = ∫ x in -L..L, qF c ξ (ampF c F) x := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le hL,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  ext x
  unfold kL qF
  by_cases hx : x ∈ Ioc (-L) L
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

theorem differentiableOn_Qrect_of (c ξ : ℝ) {F : ℂ → ℂ} {η₀ : ℝ}
    (hF : ∀ ζ ∈ [[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]], DifferentiableAt ℂ F ((1 / 2 : ℂ) * Complex.cosh ζ)) :
    DifferentiableOn ℂ (Qrect c ξ (ampF c F)) ([[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]]) := by
  intro ζ hζ
  have hAc : DifferentiableAt ℂ (fun ζ => ampF c F ((1 / 2 : ℂ) * Complex.cosh ζ)) ζ := by
    unfold ampF
    exact ((hF ζ hζ).comp ζ (by fun_prop)).mul (by fun_prop)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Qrect
  exact DifferentiableAt.mul (by fun_prop) (DifferentiableAt.mul (DifferentiableAt.mul hAc (by fun_prop))
    (by fun_prop))

/-- **The contour form** `𝓕k(ξ) = −i∫_0^π Q(η₀ + iθ) sinh(η₀ + iθ)/2 dθ`. -/
theorem fourier_kL_eq_arc (c ξ : ℝ) {F : ℂ → ℂ} {η₀ : ℝ} (hη : 0 ≤ η₀)
    (hF : ∀ ζ ∈ [[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]], DifferentiableAt ℂ F ((1 / 2 : ℂ) * Complex.cosh ζ))
    (hFx : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ContinuousAt F x) :
    𝓕 (kL c (1 / 2 * Real.cosh η₀) F) ξ = -I * ∫ θ in (0 : ℝ)..π, Qrect c ξ (ampF c F) (η₀ + θ * I) *
      (((1 / 2 : ℝ) : ℂ) * Complex.sinh (η₀ + θ * I)) := by
  rw [fourier_kL ξ F (by have := Real.cosh_pos η₀; linarith)]
  have hq : IntervalIntegrable (qF c ξ (ampF c F)) volume (-(1 / 2 * Real.cosh η₀)) (1 / 2 * Real.cosh η₀) := by
    have hc : ContinuousOn (qF c ξ (ampF c F)) (Icc (-(1 / 2 * Real.cosh η₀)) (1 / 2 * Real.cosh η₀)) := by
      have e1 : Continuous fun x : ℝ => Complex.exp (↑(-2 * π * x * ξ) * I) := by fun_prop
      exact e1.continuousOn.smul (continuousOn_carH_ampF c hFx)
    exact hc.intervalIntegrable_of_Icc (by have := Real.cosh_pos η₀; linarith)
  exact Cvs.Upstream.ConfocalEllipseDeformation.integral_eq_arc (a := 1 / 2) (by norm_num) hη (differentiableOn_Qrect_of c ξ hF) hq
    (fun η hη => by simpa using Cvs.Prolate.Hardy.CarrierNegativeFrequencies.h1 c ξ (ampF c F) hη.1)
    (fun η hη => by simpa using Cvs.Prolate.Hardy.CarrierNegativeFrequencies.h2 c ξ (ampF c F) hη.1)
    (fun y hy => by simpa using Cvs.Prolate.Hardy.CarrierNegativeFrequencies.h3 c ξ (ampF c F) hy)

/-- The arc integrand with the phase damping: `|Q(η₀ + iθ)| ≤ M₁e^{−(t − 2πξB) sin θ}`. -/
theorem norm_Qrect_arc_of (c ξ η₀ t M₁ : ℝ) {F : ℂ → ℂ} (θ : ℝ)
    (hM : ‖F ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I)) *
      Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))‖ ≤
        M₁ * Real.exp (-t * Real.sin θ)) :
    ‖Qrect c ξ (ampF c F) (η₀ + θ * I)‖ ≤
      M₁ * Real.exp (-(t - 2 * π * ξ * (1 / 2 * Real.sinh η₀)) * Real.sin θ) := by
  set z := (1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I)
  have hz : z = ((1 / 2 * Real.cosh η₀ * Real.cos θ : ℝ) : ℂ) + I * ((1 / 2 * Real.sinh η₀ * Real.sin θ : ℝ) : ℂ) :=
    by
      have h := Cvs.Upstream.JordanArcIntegral.cosh_arc (1 / 2) η₀ θ
      simp only [z]
      push_cast at h ⊢
      linear_combination h
  have e : Qrect c ξ (ampF c F) (η₀ + θ * I) = Complex.exp (((-2 * π * ξ : ℝ) : ℂ) * z * I) *
      (F z * Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))) := by
    unfold Qrect; rw [ampF_mul_exp]
  rw [e, norm_mul, Complex.norm_exp]
  have hre : (((-2 * π * ξ : ℝ) : ℂ) * z * I).re = 2 * π * ξ * (1 / 2 * Real.sinh η₀) * Real.sin θ := by
    rw [hz]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  calc Real.exp (2 * π * ξ * (1 / 2 * Real.sinh η₀) * Real.sin θ) * ‖F z * Complex.exp _‖ ≤
        Real.exp (2 * π * ξ * (1 / 2 * Real.sinh η₀) * Real.sin θ) * (M₁ * Real.exp (-t * Real.sin θ)) :=
        mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = M₁ * Real.exp (-(t - 2 * π * ξ * (1 / 2 * Real.sinh η₀)) * Real.sin θ) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- **The negative-frequency bound** `|𝓕k(ξ)| ≤ M₁Lπ/(t − 2πξB)` for `ξ ≤ 0`. -/
theorem norm_fourier_kL_le {c ξ η₀ t M₁ : ℝ} (hη : 0 ≤ η₀) (ht : 0 < t) (hξ : ξ ≤ 0) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ [[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]], DifferentiableAt ℂ F ((1 / 2 : ℂ) * Complex.cosh ζ))
    (hFx : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ContinuousAt F x)
    (hM : ∀ θ ∈ Icc 0 π, ‖F ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I)) *
      Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))‖ ≤
        M₁ * Real.exp (-t * Real.sin θ)) :
    ‖𝓕 (kL c (1 / 2 * Real.cosh η₀) F) ξ‖ ≤
      M₁ * (1 / 2 * Real.cosh η₀) * (π / (t - 2 * π * ξ * (1 / 2 * Real.sinh η₀))) := by
  have hB : 0 ≤ 1 / 2 * Real.sinh η₀ := by have := Real.sinh_nonneg_iff.2 hη; positivity
  have ht' : 0 < t - 2 * π * ξ * (1 / 2 * Real.sinh η₀) := by
    have : 2 * π * ξ * (1 / 2 * Real.sinh η₀) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hξ) hB
    linarith
  rw [fourier_kL_eq_arc c ξ hη hF hFx, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact Cvs.Upstream.JordanArcIntegral.norm_arc_le (a := 1 / 2) (η₀ := η₀) (by norm_num) ht' (Q := Qrect c ξ (ampF c F))
    (fun θ hθ => norm_Qrect_arc_of c ξ η₀ t M₁ θ (hM θ hθ))

theorem memLp_kL (c L : ℝ) {F : ℂ → ℂ} (hFx : ∀ x : ℝ, |x| ≤ L → ContinuousAt F x) :
    Integrable (kL c L F) ∧ MemLp (kL c L F) 2 (volume : Measure ℝ) :=
  Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integrable_memLp_indicator (continuousOn_carH_ampF c hFx)

/-- **The arc estimate in `L²`**: `‖k − P₊k‖² ≤ (M₁Lπ)²/(t · 2πB)`. -/
theorem norm_sub_posProj_kL_sq_le {c η₀ t M₁ : ℝ} (hη : 0 < η₀) (ht : 0 < t) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ [[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]], DifferentiableAt ℂ F ((1 / 2 : ℂ) * Complex.cosh ζ))
    (hFx : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ContinuousAt F x)
    (hM : ∀ θ ∈ Icc 0 π, ‖F ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I)) *
      Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))‖ ≤
        M₁ * Real.exp (-t * Real.sin θ)) :
    ‖(memLp_kL c _ hFx).2.toLp _ - posProj ((memLp_kL c _ hFx).2.toLp _)‖ ^ 2 ≤
      (M₁ * (1 / 2 * Real.cosh η₀) * π) ^ 2 * (1 / (t * (2 * π * (1 / 2 * Real.sinh η₀)))) := by
  set p := t
  set q := 2 * π * (1 / 2 * Real.sinh η₀) with hq
  have hq0 : 0 < q := by have := Real.sinh_pos_iff.2 hη; positivity
  rw [Cvs.Upstream.HardyHalvesFourier.norm_sub_posProj_toLp_sq (memLp_kL c _ hFx).1 (memLp_kL c _ hFx).2,
    Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integral_Iio_eq_Ioi_neg (fun ξ => ‖𝓕 (kL c (1 / 2 * Real.cosh η₀) F) ξ‖ ^ 2),
    ← Cvs.Prolate.Hardy.LipPhaseDecay.integral_inv_sq_Ioi ht hq0, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    ((Cvs.Prolate.Hardy.LipPhaseDecay.integrableOn_inv_sq_Ioi ht hq0).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hξ0 : -ξ ≤ 0 := by linarith [hξ.out]
  have hb := norm_fourier_kL_le hη.le ht hξ0 hF hFx hM
  have ht' : t - 2 * π * -ξ * (1 / 2 * Real.sinh η₀) = p + q * ξ := by rw [hq]; ring
  rw [ht'] at hb
  have hpq : 0 < p + q * ξ := by nlinarith [hξ.out]
  calc ‖𝓕 (kL c (1 / 2 * Real.cosh η₀) F) (-ξ)‖ ^ 2 ≤
        (M₁ * (1 / 2 * Real.cosh η₀) * (π / (p + q * ξ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (M₁ * (1 / 2 * Real.cosh η₀) * π) ^ 2 * (1 / (p + q * ξ) ^ 2) := by field_simp

/-! ### `J_c` on `Re F` -/

/-- `1_{(−L, L]}H − 1_I H = 1_{symS ½ L}H` at every `x ≠ −½`, for `L ≥ ½`. -/
theorem kL_sub_indicator (c : ℝ) (F : ℂ → ℂ) {L : ℝ} (hL : 1 / 2 ≤ L) {x : ℝ} (hx : x ≠ -(1 / 2)) :
    kL c L F x - cI.indicator (carH c (ampF c F)) x = (symS (1 / 2) L).indicator (carH c (ampF c F)) x := by
  unfold kL symS
  by_cases hI : x ∈ cI
  · have hx' : (-1 / 2 : ℝ) ≠ x := fun h => hx (by rw [← h]; norm_num)
    have h1 : x ∈ Ioc (-L) L := ⟨by have := lt_of_le_of_ne hI.1 hx'; linarith, by linarith [hI.2]⟩
    have h2 : x ∉ Ioc (1 / 2 : ℝ) L ∪ Ioc (-L) (-(1 / 2)) := by
      rintro (h | h)
      · linarith [h.1, hI.2]
      · exact hx (le_antisymm h.2 (by linarith [hI.1]))
    rw [indicator_of_mem h1, indicator_of_mem hI, indicator_of_notMem h2, sub_self]
  · rw [indicator_of_notMem hI, sub_zero]
    have hI' : x < -(1 / 2) ∨ 1 / 2 < x := by
      by_contra h; push Not at h; exact hI ⟨by linarith [h.1], h.2⟩
    by_cases hK : x ∈ Ioc (-L) L
    · have : x ∈ Ioc (1 / 2 : ℝ) L ∪ Ioc (-L) (-(1 / 2)) := by
        rcases hI' with h | h
        · exact Or.inr ⟨hK.1, h.le⟩
        · exact Or.inl ⟨h, hK.2⟩
      rw [indicator_of_mem hK, indicator_of_mem this]
    · have : x ∉ Ioc (1 / 2 : ℝ) L ∪ Ioc (-L) (-(1 / 2)) := by
        rintro (h | h)
        · exact hK ⟨by linarith [h.1], h.2⟩
        · exact hK ⟨h.1, by linarith [h.2]⟩
      rw [indicator_of_notMem hK, indicator_of_notMem this]

/-- The real input `1_I f / w = (h + h̄)/2` for `f = Re F` on `I`. -/
theorem input_eq {c : ℝ} (hc : 0 ≤ c) {F : ℂ → ℂ} (hm : MemLp (cI.indicator (carH c (ampF c F))) 2 volume)
    {f : L2I} (hf : (f : ℝ → ℝ) =ᵐ[volume.restrict cI] fun x : ℝ => (F x).re) :
    mulOp (wInvI (c / 2)) (ofRealLp (ext0 f)) =
      (1 / 2 : ℝ) • (toL2 (cI.indicator (carH c (ampF c F))) +
        conjLp (toL2 (cI.indicator (carH c (ampF c F))))) := by
  have hb : 0 ≤ c / 2 := by positivity
  set H := toL2 (cI.indicator (carH c (ampF c F)))
  have hE : (ext0 f : ℝ → ℝ) =ᵐ[volume] cI.indicator (f : ℝ → ℝ) :=
    MemLp.coeFn_toLp (Cvs.Prolate.Hardy.HardyExtensionOperator.memLp_indicator_L2I f)
  have hE' := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 hf
  have hFc : (ofRealLp (ext0 f) : ℝ → ℂ) =ᵐ[volume] fun x => ((ext0 f : ℝ → ℝ) x : ℂ) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  refine Lp.ext ?_
  filter_upwards [Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wInvI hb) (ofRealLp (ext0 f)), hFc, hE, hE',
    Lp.coeFn_smul (1 / 2 : ℝ) (H + conjLp H), Lp.coeFn_add H (conjLp H),
    Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp H, Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 hm] with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, Pi.smul_apply, h6, Pi.add_apply, h7]
  simp only [H] at h8 ⊢
  rw [h8]
  by_cases hx : x ∈ cI
  · rw [indicator_of_mem hx, indicator_of_mem hx, Cvs.Prolate.Hardy.HardyExtensionOperator.wInvI, indicator_of_mem hx]
    set r := Real.exp (-(c / 2) * (Cvs.Prolate.Hardy.HardyExtensionOperator.sS x).im)
    have hw : wR (c / 2) x = (r : ℂ) := Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_on_I hx
    rw [carH_ampF, hw, ← Complex.ofReal_inv]
    set z := F x
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
    · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp

/-- **The phase carrier bound** `‖J_c f‖ ≤ M₀ + 2(M₁Lπ(2πtB)^{−1/2} + M₀√(2(L − ½)))`. -/
theorem norm_hardyJ_le {c η₀ t M₀ M₁ : ℝ} (hc : 0 < c) (hη : 0 < η₀) (ht : 0 < t) {F : ℂ → ℂ}
    (hF : ∀ ζ ∈ [[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]], DifferentiableAt ℂ F ((1 / 2 : ℂ) * Complex.cosh ζ))
    (hFx : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ContinuousAt F x)
    (hM₀ : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ‖F x‖ ≤ M₀)
    (hM : ∀ θ ∈ Icc 0 π, ‖F ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I)) *
      Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))‖ ≤
        M₁ * Real.exp (-t * Real.sin θ))
    {f : L2I} (hf : (f : ℝ → ℝ) =ᵐ[volume.restrict cI] fun x : ℝ => (F x).re) :
    ‖hardyJ c f‖ ≤ M₀ + 2 * (M₁ * (1 / 2 * Real.cosh η₀) * π *
      √(1 / (t * (2 * π * (1 / 2 * Real.sinh η₀)))) + M₀ * √(2 * (1 / 2 * Real.cosh η₀ - 1 / 2))) := by
  set L := 1 / 2 * Real.cosh η₀ with hLdef
  have hL : 1 / 2 ≤ L := by rw [hLdef]; linarith [Real.one_le_cosh η₀]
  have hb : 0 ≤ c / 2 := by positivity
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0 (by simp; linarith))
  have hM₁0 : 0 ≤ M₁ := by
    have h := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.pi_pos.le⟩)
    rwa [Real.sin_zero, mul_zero, Real.exp_zero, mul_one] at h
  set H := carH c (ampF c F)
  have hHc := continuousOn_carH_ampF c hFx
  have hmI : MemLp (cI.indicator H) 2 (volume : Measure ℝ) := by
    have hc' : ContinuousOn H cI := hHc.mono (Icc_subset_Icc (by linarith) (by linarith))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
    refine (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (MemLp.of_bound
      (hc'.aestronglyMeasurable measurableSet_Icc) C ?_)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC x hx
  have hmS : MemLp ((symS (1 / 2) L).indicator H) 2 (volume : Measure ℝ) := by
    rw [Cvs.Prolate.Hardy.LipSymmetricPieces.indicator_symS (by norm_num)]
    exact (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integrable_memLp_indicator (hHc.mono (Icc_subset_Icc (by linarith) le_rfl))).2.add
      (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integrable_memLp_indicator (hHc.mono (Icc_subset_Icc le_rfl (by linarith)))).2
  set h := toL2 (cI.indicator H)
  set k := toL2 (kL c L F)
  set m := toL2 ((symS (1 / 2) L).indicator H)
  have hkm : h = k - m := by
    refine Lp.ext ?_
    filter_upwards [Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 hmI, Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (memLp_kL c L hFx).2, Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 hmS,
      Lp.coeFn_sub k m, Cvs.Prolate.Hardy.SpectrumCosineHighpass.ae_ne (-(1 / 2))] with x h1 h2 h3 h4 hx
    rw [h1, h4, Pi.sub_apply, h2, h3, ← kL_sub_indicator c F hL hx]
    ring
  have hh : h = k - m - ((0 : L2C) + 0) - 0 := by rw [hkm]; abel
  have hsplit := Cvs.Prolate.Hardy.ReflectedWaveSplit.split h k m 0 0 0 hh
  simp only [map_zero, sub_zero, add_zero, sub_self] at hsplit
  have hJ : hardyJ c f = reLp (mulOp (wR (c / 2)) (posProj h + conjLp (h - posProj h))) := by
    have hJ0 : hardyJ c f =
        (2 : ℝ) • reLp (mulOp (wR (c / 2)) (posProj (mulOp (wInvI (c / 2)) (ofRealLp (ext0 f))))) := rfl
    rw [hJ0, input_eq hc.le hmI hf, ContinuousLinearMap.map_smul_of_tower, map_add, Cvs.Prolate.Hardy.ReflectedWaveSplit.posProj_conjLp,
      ContinuousLinearMap.map_smul_of_tower, map_smul, smul_smul]
    norm_num
    rfl
  rw [hJ, hsplit, map_add, map_add]
  -- the interior carrier `Re(wh) = Re F` on `I`
  have t1 : ‖reLp (mulOp (wR (c / 2)) h)‖ ≤ M₀ := by
    set g : ℝ → ℝ := cI.indicator fun _ => M₀
    have hg : MemLp g 2 (volume : Measure ℝ) :=
      (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (memLp_const M₀)
    have hle : ‖reLp (mulOp (wR (c / 2)) h)‖ ≤ ‖hg.toLp g‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [Cvs.Prolate.Hardy.ReflectedWaveSplit.coeFn_reLp (mulOp (wR (c / 2)) h), Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) h,
        Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 hmI, hg.coeFn_toLp] with x h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      simp only [g]
      by_cases hx : x ∈ cI
      · rw [indicator_of_mem hx, indicator_of_mem hx, Real.norm_eq_abs, Real.norm_of_nonneg hM₀0]
        have hxx : |x| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        have e : wR (c / 2) x * H x = F x := by
          simp only [H]; rw [carH_ampF]; field_simp [Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_ne_zero]
        rw [e]
        exact (Complex.abs_re_le_norm _).trans (hM₀ x hxx)
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
    refine hle.trans ?_
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet]
    have : (volume.restrict cI) Set.univ = 1 := by
      rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
    rw [eLpNorm_const _ (by norm_num) (by rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]; norm_num), this]
    simp [Real.eNorm_of_nonneg hM₀0, ENNReal.toReal_ofReal hM₀0]
  have t2 := Cvs.Prolate.Hardy.ReflectedWaveSplit.norm_reflect_le (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.norm_wR_le hb) (k - posProj k - (m - posProj m))
  have tk : ‖k - posProj k‖ ≤ M₁ * L * π * √(1 / (t * (2 * π * (1 / 2 * Real.sinh η₀)))) := by
    have h2 := norm_sub_posProj_kL_sq_le hη ht hF hFx hM
    rw [show k = (memLp_kL c L hFx).2.toLp _ from Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq _]
    exact Cvs.Prolate.Hardy.ColumnWaveErrorBound.norm_le_of_sq_le (by positivity) h2
  have tm : ‖m - posProj m‖ ≤ M₀ * √(2 * (L - 1 / 2)) := by
    refine (Cvs.Upstream.HardyHalvesFourier.norm_sub_posProj_le m).trans ?_
    have h2 := Cvs.Prolate.Hardy.LipSymmetricPieces.norm_sq_symS_le (c := c) (a := 1 / 2) (b := L) le_rfl hL (A := ampF c F)
      (fun x hx => by
        have hxL : |x| ≤ L := by
          rcases hx with hx | hx
          · rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
          · rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        unfold ampF
        rw [norm_mul, show -(I * (c : ℂ) * (x : ℂ)) = ((-(c * x) : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hM₀ x hxL) hmS
    rw [show m = hmS.toLp _ from Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq _]
    exact Cvs.Prolate.Hardy.ColumnWaveErrorBound.norm_le_of_sq_le hM₀0 (by rw [mul_comm (2 : ℝ)] at h2 ⊢; linarith)
  have hE : ‖k - posProj k - (m - posProj m)‖ ≤ ‖k - posProj k‖ + ‖m - posProj m‖ := norm_sub_le _ _
  calc _ ≤ ‖reLp (mulOp (wR (c / 2)) h)‖ + ‖reLp (mulOp (wR (c / 2)) (conjLp (k - posProj k - (m - posProj m)) -
        (k - posProj k - (m - posProj m))))‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end Cvs.Prolate.Hardy.CarrierBoundHolomorphicPhase

end
