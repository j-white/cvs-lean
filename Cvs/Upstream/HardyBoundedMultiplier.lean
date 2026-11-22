import Mathlib
import Cvs.Prolate.Hardy.HardyExtensionHighpass
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Upstream.FourierLaplaceExtension
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.UpperHalfPlaneIntegralVanishes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `H²` of the upper half-plane is a module over bounded holomorphic functions

`Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule` holds: testing `𝓕(Φ u)` on `(−∞, 0)` against `𝓕⁻ g` moves `Φ` onto the test side, and for
`ξ ≥ 0` the integral `∫ e^{2πixξ} Φ(x) G(x) dx` vanishes by `Cvs.Upstream.UpperHalfPlaneIntegralVanishes`, `G` the Fourier–Laplace extension of `g`.
-/

noncomputable section

open Real Set MeasureTheory Filter FourierTransform SchwartzMap
open Complex (I)
open scoped ContDiff

namespace Cvs.Upstream.HardyBoundedMultiplier
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe mulOp)
open Cvs.Upstream.FourierLaplaceExtension (flExt)

/-- The conjugate of the inverse Fourier transform of a real function is its Fourier–Laplace extension on `ℝ`. -/
theorem conj_fourierInv_real (g : ℝ → ℝ) (x : ℝ) :
    (starRingEnd ℂ) (𝓕⁻ (fun η => (g η : ℂ)) x) = flExt (fun η => (g η : ℂ)) x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, ← integral_conj, flExt]
  congr 1
  ext η
  rw [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, mul_comm]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- For `ξ ≥ 0`, `∫ e^{2πixξ} Φ(x) G(x) dx = 0`. -/
theorem integral_exp_mul_eq_zero {Φ : ℂ → ℂ} {M : ℝ} (hd : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hc : ContinuousOn Φ {z : ℂ | 0 ≤ z.im}) (hb : ∀ z : ℂ, 0 ≤ z.im → ‖Φ z‖ ≤ M) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (hsupp : tsupport g ⊆ Iic 0) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ∫ x : ℝ, Complex.exp (2 * π * I * x * ξ) * (Φ x * flExt g x) = 0 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (by simp))
  have hG := Cvs.Upstream.FourierLaplaceExtension.differentiable_flExt hg.continuous hs
  refine Cvs.Upstream.UpperHalfPlaneIntegralVanishes.integral_eq_zero_of_decay
    (F := fun z => Complex.exp (2 * π * I * z * ξ) * (Φ z * flExt g z))
    (C := M * ((∫ η : ℝ, ‖g η‖) + (∫ η : ℝ, ‖deriv (deriv g) η‖) / (4 * π ^ 2)))
    ((Continuous.continuousOn (by fun_prop)).mul (hc.mul hG.continuous.continuousOn))
    ((Differentiable.differentiableOn (by fun_prop)).mul (hd.mul hG.differentiableOn)) fun z hz => ?_
  have he : ‖Complex.exp (2 * π * I * z * ξ)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have : (2 * π * I * z * (ξ : ℂ)).re = -(2 * π * z.im * ξ) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, neg_nonpos]
    have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hz) hξ
    linarith
  have hG2 := Cvs.Upstream.FourierLaplaceExtension.norm_flExt_mul_le hg hs hsupp hz
  rw [norm_mul, norm_mul]
  calc ‖Complex.exp (2 * π * I * z * ξ)‖ * (‖Φ z‖ * ‖flExt g z‖) * (1 + ‖z‖ ^ 2)
      ≤ 1 * (M * (‖flExt g z‖ * (1 + ‖z‖ ^ 2))) := by
        rw [← mul_assoc M, mul_assoc]
        gcongr
        exact hb z hz
    _ ≤ M * ((∫ η : ℝ, ‖g η‖) + (∫ η : ℝ, ‖deriv (deriv g) η‖) / (4 * π ^ 2)) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hG2 hM

/-- **`H²` of the upper half-plane is a module over `H^∞`**: `Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule`. -/
theorem hardyModule : Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule := by
  intro Φ M hd hc hb u hu
  have hcr : Continuous fun x : ℝ => Φ x := hc.comp_continuous Complex.continuous_ofReal (fun x => by simp)
  have hbR : ∀ x : ℝ, ‖Φ x‖ ≤ M := fun x => hb x (by simp)
  have hm : MemLp (fun x : ℝ => Φ x) ⊤ (volume : Measure ℝ) :=
    memLp_top_of_bound hcr.aestronglyMeasurable M (Eventually.of_forall hbR)
  set w := mulOp (fun x : ℝ => Φ x) u
  rw [Cvs.Upstream.HardyProjectionReal.mem_specGe_iff]
  have hloc : LocallyIntegrableOn ((𝓕 w : L2C) : ℝ → ℂ) (Iio 0) volume :=
    ((Lp.memLp _).locallyIntegrable one_le_two).locallyIntegrableOn _
  refine isOpen_Iio.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => ?_
  set gc : ℝ → ℂ := fun x => (g x : ℂ)
  have hgc' : HasCompactSupport gc := hgc.comp_left Complex.ofReal_zero
  have hgs' : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg
  have htsupp : tsupport gc ⊆ Iic 0 :=
    (tsupport_comp_subset Complex.ofReal_zero g).trans (hgs.trans Iio_subset_Iic_self)
  set ψ : 𝓢(ℝ, ℂ) := hgc'.toSchwartzMap hgs'
  have hψ : ∀ x, ψ x = gc x := fun x => rfl
  set k : 𝓢(ℝ, ℂ) := 𝓕⁻ ψ
  have hk : ∀ x, (starRingEnd ℂ) (k x) = flExt gc x := fun x => by
    rw [show k x = 𝓕⁻ (ψ : ℝ → ℂ) x from congrFun (SchwartzMap.fourierInv_coe ψ) x]
    exact conj_fourierInv_real g x
  -- the test pairing is an `L²` inner product
  have ha : ∫ ξ, g ξ • ((𝓕 w : L2C) : ℝ → ℂ) ξ = inner ℂ (ψ.toLp 2) (𝓕 w : L2C) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp ψ 2 volume] with ξ h
    rw [h, hψ]
    simp [gc, Complex.real_smul, mul_comm]
  have hb2 : inner ℂ (ψ.toLp 2) (𝓕 w : L2C) = inner ℂ (k.toLp 2) w := by
    have := Lp.inner_fourier_eq (k.toLp 2) w
    rw [SchwartzMap.toLp_fourier_eq, FourierTransform.fourier_fourierInv_eq] at this
    exact this
  -- move `Φ` to the test side
  set m : ℝ → ℂ := fun x => (starRingEnd ℂ) (Φ x) * k x
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (starRingEnd ℂ) (Φ x)) volume :=
    (Complex.continuous_conj.comp hcr).aestronglyMeasurable
  have hmb : ∀ᵐ x : ℝ ∂volume, ‖(starRingEnd ℂ) (Φ x)‖ ≤ M :=
    Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact hbR x
  have hmi : Integrable m := k.integrable.bdd_mul hmeas hmb
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    (k.memLp 2 volume).of_le_mul (c := M) (hmeas.mul k.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        simp only [m, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hbR x) (norm_nonneg _))
  have hc2 : inner ℂ (k.toLp 2) w = inner ℂ (hm2.toLp m) u := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp k 2 volume, Cvs.Upstream.HardyProjectionReal.coeFn_mulOp hm u, hm2.coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, h3]
    simp only [m, RCLike.inner_apply, map_mul, Complex.conj_conj]
    ring
  -- the Fourier transform of `m` vanishes on `[0, ∞)`
  have hFm : ∀ ξ : ℝ, 0 ≤ ξ → 𝓕 m ξ = 0 := by
    intro ξ hξ
    have e : (starRingEnd ℂ) (𝓕 m ξ) = ∫ x : ℝ, Complex.exp (2 * π * I * x * ξ) * (Φ x * flExt gc x) := by
      rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [m, smul_eq_mul, map_mul, Complex.conj_conj, hk]
      rw [← Complex.exp_conj]
      congr 2
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [integral_exp_mul_eq_zero hd hc hb hgs' hgc' htsupp hξ, map_eq_zero] at e
    exact e
  have hd2 : inner ℂ (hm2.toLp m) u = 0 := by
    rw [← Lp.inner_fourier_eq, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Cvs.Upstream.HardyProjectionReal.mem_specGe_iff.1 hu, Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hmi hm2] with ξ h1 h2
    rcases lt_or_ge ξ 0 with hξ | hξ
    · rw [h1 hξ]; simp
    · rw [h2, hFm ξ hξ]; simp
  rw [ha, hb2, hc2, hd2]

end Cvs.Upstream.HardyBoundedMultiplier

end
