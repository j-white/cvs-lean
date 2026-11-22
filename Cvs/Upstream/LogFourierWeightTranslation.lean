import Mathlib
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The logarithmic Fourier weight from translation differences

For `r ≥ 0`, `log⁺ r ≤ ∫₀¹ (1 − cos rt)/t dt + 2` (one integration by parts against `1/s`). With `t = Th` and
`|𝓕(φ(· + h)) − 𝓕φ|² = (2 − 2cos 2πξh)|𝓕φ|²`, Tonelli and Plancherel give, for `φ ∈ L¹ ∩ L²` and `T > 0`,

  `∫ |𝓕φ(ξ)|² log⁺(2π|ξ|/T) dξ ≤ ½ ∫₀^{1/T} ‖φ(· + h) − φ‖₂² dh/h + 2‖φ‖₂²`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped FourierTransform ENNReal

namespace Cvs.Upstream.LogFourierWeightTranslation

/-! ### The scalar weight -/

/-- `1 − cos y ≤ y²/2`. -/
theorem one_sub_cos_le (y : ℝ) : 1 - cos y ≤ y ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := y)
  linarith

/-- The kernel `(1 − cos rt)/t` is nonnegative on `t > 0`. -/
theorem kernel_nonneg (r : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (1 - cos (r * t)) / t :=
  div_nonneg (by linarith [cos_le_one (r * t)]) ht

theorem measurable_kernel (r : ℝ) : Measurable fun t : ℝ => (1 - cos (r * t)) / t :=
  (measurable_const.sub (continuous_cos.measurable.comp (measurable_const.mul measurable_id))).div measurable_id

/-- The kernel is bounded by `r²t/2`. -/
theorem kernel_le (r : ℝ) {t : ℝ} (ht0 : 0 ≤ t) : (1 - cos (r * t)) / t ≤ r ^ 2 * t / 2 := by
  rcases ht0.eq_or_lt with h | h
  · rw [← h, div_zero]; simp
  rw [div_le_iff₀ h]
  calc 1 - cos (r * t) ≤ (r * t) ^ 2 / 2 := one_sub_cos_le _
    _ = r ^ 2 * t / 2 * t := by ring

theorem intervalIntegrable_kernel (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (1 - cos (r * t)) / t) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 ?_
  refine Measure.integrableOn_of_bounded (M := r ^ 2 * b / 2) (by simp) (measurable_kernel r).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg r (ha.trans ht.1))]
  refine (kernel_le r (ha.trans ht.1)).trans ?_
  have : 0 ≤ r ^ 2 := sq_nonneg r
  have := ht.2
  have : r ^ 2 * t ≤ r ^ 2 * b := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg r)
  linarith

/-- `∫₁^r cos s/s ds ≤ 2` for `r ≥ 1`, by parts against `1/s`. -/
theorem integral_cos_div_le {r : ℝ} (hr : 1 ≤ r) : ∫ s in (1 : ℝ)..r, cos s / s ≤ 2 := by
  have hpos : ∀ s ∈ uIcc (1 : ℝ) r, 0 < s := fun s hs => by
    rw [uIcc_of_le hr] at hs; linarith [hs.1]
  have hu : ∀ s ∈ uIcc (1 : ℝ) r, HasDerivAt (fun s : ℝ => s⁻¹) (-(s ^ 2)⁻¹) s := fun s hs =>
    hasDerivAt_inv (hpos s hs).ne'
  have hv : ∀ s ∈ uIcc (1 : ℝ) r, HasDerivAt sin (cos s) s := fun s _ => hasDerivAt_sin s
  have hcont0 : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (uIcc 1 r) :=
    (continuous_pow 2).continuousOn.inv₀ fun s hs => pow_ne_zero 2 (hpos s hs).ne'
  have hcont : ContinuousOn (fun s : ℝ => -(s ^ 2)⁻¹) (uIcc 1 r) := hcont0.neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcont.intervalIntegrable) (continuous_cos.intervalIntegrable 1 r)
  have e : ∫ s in (1 : ℝ)..r, cos s / s = ∫ s in (1 : ℝ)..r, s⁻¹ * cos s :=
    intervalIntegral.integral_congr fun s _ => by rw [div_eq_inv_mul]
  rw [e, hibp]
  have h1 : r⁻¹ * sin r ≤ 1 := by
    have : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
    have hs : sin r ≤ 1 := sin_le_one r
    have hr0 : 0 ≤ r⁻¹ := by positivity
    rcases le_total 0 (sin r) with h | h
    · calc r⁻¹ * sin r ≤ 1 * 1 := mul_le_mul this hs h zero_le_one
        _ = 1 := one_mul 1
    · nlinarith
  have h2 : 0 ≤ (1 : ℝ)⁻¹ * sin 1 := by
    rw [inv_one, one_mul]; exact sin_nonneg_of_nonneg_of_le_pi zero_le_one (by linarith [pi_gt_three])
  have h3 : -∫ s in (1 : ℝ)..r, -(s ^ 2)⁻¹ * sin s ≤ 1 := by
    have hle : ∫ s in (1 : ℝ)..r, -(-(s ^ 2)⁻¹ * sin s) ≤ ∫ s in (1 : ℝ)..r, (s ^ 2)⁻¹ := by
      refine intervalIntegral.integral_mono_on hr ?_ ?_ fun s hs => ?_
      · exact ((hcont.mul continuous_sin.continuousOn).neg).intervalIntegrable
      · exact hcont0.intervalIntegrable
      · have hs0 : 0 < s := by linarith [hs.1]
        have : 0 < (s ^ 2)⁻¹ := by positivity
        have := sin_le_one s
        nlinarith
    have hval : ∫ s in (1 : ℝ)..r, (s ^ 2)⁻¹ = 1 - r⁻¹ := by
      have hd : ∀ s ∈ uIcc (1 : ℝ) r, HasDerivAt (fun s : ℝ => -s⁻¹) ((s ^ 2)⁻¹) s := fun s hs => by
        have := (hasDerivAt_inv (hpos s hs).ne').neg
        rw [neg_neg] at this
        exact this
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont0.intervalIntegrable]
      simp; ring
    rw [intervalIntegral.integral_neg] at hle
    have : 0 ≤ r⁻¹ := by positivity
    linarith
  linarith

/-- **The logarithmic weight**: `log⁺ r ≤ ∫₀¹ (1 − cos rt)/t dt + 2` for every `r ≥ 0`. -/
theorem log_pos_le (r : ℝ) (hr : 0 ≤ r) :
    max (Real.log r) 0 ≤ (∫ t in (0 : ℝ)..1, (1 - cos (r * t)) / t) + 2 := by
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..1, (1 - cos (r * t)) / t :=
    intervalIntegral.integral_nonneg zero_le_one fun t ht => kernel_nonneg r ht.1
  rcases lt_or_ge r 1 with h1 | h1
  · rw [max_eq_right (Real.log_nonpos hr h1.le)]; linarith
  rw [max_eq_left (Real.log_nonneg h1)]
  have hr0 : 0 < r := by linarith
  have hsplit : ∫ t in (0 : ℝ)..1, (1 - cos (r * t)) / t
      = (∫ t in (0 : ℝ)..r⁻¹, (1 - cos (r * t)) / t) + ∫ t in r⁻¹..1, (1 - cos (r * t)) / t :=
    (intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_kernel r le_rfl (by positivity))
      (intervalIntegrable_kernel r (by positivity) (inv_le_one_of_one_le₀ h1))).symm
  have hA : 0 ≤ ∫ t in (0 : ℝ)..r⁻¹, (1 - cos (r * t)) / t :=
    intervalIntegral.integral_nonneg (by positivity) fun t ht => kernel_nonneg r ht.1
  -- substitute `s = rt`
  have hsub : ∫ t in r⁻¹..1, (1 - cos (r * t)) / t = ∫ s in (1 : ℝ)..r, (1 - cos s) / s := by
    have := intervalIntegral.integral_comp_mul_left (fun s : ℝ => (1 - cos s) / s) (a := r⁻¹) (b := 1) hr0.ne'
    rw [mul_inv_cancel₀ hr0.ne', mul_one, smul_eq_mul] at this
    rw [← mul_right_inj' hr0.ne', ← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : 0 < t := by
      rw [uIcc_of_le (inv_le_one_of_one_le₀ h1)] at ht; linarith [ht.1, inv_pos.2 hr0]
    field_simp
  have hpos : ∀ s ∈ uIcc (1 : ℝ) r, 0 < s := fun s hs => by
    rw [uIcc_of_le h1] at hs; linarith [hs.1]
  have hsplit2 : ∫ s in (1 : ℝ)..r, (1 - cos s) / s = Real.log r - ∫ s in (1 : ℝ)..r, cos s / s := by
    have hi1 : IntervalIntegrable (fun s : ℝ => s⁻¹) volume 1 r :=
      intervalIntegral.intervalIntegrable_inv (fun s hs => (hpos s hs).ne') continuousOn_id
    have hi2 : IntervalIntegrable (fun s : ℝ => cos s / s) volume 1 r :=
      (continuous_cos.continuousOn.div continuousOn_id fun s hs => (hpos s hs).ne').intervalIntegrable
    rw [show (fun s : ℝ => (1 - cos s) / s) = fun s => s⁻¹ - cos s / s from funext fun s => by ring,
      intervalIntegral.integral_sub hi1 hi2, integral_inv_of_pos one_pos hr0, div_one]
  have hc := integral_cos_div_le h1
  linarith

/-- **The weight in the frequency variable**: `log⁺(2π|ξ|/T) ≤ ∫₀^{1/T} (1 − cos 2πξh)/h dh + 2` for `T > 0`. -/
theorem log_pos_le_freq {T : ℝ} (hT : 0 < T) (ξ : ℝ) :
    max (Real.log (2 * π * |ξ| / T)) 0 ≤ (∫ h in (0 : ℝ)..1 / T, (1 - cos (2 * π * ξ * h)) / h) + 2 := by
  have h := log_pos_le (2 * π * |ξ| / T) (by positivity)
  have e : ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * |ξ| / T * t)) / t
      = ∫ h in (0 : ℝ)..1 / T, (1 - cos (2 * π * ξ * h)) / h := by
    have := intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => (1 - cos (2 * π * |ξ| / T * t)) / t) (a := 0) (b := 1 / T) hT.ne'
    rw [mul_zero, mul_one_div_cancel hT.ne', smul_eq_mul] at this
    rw [← mul_right_inj' (inv_ne_zero hT.ne'), ← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun h _ => ?_
    have hc : cos (2 * π * |ξ| / T * (T * h)) = cos (2 * π * ξ * h) := by
      rw [show 2 * π * |ξ| / T * (T * h) = |ξ| * (2 * π * h) by field_simp]
      rcases abs_choice ξ with h' | h'
      · rw [h']; ring_nf
      · rw [h', neg_mul, cos_neg]; ring_nf
    rw [hc]
    rcases eq_or_ne h 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [e] at h
  exact h

/-! ### Translation differences on the Fourier side -/

/-- `‖e^{iθ} − 1‖² = 2 − 2cos θ` for the additive character `𝐞`. -/
theorem norm_fourierChar_sub_one_sq (t : ℝ) : ‖((𝐞 t : Circle) : ℂ) - 1‖ ^ 2 = 2 - 2 * cos (2 * π * t) := by
  rw [Real.fourierChar_apply, Complex.sq_norm, Complex.normSq_apply]
  have e : Complex.exp (↑(2 * π * t) * Complex.I) = ↑(cos (2 * π * t)) + ↑(sin (2 * π * t)) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [e]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_im]
  nlinarith [sin_sq_add_cos_sq (2 * π * t)]

/-- The Fourier transform of a translate is the transform times a phase. -/
theorem fourier_comp_add (φ : ℝ → ℂ) (h ξ : ℝ) :
    𝓕 (fun u => φ (u + h)) ξ = ((𝐞 (h * ξ) : Circle) : ℂ) * 𝓕 φ ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  rw [← integral_add_right_eq_self (fun v => ((𝐞 (h * ξ) : Circle) : ℂ) • (𝐞 (-(v * ξ)) • φ v)) h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-- `‖𝓕φ‖²` is integrable for `φ ∈ L¹ ∩ L²`. -/
theorem integrable_norm_sq_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2 volume) :
    Integrable fun ξ => ‖𝓕 φ ξ‖ ^ 2 := by
  have hae := Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hφ hφ2
  have hL := Lp.memLp (𝓕 (hφ2.toLp φ) : Lp ℂ 2 (volume : Measure ℝ))
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 hL
  refine hi.congr ?_
  filter_upwards [hae] with ξ hξ
  rw [hξ]

theorem continuous_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) : Continuous (𝓕 φ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hφ

/-- **The difference identity**: `∫ |𝓕φ(ξ)|²(1 − cos 2πξh) dξ = ½‖φ(· + h) − φ‖₂²` for `φ ∈ L¹ ∩ L²`. -/
theorem integral_fourier_one_sub_cos {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2 volume) (h : ℝ) :
    ∫ ξ, ‖𝓕 φ ξ‖ ^ 2 * (1 - cos (2 * π * ξ * h)) = (1 / 2) * ∫ u, ‖φ (u + h) - φ u‖ ^ 2 := by
  set ψ : ℝ → ℂ := fun u => φ (u + h) - φ u with hψ
  have hφh : Integrable fun u => φ (u + h) := hφ.comp_add_right h
  have hψi : Integrable ψ := hφh.sub hφ
  have hψ2 : MemLp ψ 2 volume :=
    (hφ2.comp_measurePreserving (measurePreserving_add_right volume h)).sub hφ2
  have hF : ∀ ξ, 𝓕 ψ ξ = (((𝐞 (h * ξ) : Circle) : ℂ) - 1) * 𝓕 φ ξ := fun ξ => by
    have e1 : 𝓕 ψ ξ = 𝓕 (fun u => φ (u + h)) ξ - 𝓕 φ ξ := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq, ← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [hψ, smul_sub]
      · exact (Real.fourierIntegral_convergent_iff ξ).2 hφh |>.congr (Eventually.of_forall fun v => by
          simp [mul_comm])
      · exact (Real.fourierIntegral_convergent_iff ξ).2 hφ |>.congr (Eventually.of_forall fun v => by
          simp [mul_comm])
    rw [e1, fourier_comp_add, sub_mul, one_mul]
  have hP := Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier hψi hψ2
  rw [← hP, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [hF, norm_mul, mul_pow, norm_fourierChar_sub_one_sq]
  ring_nf

/-! ### The weighted Fourier integral -/

/-- **The log-weighted Fourier mass from translation differences**: for `φ ∈ L¹ ∩ L²`, `T > 0` and
`‖φ(· + h) − φ‖₂² ≤ D(h)` on `(0, 1/T]` with `D(h)/h` integrable there, `|𝓕φ|²·log⁺(2π|·|/T)` is integrable and
`∫ |𝓕φ(ξ)|² log⁺(2π|ξ|/T) dξ ≤ ½∫₀^{1/T} D(h)/h dh + 2‖φ‖₂²`. -/
theorem integral_fourier_log_le {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2 volume) {T : ℝ} (hT : 0 < T)
    {D : ℝ → ℝ} (hD : ∀ h ∈ Ioc 0 (1 / T), ∫ u, ‖φ (u + h) - φ u‖ ^ 2 ≤ D h)
    (hDi : IntegrableOn (fun h => D h / h) (Ioc 0 (1 / T))) :
    Integrable (fun ξ => ‖𝓕 φ ξ‖ ^ 2 * max (Real.log (2 * π * |ξ| / T)) 0)
      ∧ ∫ ξ, ‖𝓕 φ ξ‖ ^ 2 * max (Real.log (2 * π * |ξ| / T)) 0
          ≤ (1 / 2) * (∫ h in Ioc 0 (1 / T), D h / h) + 2 * ∫ u, ‖φ u‖ ^ 2 := by
  set F : ℝ → ℝ := fun ξ => ‖𝓕 φ ξ‖ ^ 2 with hFdef
  set Lg : ℝ → ℝ := fun ξ => max (Real.log (2 * π * |ξ| / T)) 0 with hLg
  set k : ℝ → ℝ → ℝ := fun ξ h => (1 - cos (2 * π * ξ * h)) / h with hk
  set S := Ioc (0 : ℝ) (1 / T) with hS
  have hT1 : (0 : ℝ) ≤ 1 / T := by positivity
  have hFc : Continuous F := (continuous_fourier hφ).norm.pow 2
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => by positivity
  have hFi : Integrable F := integrable_norm_sq_fourier hφ hφ2
  have hLm : Measurable Lg :=
    (Real.measurable_log.comp ((measurable_const.mul measurable_abs).div_const T)).max measurable_const
  have hk0 : ∀ ξ, ∀ h ∈ S, 0 ≤ k ξ h := fun ξ h hh => kernel_nonneg _ hh.1.le
  have hkm : Measurable (Function.uncurry k) :=
    (measurable_const.sub (continuous_cos.measurable.comp
      ((measurable_const.mul measurable_fst).mul measurable_snd))).div measurable_snd
  have hkI : ∀ ξ, IntegrableOn (k ξ) S := fun ξ =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).1
      (intervalIntegrable_kernel (2 * π * ξ) le_rfl hT1)
  -- the pointwise weight, in `ℝ≥0∞`
  have hw : ∀ ξ, ENNReal.ofReal (F ξ * Lg ξ)
      ≤ ENNReal.ofReal (F ξ) * ((∫⁻ h in S, ENNReal.ofReal (k ξ h)) + 2) := fun ξ => by
    have h1 := log_pos_le_freq hT ξ
    rw [intervalIntegral.integral_of_le hT1] at h1
    rw [ENNReal.ofReal_mul (hF0 ξ), ← ofReal_integral_eq_lintegral_ofReal (hkI ξ)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hk0 ξ)))]
    gcongr
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_add
      (setIntegral_nonneg measurableSet_Ioc (hk0 ξ)) zero_le_two]
    exact ENNReal.ofReal_le_ofReal h1
  -- the per-shift identity
  have hshift : ∀ h ∈ S, ∫⁻ ξ, ENNReal.ofReal (F ξ * k ξ h) ≤ ENNReal.ofReal (D h / h / 2) := fun h hh => by
    have hh0 : 0 < h := hh.1
    have hint : Integrable fun ξ => F ξ * k ξ h := by
      refine (hFi.mul_const (2 / h)).mono'
        (hFc.measurable.mul (hkm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 ξ) (hk0 ξ h hh))]
      refine mul_le_mul_of_nonneg_left ?_ (hF0 ξ)
      rw [hk, div_le_div_iff_of_pos_right hh0]
      linarith [neg_one_le_cos (2 * π * ξ * h)]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ => mul_nonneg (hF0 ξ) (hk0 ξ h hh))]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ ξ, F ξ * k ξ h = (∫ ξ, F ξ * (1 - cos (2 * π * ξ * h))) / h := by
      rw [← integral_div]; congr 1; funext ξ; rw [hk]; ring
    rw [e, integral_fourier_one_sub_cos hφ hφ2 h, div_div, div_le_div_iff₀ hh0 (by positivity)]
    have := hD h hh
    nlinarith
  have hDS0 : ∀ h ∈ S, 0 ≤ D h / h := fun h hh =>
    div_nonneg ((integral_nonneg fun u => by positivity).trans (hD h hh)) hh.1.le
  -- Tonelli
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 * k p.1 p.2) :=
    ENNReal.measurable_ofReal.comp ((hFc.measurable.comp measurable_fst).mul hkm)
  have hchain : ∫⁻ ξ, ENNReal.ofReal (F ξ * Lg ξ)
      ≤ ENNReal.ofReal ((1 / 2) * (∫ h in S, D h / h)) + 2 * ENNReal.ofReal (∫ u, ‖φ u‖ ^ 2) := by
    calc ∫⁻ ξ, ENNReal.ofReal (F ξ * Lg ξ)
        ≤ ∫⁻ ξ, ENNReal.ofReal (F ξ) * ((∫⁻ h in S, ENNReal.ofReal (k ξ h)) + 2) := lintegral_mono hw
      _ = (∫⁻ ξ, ∫⁻ h in S, ENNReal.ofReal (F ξ * k ξ h)) + 2 * ∫⁻ ξ, ENNReal.ofReal (F ξ) := by
          simp only [mul_add]
          rw [lintegral_add_right _ (show Measurable fun ξ => ENNReal.ofReal (F ξ) * 2 from
              (ENNReal.measurable_ofReal.comp hFc.measurable).mul_const 2),
            ← lintegral_const_mul' 2 _ (by simp)]
          congr 1
          · refine lintegral_congr fun ξ => ?_
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine setLIntegral_congr_fun measurableSet_Ioc fun h hh => ?_
            rw [ENNReal.ofReal_mul (hF0 ξ)]
          · simp only [mul_comm]
      _ = (∫⁻ h in S, ∫⁻ ξ, ENNReal.ofReal (F ξ * k ξ h)) + 2 * ∫⁻ ξ, ENNReal.ofReal (F ξ) := by
          rw [lintegral_lintegral_swap (hmeas.aemeasurable)]
      _ ≤ (∫⁻ h in S, ENNReal.ofReal (D h / h / 2)) + 2 * ∫⁻ ξ, ENNReal.ofReal (F ξ) := by
          gcongr 1
          exact setLIntegral_mono' measurableSet_Ioc hshift
      _ = _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hDi.div_const 2)
              ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun h hh => div_nonneg (hDS0 h hh)
                zero_le_two)),
            ← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hF0),
            Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier hφ hφ2, integral_div]
          ring_nf
  have hfin : ∫⁻ ξ, ENNReal.ofReal (F ξ * Lg ξ) < ⊤ :=
    hchain.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top⟩)
  have hFL0 : ∀ ξ, 0 ≤ F ξ * Lg ξ := fun ξ => mul_nonneg (hF0 ξ) (le_max_right _ _)
  have hFLm : AEStronglyMeasurable (fun ξ => F ξ * Lg ξ) volume :=
    (hFc.measurable.mul hLm).aestronglyMeasurable
  have hInt : Integrable (fun ξ => F ξ * Lg ξ) :=
    ⟨hFLm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hFL0)).2 hfin⟩
  refine ⟨hInt, ?_⟩
  have hA : 0 ≤ (1 / 2) * (∫ h in S, D h / h) :=
    mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc hDS0)
  have hB : 0 ≤ ∫ u, ‖φ u‖ ^ 2 := integral_nonneg fun u => by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hFL0) hFLm]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hchain.trans_eq ?_)
  rw [ENNReal.ofReal_add hA (by positivity), ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

end Cvs.Upstream.LogFourierWeightTranslation

end
