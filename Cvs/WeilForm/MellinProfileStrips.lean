import Mathlib
import Cvs.WeilForm.ThetaSpaceParseval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Mellin profiles on vertical strips

`gM G = ∫₀¹ u^{s−1} G(u) du` is holomorphic on `Re s > −1` and `O(1/|s|)` there, by one integration by parts.
A piecewise-`W^{1,1}` test with pieces in `(0, ∞)` has Mellin transform `O(1/|s|)` on every strip.
`Hfun a G v = a^{1−s} (dslope gM 1) Mv` is then holomorphic on `Re s > −1` and `O(|t|⁻³)` on `−½ ≤ Re s ≤ 2`.
-/

namespace Cvs.WeilForm.MellinProfileStrips

open Real Set Filter Topology MeasureTheory Asymptotics
open Complex (I)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)

/-! ### Definitions -/

/-- The Mellin transform of the profile on `(0, 1]`, `g(s) = ∫₀¹ u^{s−1} G(u) du`. -/
noncomputable def gM (G : ℝ → ℝ) : ℂ → ℂ := mellinR ((Ioc (0 : ℝ) 1).indicator G)

/-- The product `H(s) = a^{1−s} · (dslope g 1)(s) · Mv(s)`. -/
noncomputable def Hfun (a : ℝ) (G v : ℝ → ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) ^ (1 - s) * dslope (gM G) 1 s * mellinR v s

/-! ### Mellin transforms of indicators -/

/-- The Mellin integrand of an indicator is the indicator of the Mellin integrand. -/
theorem cpow_smul_indicator (t : Set ℝ) (F : ℝ → ℝ) (s : ℂ) (θ : ℝ) :
    (θ : ℂ) ^ (s - 1) • ((t.indicator F θ : ℝ) : ℂ)
      = t.indicator (fun x => (x : ℂ) ^ (s - 1) * (F x : ℂ)) θ := by
  by_cases h : θ ∈ t <;> simp [h]

/-- The Mellin transform of `1_t F` for measurable `t ⊆ (0, ∞)` is `∫_t θ^{s−1} F(θ) dθ`. -/
theorem mellinR_indicator {t : Set ℝ} (ht : MeasurableSet t) (h0 : t ⊆ Ioi 0) (F : ℝ → ℝ) (s : ℂ) :
    mellinR (t.indicator F) s = ∫ θ in t, (θ : ℂ) ^ (s - 1) * (F θ : ℂ) := by
  unfold mellinR mellin
  simp_rw [cpow_smul_indicator]
  rw [setIntegral_indicator ht, inter_eq_right.mpr h0]

/-- `g(s) = ∫₀¹ u^{s−1} G(u) du`. -/
theorem gM_eq_integral (G : ℝ → ℝ) (s : ℂ) :
    gM G s = ∫ u in (0 : ℝ)..1, (u : ℂ) ^ (s - 1) * (G u : ℂ) := by
  rw [gM, mellinR_indicator measurableSet_Ioc Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le zero_le_one]

/-- `g(1) = ∫₀¹ G = 0`. -/
theorem gM_one {G : ℝ → ℝ} (hGi : ∫ u in (0 : ℝ)..1, G u = 0) : gM G 1 = 0 := by
  rw [gM_eq_integral]
  simp only [sub_self, Complex.cpow_zero, one_mul]
  rw [intervalIntegral.integral_ofReal, hGi, Complex.ofReal_zero]

/-! ### The profile transform `g` -/

/-- A `C¹` profile on `[0, 1]` vanishing at `0` satisfies `|G₁| ≤ M` and `|G(u)| ≤ M u` there. -/
theorem exists_bound_deriv {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hG0 : G 0 = 0) :
    ∃ M, 0 ≤ M ∧ (∀ u ∈ Icc (0 : ℝ) 1, |G₁ u| ≤ M) ∧ ∀ u ∈ Icc (0 : ℝ) 1, |G u| ≤ M * u := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG₁
  refine ⟨max M 0, le_max_right _ _, fun u hu => (hM u hu).trans (le_max_left _ _), fun u hu => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G) (f' := G₁)
    (fun x hx => (hG x hx).hasDerivWithinAt) (fun x hx => (hM x hx).trans (le_max_left M 0))
    (convex_Icc 0 1) (left_mem_Icc.2 zero_le_one) hu
  simpa [hG0, abs_of_nonneg hu.1] using h

/-- **Integration by parts**: `s g(s) = G(1) − ∫₀¹ u^s G₁(u) du` for `Re s > −1`, `s ≠ 0`. -/
theorem gM_ibp {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hG0 : G 0 = 0) {s : ℂ} (hs : -1 < s.re) (hs0 : s ≠ 0) :
    s * gM G s = (G 1 : ℂ) - ∫ u in (0 : ℝ)..1, (u : ℂ) ^ s * (G₁ u : ℂ) := by
  obtain ⟨M, hM0, hM₁, hMG⟩ := exists_bound_deriv hG hG₁ hG0
  have hr : IntervalIntegrable (fun u : ℝ => M * u ^ s.re) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hs).const_mul M
  have hcpow : ∀ (z : ℂ) (u : ℝ), u ∈ Ioc (0 : ℝ) 1 → ContinuousAt (fun x : ℝ => (x : ℂ) ^ z) u :=
    fun z u hu => Complex.continuousAt_ofReal_cpow_const u z (Or.inr hu.1.ne')
  have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (s - 1) * (G u : ℂ)) volume 0 1 := by
    refine hr.mono_fun' ?_ ?_
    · rw [uIoc_of_le zero_le_one]
      refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioc
      exact ((hcpow _ u hu).mul (Complex.continuous_ofReal.continuousAt.comp
        (hG u (Ioc_subset_Icc_self hu)).continuousAt)).continuousWithinAt
    · rw [uIoc_of_le zero_le_one]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real, Real.norm_eq_abs,
        Complex.sub_re, Complex.one_re]
      calc u ^ (s.re - 1) * |G u| ≤ u ^ (s.re - 1) * (M * u) :=
            mul_le_mul_of_nonneg_left (hMG u (Ioc_subset_Icc_self hu)) (Real.rpow_nonneg hu.1.le _)
        _ = M * u ^ s.re := by
            rw [Real.rpow_sub_one hu.1.ne', mul_comm M u, ← mul_assoc, div_mul_cancel₀ _ hu.1.ne',
              mul_comm]
  have hI2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ s * (G₁ u : ℂ)) volume 0 1 := by
    refine hr.mono_fun' ?_ ?_
    · rw [uIoc_of_le zero_le_one]
      refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioc
      exact ((hcpow _ u hu).continuousWithinAt).mul
        ((Complex.continuous_ofReal.comp_continuousOn hG₁).mono Ioc_subset_Icc_self u hu)
    · rw [uIoc_of_le zero_le_one]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real, Real.norm_eq_abs,
        mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM₁ u (Ioc_subset_Icc_self hu)) (Real.rpow_nonneg hu.1.le _)
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ s * (G u : ℂ)) (Icc 0 1) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · subst h
      have hf0 : ((0 : ℝ) : ℂ) ^ s * ((G 0 : ℝ) : ℂ) = 0 := by simp [hG0]
      show Tendsto _ _ (𝓝 (((0 : ℝ) : ℂ) ^ s * ((G 0 : ℝ) : ℂ)))
      rw [hf0]
      refine squeeze_zero_norm' (a := fun u : ℝ => M * u ^ (s.re + 1)) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with x hx
        rcases eq_or_lt_of_le hx.1 with hx0 | hx0
        · subst hx0; rw [hf0, norm_zero]; positivity
        · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
            Real.norm_eq_abs, Real.rpow_add_one hx0.ne']
          calc x ^ s.re * |G x| ≤ x ^ s.re * (M * x) := by gcongr; exact hMG x hx
            _ = M * (x ^ s.re * x) := by ring
      · have hc : ContinuousAt (fun u : ℝ => M * u ^ (s.re + 1)) 0 := continuousAt_const.mul
          (Real.continuousAt_rpow_const 0 (s.re + 1) (Or.inr (by linarith)))
        have h0 : M * (0 : ℝ) ^ (s.re + 1) = 0 := by
          rw [Real.zero_rpow (by linarith), mul_zero]
        simpa [h0] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · exact ((Complex.continuousAt_ofReal_cpow_const u s (Or.inr h.ne')).mul
        (Complex.continuous_ofReal.continuousAt.comp (hG u hu).continuousAt)).continuousWithinAt
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u : ℝ => (u : ℂ) ^ s * (G u : ℂ))
      (s * ((x : ℂ) ^ (s - 1) * (G x : ℂ)) + (x : ℂ) ^ s * (G₁ x : ℂ)) x := fun x hx =>
    ((hasDerivAt_ofReal_cpow_const hx.1.ne' hs0).mul
      (hG x (Ioo_subset_Icc_self hx)).ofReal_comp).congr_deriv (by ring)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    ((hI1.const_mul s).add hI2)
  rw [intervalIntegral.integral_add (hI1.const_mul s) hI2, intervalIntegral.integral_const_mul]
    at key
  have h1 : ((1 : ℝ) : ℂ) ^ s * ((G 1 : ℝ) : ℂ) = G 1 := by simp
  have h0 : ((0 : ℝ) : ℂ) ^ s * ((G 0 : ℝ) : ℂ) = 0 := by simp [hG0]
  simp only [h1, h0, sub_zero] at key
  rw [gM_eq_integral]
  linear_combination key

/-- `‖g(s)‖ ≤ C/‖s‖` on `Re s ≥ −½`. -/
theorem norm_gM_le_div_norm {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hG0 : G 0 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s ≠ 0 → ‖gM G s‖ ≤ C / ‖s‖ := by
  obtain ⟨M, hM0, hM₁, -⟩ := exists_bound_deriv hG hG₁ hG0
  have hr : IntervalIntegrable (fun u : ℝ => M * u ^ (-1 / 2 : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul M
  have hJ : 0 ≤ ∫ u in (0 : ℝ)..1, M * u ^ (-1 / 2 : ℝ) :=
    intervalIntegral.integral_nonneg zero_le_one fun u hu => by
      have := Real.rpow_nonneg hu.1 (-1 / 2 : ℝ); positivity
  refine ⟨|G 1| + ∫ u in (0 : ℝ)..1, M * u ^ (-1 / 2 : ℝ), by positivity, fun s hs hs0 => ?_⟩
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hint : ‖∫ u in (0 : ℝ)..1, (u : ℂ) ^ s * (G₁ u : ℂ)‖
      ≤ ∫ u in (0 : ℝ)..1, M * u ^ (-1 / 2 : ℝ) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall fun u hu => ?_) hr
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real, Real.norm_eq_abs,
      mul_comm M]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2 hs)
      (hM₁ u (Ioc_subset_Icc_self hu)) (abs_nonneg _) (Real.rpow_nonneg hu.1.le _)
  rw [le_div_iff₀ hspos, mul_comm, ← norm_mul, gM_ibp hG hG₁ hG0 (by linarith) hs0]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- **`g` is holomorphic on `Re s > −1`.** -/
theorem differentiableOn_gM {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hG0 : G 0 = 0) :
    DifferentiableOn ℂ (gM G) {s | -1 < s.re} := by
  obtain ⟨M, -, -, hMG⟩ := exists_bound_deriv hG hG₁ hG0
  have hcG : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (mellin fun θ => (((Ioc (0 : ℝ) 1).indicator G θ : ℝ) : ℂ)) s
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := -1) ?_ ?_ (by linarith) ?_ hs
  · refine (Integrable.integrableOn ?_).locallyIntegrableOn
    have e : (fun θ => (((Ioc (0 : ℝ) 1).indicator G θ : ℝ) : ℂ))
        = (Ioc (0 : ℝ) 1).indicator (fun θ => (G θ : ℂ)) := by
      funext θ; by_cases h : θ ∈ Ioc (0 : ℝ) 1 <;> simp [h]
    rw [e]
    exact (integrable_indicator_iff measurableSet_Ioc).2
      ((Complex.continuous_ofReal.comp_continuousOn hcG).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)
  · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with θ hθ
    have : θ ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.2 hθ) h.2
    simp [this]
  · refine IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds one_pos)]
      with θ (hθ : 0 < θ) (hθ1 : θ < 1)
    rw [indicator_of_mem (show θ ∈ Ioc (0 : ℝ) 1 from ⟨hθ, hθ1.le⟩), Complex.norm_real, Real.norm_eq_abs, neg_neg,
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hθ]
    exact hMG θ ⟨hθ.le, hθ1.le⟩

/-- **`‖g(s)‖ ≤ C/|Im s|` on `−½ ≤ Re s ≤ 2`, `|Im s| ≥ 1`.** -/
theorem norm_gM_le {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hG0 : G 0 = 0) :
    ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖gM G s‖ ≤ C / |s.im| := by
  obtain ⟨C, hC0, hC⟩ := norm_gM_le_div_norm hG hG₁ hG0
  refine ⟨C, fun s h1 _ h3 => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; simp at h3; linarith
  exact (hC s h1 hs0).trans (div_le_div_of_nonneg_left hC0 (by linarith) (Complex.abs_im_le_norm s))

/-! ### Piecewise tests -/

/-- On `[p, q] × [σ₁, σ₂]` with `p > 0`, `θ^x` is bounded by the sum of its four corner values. -/
theorem rpow_le_corners {p q θ x σ₁ σ₂ : ℝ} (hp : 0 < p) (hθ : θ ∈ Icc p q) (hx₁ : σ₁ ≤ x)
    (hx₂ : x ≤ σ₂) : θ ^ x ≤ p ^ σ₁ + p ^ σ₂ + q ^ σ₁ + q ^ σ₂ := by
  have hθ0 : 0 < θ := hp.trans_le hθ.1
  have hq : 0 < q := hθ0.trans_le hθ.2
  have hc : ∀ c : ℝ, 0 < c → c ^ x ≤ c ^ σ₁ + c ^ σ₂ := fun c hc => by
    rcases le_or_gt 1 c with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h hx₂
      have := Real.rpow_nonneg hc.le σ₁
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hc h.le hx₁
      have := Real.rpow_nonneg hc.le σ₂
      linarith
  have := hc p hp
  have := hc q hq
  have := Real.rpow_nonneg hp.le σ₁
  have := Real.rpow_nonneg hp.le σ₂
  have := Real.rpow_nonneg hq.le σ₁
  have := Real.rpow_nonneg hq.le σ₂
  rcases le_or_gt 0 x with h | h
  · have := Real.rpow_le_rpow hθ0.le hθ.2 h
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hp hθ.1 h.le
    linarith

/-- The Mellin integrand of a piece `1_{[p,q)} w` with `p > 0` and `w` continuous on `[p, q]` is integrable. -/
theorem integrableOn_mellin_piece {p q : ℝ} {w : ℝ → ℝ} (hp : 0 < p) (hwc : ContinuousOn w (Icc p q))
    (s : ℂ) :
    IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) • (((Ico p q).indicator w θ : ℝ) : ℂ)) (Ioi 0) := by
  simp_rw [cpow_smul_indicator]
  refine Integrable.integrableOn ((integrable_indicator_iff measurableSet_Ico).2 ?_)
  refine ContinuousOn.integrableOn_Icc (fun θ hθ => ?_) |>.mono_set Ico_subset_Icc_self
  exact ((Complex.continuousAt_ofReal_cpow_const θ (s - 1)
    (Or.inr (hp.trans_le hθ.1).ne')).continuousWithinAt).mul
    ((Complex.continuous_ofReal.comp_continuousOn hwc) θ hθ)

/-- **One piece**: `‖M[1_{[p,q)} w](s)‖ ≤ C/‖s‖` on `σ₁ ≤ Re s ≤ σ₂`, for `w` absolutely continuous on `[p, q]`. -/
theorem norm_mellinR_piece_le {p q : ℝ} {w w₁ : ℝ → ℝ} (hp : 0 < p) (hwc : ContinuousOn w (Icc p q))
    (hw : ∀ θ ∈ Ioo p q, HasDerivAt w (w₁ θ) θ) (hw₁ : IntervalIntegrable w₁ volume p q)
    (σ₁ σ₂ : ℝ) :
    ∃ C, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → s ≠ 0 → ‖mellinR ((Ico p q).indicator w) s‖ ≤ C / ‖s‖ := by
  rcases lt_or_ge q p with hqp | hpq
  · refine ⟨0, fun s _ _ _ => ?_⟩
    rw [Ico_eq_empty (not_lt.2 hqp.le), indicator_empty]
    simp [mellinR, mellin]
  set K := p ^ σ₁ + p ^ σ₂ + q ^ σ₁ + q ^ σ₂
  refine ⟨K * (|w q| + |w p| + ∫ θ in p..q, |w₁ θ|), fun s h1 h2 hs0 => ?_⟩
  have hpos : ∀ θ ∈ Icc p q, 0 < θ := fun θ hθ => hp.trans_le hθ.1
  have hK : ∀ θ ∈ Icc p q, ‖(θ : ℂ) ^ s‖ ≤ K := fun θ hθ => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos θ hθ)]
    exact rpow_le_corners hp hθ h1 h2
  have hcpow : ∀ z : ℂ, ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Icc p q) := fun z θ hθ =>
    (Complex.continuousAt_ofReal_cpow_const θ z (Or.inr (hpos θ hθ).ne')).continuousWithinAt
  have hwC : ContinuousOn (fun θ => (w θ : ℂ)) (Icc p q) :=
    Complex.continuous_ofReal.comp_continuousOn hwc
  have hI1 : IntervalIntegrable (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (w θ : ℂ)) volume p q :=
    ((hcpow _).mul hwC).intervalIntegrable_of_Icc hpq
  have hw₁C : IntervalIntegrable (fun θ => (w₁ θ : ℂ)) volume p q :=
    intervalIntegrable_iff.2 (intervalIntegrable_iff.1 hw₁).ofReal
  have hI2 : IntervalIntegrable (fun θ : ℝ => (θ : ℂ) ^ s * (w₁ θ : ℂ)) volume p q :=
    hw₁C.continuousOn_mul (by rw [uIcc_of_le hpq]; exact hcpow s)
  have hcont : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ s * (w θ : ℂ)) (Icc p q) := (hcpow s).mul hwC
  have hderiv : ∀ x ∈ Ioo p q, HasDerivAt (fun θ : ℝ => (θ : ℂ) ^ s * (w θ : ℂ))
      (s * ((x : ℂ) ^ (s - 1) * (w x : ℂ)) + (x : ℂ) ^ s * (w₁ x : ℂ)) x := fun x hx =>
    ((hasDerivAt_ofReal_cpow_const (hpos x (Ioo_subset_Icc_self hx)).ne' hs0).mul
      (hw x hx).ofReal_comp).congr_deriv (by ring)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq hcont hderiv
    ((hI1.const_mul s).add hI2)
  rw [intervalIntegral.integral_add (hI1.const_mul s) hI2, intervalIntegral.integral_const_mul]
    at key
  have hM : mellinR ((Ico p q).indicator w) s = ∫ θ in p..q, (θ : ℂ) ^ (s - 1) * (w θ : ℂ) := by
    rw [mellinR_indicator measurableSet_Ico (fun x hx => hp.trans_le hx.1), integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hpq]
  have hint : ‖∫ θ in p..q, (θ : ℂ) ^ s * (w₁ θ : ℂ)‖ ≤ ∫ θ in p..q, K * |w₁ θ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le hpq
      (Eventually.of_forall fun θ hθ => ?_) (hw₁.abs.const_mul K)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK θ (Ioc_subset_Icc_self hθ)) (abs_nonneg _)
  have hq' : ‖(q : ℂ) ^ s * (w q : ℂ)‖ ≤ K * |w q| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK q (right_mem_Icc.2 hpq)) (abs_nonneg _)
  have hp' : ‖(p : ℂ) ^ s * (w p : ℂ)‖ ≤ K * |w p| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK p (left_mem_Icc.2 hpq)) (abs_nonneg _)
  have hsM : s * mellinR ((Ico p q).indicator w) s
      = (q : ℂ) ^ s * (w q : ℂ) - (p : ℂ) ^ s * (w p : ℂ)
        - ∫ θ in p..q, (θ : ℂ) ^ s * (w₁ θ : ℂ) := by
    rw [hM]; linear_combination key
  rw [intervalIntegral.integral_const_mul] at hint
  rw [le_div_iff₀ (norm_pos_iff.2 hs0), mul_comm, ← norm_mul, hsM]
  calc _ ≤ ‖(q : ℂ) ^ s * (w q : ℂ)‖ + ‖(p : ℂ) ^ s * (w p : ℂ)‖
        + ‖∫ θ in p..q, (θ : ℂ) ^ s * (w₁ θ : ℂ)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ K * |w q| + K * |w p| + K * ∫ θ in p..q, |w₁ θ| := by gcongr
    _ = _ := by ring

/-- **Piecewise tests**: a finite sum of pieces `1_{[p_j,q_j)} w_j` with `p_j > 0` and each `w_j`
absolutely continuous on `[p_j, q_j]` has `‖Mv(s)‖ ≤ C/‖s‖` on every vertical strip. -/
theorem norm_mellinR_le_of_pieces {ι : Type*} (J : Finset ι) (p q : ι → ℝ) (w w₁ : ι → ℝ → ℝ)
    (hp : ∀ j ∈ J, 0 < p j) (hwc : ∀ j ∈ J, ContinuousOn (w j) (Icc (p j) (q j)))
    (hw : ∀ j ∈ J, ∀ θ ∈ Ioo (p j) (q j), HasDerivAt (w j) (w₁ j θ) θ)
    (hw₁ : ∀ j ∈ J, IntervalIntegrable (w₁ j) volume (p j) (q j)) {v : ℝ → ℝ}
    (hv : v = fun θ => ∑ j ∈ J, (Ico (p j) (q j)).indicator (w j) θ) (σ₁ σ₂ : ℝ) :
    ∃ C, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → s ≠ 0 → ‖mellinR v s‖ ≤ C / ‖s‖ := by
  have h := fun j (hj : j ∈ J) =>
    norm_mellinR_piece_le (hp j hj) (hwc j hj) (hw j hj) (hw₁ j hj) σ₁ σ₂
  choose! C hC using h
  refine ⟨∑ j ∈ J, C j, fun s h1 h2 hs0 => ?_⟩
  have hsum : mellinR v s = ∑ j ∈ J, mellinR ((Ico (p j) (q j)).indicator (w j)) s := by
    subst hv
    unfold mellinR mellin
    rw [← integral_finsetSum J fun j hj => integrableOn_mellin_piece (hp j hj) (hwc j hj) s]
    congr 1; funext θ
    push_cast
    rw [Finset.smul_sum]
  rw [hsum, Finset.sum_div]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hC j hj s h1 h2 hs0)

/-- A bounded measurable `v` supported in `[α, β]` with `α > 0` has an entire Mellin transform. -/
theorem differentiable_mellinR_of_support {v : ℝ → ℝ} {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v) (hvb : ∃ M, ∀ θ, |v θ| ≤ M) :
    Differentiable ℂ (mellinR v) := by
  obtain ⟨M, hM⟩ := hvb
  have hint : Integrable v := by
    have h : IntegrableOn v (Icc α β) :=
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne hvm.aestronglyMeasurable
        (Eventually.of_forall fun θ => (Real.norm_eq_abs _).trans_le (hM θ))
    exact (integrableOn_iff_integrable_of_support_subset fun θ hθ => by
      by_contra h'; exact hθ (hsupp θ h')).1 h
  intro s
  show DifferentiableAt ℂ (mellin fun θ => (v θ : ℂ)) s
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    hint.ofReal.integrableOn.locallyIntegrableOn ?_ (by linarith) ?_ (by linarith)
  · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop β] with θ hθ
    simp [hsupp θ fun h => not_le.2 hθ h.2]
  · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hα)] with θ (hθ : θ < α)
    simp [hsupp θ fun h => not_le.2 hθ h.1]

/-! ### The product `H` -/

/-- **`H` is holomorphic on `Re s > −1`.** -/
theorem differentiableOn_Hfun {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M) :
    DifferentiableOn ℂ (Hfun a G v) {s | -1 < s.re} := by
  have hopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {s : ℂ | -1 < s.re} := by show (-1 : ℝ) < (1 : ℂ).re; norm_num
  have hd : DifferentiableOn ℂ (dslope (gM G) 1) {s | -1 < s.re} :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds h1)).2 (differentiableOn_gM hG hG₁ hG0)
  have hv := differentiable_mellinR_of_support hα hsupp hvm hvb
  intro s hs
  have hA : DifferentiableAt ℂ (fun s : ℂ => (a : ℂ) ^ (1 - s)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow
      (Or.inl (by exact_mod_cast ha.ne'))
  exact (hA.differentiableWithinAt.mul (hd s hs)).mul (hv s).differentiableWithinAt

/-- **`‖H(s)‖ ≤ C (1 + |Im s|)^{−3}` on `−½ ≤ Re s ≤ 2`, `|Im s| ≥ 1`.** -/
theorem norm_Hfun_le {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖Hfun a G v s‖ ≤ C * (1 + |s.im|) ^ (-3 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := norm_gM_le hG hG₁ hG0
  obtain ⟨C₂, hC₂⟩ := hvdec
  set A := a ^ (3 / 2 : ℝ) + a ^ (-1 : ℝ)
  have hA0 : 0 ≤ A := by positivity
  refine ⟨8 * (A * |C₁| * |C₂|), fun s h1 h2 h3 => ?_⟩
  set t := |s.im| with ht_def
  have ht : 0 < t := by linarith
  have hA : ‖(a : ℂ) ^ (1 - s)‖ ≤ A := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.sub_re, Complex.one_re]
    have := Real.rpow_nonneg ha.le (3 / 2 : ℝ)
    have := Real.rpow_nonneg ha.le (-1 : ℝ)
    rcases le_or_gt 1 a with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show 1 - s.re ≤ 3 / 2 by linarith)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge ha h.le (show -1 ≤ 1 - s.re by linarith)
      linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp [ht_def] at h3; linarith
  have hn : t ≤ ‖s - 1‖ := by simpa [ht_def] using Complex.abs_im_le_norm (s - 1)
  have hg : ‖gM G s‖ ≤ |C₁| / t :=
    (hC₁ s h1 h2 h3).trans (div_le_div_of_nonneg_right (le_abs_self _) ht.le)
  have hD : ‖dslope (gM G) 1 s‖ ≤ |C₁| / t / t := by
    rw [dslope_of_ne _ hs1, slope_def_module, gM_one hGi, sub_zero, norm_smul, norm_inv,
      inv_mul_eq_div]
    calc ‖gM G s‖ / ‖s - 1‖ ≤ (|C₁| / t) / ‖s - 1‖ :=
          div_le_div_of_nonneg_right hg (norm_nonneg _)
      _ ≤ |C₁| / t / t := div_le_div_of_nonneg_left (by positivity) ht hn
  have hV : ‖mellinR v s‖ ≤ |C₂| / t :=
    (hC₂ s h1 h2 h3).trans (div_le_div_of_nonneg_right (le_abs_self _) ht.le)
  have h8 : (1 + t) ^ 3 ≤ 8 * t ^ 3 := by
    have : 1 + t ≤ 2 * t := by linarith
    calc (1 + t) ^ 3 ≤ (2 * t) ^ 3 := by gcongr
      _ = 8 * t ^ 3 := by ring
  have hrp : (1 + t) ^ (-3 : ℝ) = ((1 + t) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]; norm_cast
  have hkey : A * (|C₁| / t / t) * (|C₂| / t) ≤ 8 * (A * |C₁| * |C₂|) * (1 + t) ^ (-3 : ℝ) := by
    rw [hrp]
    have hK : 0 ≤ A * |C₁| * |C₂| := by positivity
    have e : A * (|C₁| / t / t) * (|C₂| / t) = A * |C₁| * |C₂| / t ^ 3 := by
      field_simp
    rw [e, div_eq_mul_inv, mul_assoc 8, mul_left_comm, ← div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hK
    have h1t : 0 < (1 + t) ^ 3 := by positivity
    have ht3 : 0 < t ^ 3 := by positivity
    calc (t ^ 3)⁻¹ = 1 / t ^ 3 := (one_div _).symm
      _ ≤ 8 / (1 + t) ^ 3 := by rw [div_le_div_iff₀ ht3 h1t]; linarith
      _ = 8 * ((1 + t) ^ 3)⁻¹ := div_eq_mul_inv _ _
  calc ‖Hfun a G v s‖ = ‖(a : ℂ) ^ (1 - s)‖ * ‖dslope (gM G) 1 s‖ * ‖mellinR v s‖ := by
        simp only [Hfun, norm_mul]
    _ ≤ A * (|C₁| / t / t) * (|C₂| / t) := by gcongr
    _ ≤ _ := hkey

/-- `H(1) = g′(1) · Mv(1)`. -/
theorem Hfun_one (a : ℝ) (G v : ℝ → ℝ) : Hfun a G v 1 = deriv (gM G) 1 * mellinR v 1 := by
  simp [Hfun, dslope_same]

/-- `H(0) = −a · g(0) · Mv(0)`, since `g(1) = 0`. -/
theorem Hfun_zero (a : ℝ) {G : ℝ → ℝ} (v : ℝ → ℝ) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    Hfun a G v 0 = -((a : ℂ) * gM G 0 * mellinR v 0) := by
  rw [Hfun, dslope_of_ne _ zero_ne_one, slope_def_module, gM_one hGi]
  simp

end Cvs.WeilForm.MellinProfileStrips
