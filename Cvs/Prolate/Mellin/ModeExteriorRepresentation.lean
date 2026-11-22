import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.TrigMellinIntegralsContinuation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior representation of the per-mode Mellin transform

For `ψ = ψ_g` the cosine transform of an even `g` on `[−1, 1]` (band `[−c, c]`) and `k ≥ 1`, `Re s < 0`, the function
`t ↦ C(kct, s)` has spectrum in `|ω| ≥ kc`, so Plancherel gives `∫_ℝ ψ(t)C(kct, s) dt = 0`. With `G = ψ` on `[−1, 1]`
and Fubini, `∫₁^∞ θ^{s−1}ψ_G(kθ) dθ = ∫_{−1}^{1} G(t)C(kct, s) dt = −2∫₁^∞ ψ(t)C(kct, s) dt`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Complex
open scoped FourierTransform ComplexConjugate
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Upstream.TrigMellinIntegralsContinuation (cosM sinM)

namespace Cvs.Prolate.Mellin.ModeExteriorRepresentation
open Cvs.ZeroCounting

/-! ### Plancherel for the inner product -/

/-- **Plancherel's identity on `L¹ ∩ L²`**: `∫ conj(𝓕f)·𝓕g = ∫ conj(f)·g`. -/
theorem integral_conj_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2 volume) (hg : Integrable g)
    (hg2 : MemLp g 2 volume) : ∫ w, conj (𝓕 f w) * 𝓕 g w = ∫ v, conj (f v) * g v := by
  have hA := Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hf hf2
  have hB := Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hg hg2
  have h := Lp.inner_fourier_eq (hf2.toLp f) (hg2.toLp g)
  rw [L2.inner_def, L2.inner_def] at h
  calc ∫ w, conj (𝓕 f w) * 𝓕 g w
      = ∫ w, inner ℂ (((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w)
          (((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w) := by
        refine integral_congr_ae ?_
        filter_upwards [hA, hB] with w h1 h2
        rw [h1, h2, RCLike.inner_apply']
    _ = ∫ v, inner ℂ (((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) v)
          (((hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) v) := h
    _ = ∫ v, conj (f v) * g v := by
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with v h1 h2
        rw [h1, h2, RCLike.inner_apply']

/-! ### The tail function and its transform -/

/-- `B_{k,s}(v) = 1_{v>k} k⁻¹(v/k)^{s−1}`. -/
def tailB (k : ℝ) (s : ℂ) (v : ℝ) : ℂ := (Ioi k).indicator (fun v => (1 / k : ℂ) * ((v / k : ℝ) : ℂ) ^ (s - 1)) v

theorem norm_tailB {k : ℝ} (hk : 0 < k) (s : ℂ) (v : ℝ) :
    ‖tailB k s v‖ = (Ioi k).indicator (fun v => (1 / k) * (v / k) ^ (s.re - 1)) v := by
  unfold tailB
  by_cases hv : v ∈ Ioi k
  · rw [indicator_of_mem hv, indicator_of_mem hv, norm_mul,
      Cvs.Upstream.TrigMellinIntegralsContinuation.norm_cpow_sub_one (div_pos (hk.trans hv) hk) s]
    congr 1
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, one_div]
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, norm_zero]

theorem measurable_tailB (k : ℝ) (s : ℂ) : Measurable (tailB k s) := by
  unfold tailB
  refine Measurable.indicator ?_ measurableSet_Ioi
  refine measurable_const.mul ?_
  exact (Complex.continuous_ofReal.measurable.comp (measurable_id.div_const k)).pow_const _

theorem integrable_tailB {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : s.re < 0) : Integrable (tailB k s) := by
  refine Integrable.mono' (g := (Ioi k).indicator (fun v => (1 / k) * (v / k) ^ (s.re - 1))) ?_
    (measurable_tailB k s).aestronglyMeasurable (Eventually.of_forall fun v => (norm_tailB hk s v).le)
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h := (integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 1 < -1) hk).const_mul (1 / k / k ^ (s.re - 1))
  refine IntegrableOn.congr_fun h (fun v hv => ?_) measurableSet_Ioi
  have hv0 : 0 < v := hk.trans hv
  have hkr : 0 < k ^ (s.re - 1) := Real.rpow_pos_of_pos hk _
  rw [Real.div_rpow hv0.le hk.le]
  field_simp

theorem memLp_tailB {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : s.re < 0) : MemLp (tailB k s) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (measurable_tailB k s).aestronglyMeasurable).2 ?_
  simp only [norm_tailB hk s]
  refine Integrable.congr (f := (Ioi k).indicator (fun v => ((1 / k) * (v / k) ^ (s.re - 1)) ^ 2)) ?_
    (Eventually.of_forall fun v => ?_)
  · rw [integrable_indicator_iff measurableSet_Ioi]
    have h := (integrableOn_Ioi_rpow_of_lt (by linarith : 2 * (s.re - 1) < -1) hk).const_mul
      ((1 / k) ^ 2 / (k ^ (s.re - 1)) ^ 2)
    refine IntegrableOn.congr_fun h (fun v hv => ?_) measurableSet_Ioi
    have hv0 : 0 < v := hk.trans hv
    have hkr : 0 < k ^ (s.re - 1) := Real.rpow_pos_of_pos hk _
    have hsq : v ^ (2 * (s.re - 1)) = (v ^ (s.re - 1)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le]; ring_nf
    rw [Real.div_rpow hv0.le hk.le, hsq]
    field_simp
  · by_cases hv : v ∈ Ioi k <;> simp [hv]

/-- **The transform of the tail function**: `𝓕B(w) = ∫₁^∞ θ^{s−1} e^{−2πikθw} dθ`. -/
theorem fourier_tailB {k : ℝ} (hk : 0 < k) (s : ℂ) (w : ℝ) :
    𝓕 (tailB k s) w = ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * cexp (↑(-2 * π * (k * θ) * w) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold tailB
  have e : ∀ v : ℝ, cexp (↑(-2 * π * v * w) * I) • (Ioi k).indicator
      (fun v => (1 / k : ℂ) * ((v / k : ℝ) : ℂ) ^ (s - 1)) v
      = (Ioi k).indicator (fun v => (1 / k : ℂ) * (((v / k : ℝ) : ℂ) ^ (s - 1) * cexp (↑(-2 * π * v * w) * I))) v :=
    fun v => by
      by_cases hv : v ∈ Ioi k
      · rw [indicator_of_mem hv, indicator_of_mem hv, smul_eq_mul]; ring
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
  simp only [e]
  rw [integral_indicator measurableSet_Ioi]
  have h := integral_comp_mul_left_Ioi
    (fun v : ℝ => (1 / k : ℂ) * (((v / k : ℝ) : ℂ) ^ (s - 1) * cexp (↑(-2 * π * v * w) * I))) 1 hk
  rw [mul_one] at h
  have hX : ∫ v in Ioi k, (1 / k : ℂ) * (((v / k : ℝ) : ℂ) ^ (s - 1) * cexp (↑(-2 * π * v * w) * I))
      = (k : ℂ) * ∫ θ in Ioi (1 : ℝ), (1 / k : ℂ) * ((((k * θ) / k : ℝ) : ℂ) ^ (s - 1)
          * cexp (↑(-2 * π * (k * θ) * w) * I)) := by
    rw [h, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ (by simpa using hk.ne'), one_mul]
  rw [hX, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  rw [show k * θ / k = θ by field_simp]
  have hk0 : (k : ℂ) ≠ 0 := by simpa using hk.ne'
  field_simp

/-- The symmetric part of the tail transform is the cosine integral: `(𝓕B(w) + 𝓕B(−w))/2 = C(2πkw, s)`. -/
theorem fourier_tailB_add_neg {k : ℝ} (hk : 0 < k) {s : ℂ} (hs : s.re < 0) (w : ℝ) :
    (𝓕 (tailB k s) w + 𝓕 (tailB k s) (-w)) / 2 = cosM (2 * π * k * w) s := by
  rw [fourier_tailB hk, fourier_tailB hk, ← integral_add, ← integral_div]
  · unfold cosM
    refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
    rw [Complex.ofReal_cos]
    rw [Complex.cos]
    push_cast
    ring_nf
  · exact Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_cpow_mul hs (by fun_prop) fun θ => by
      rw [Complex.norm_exp_ofReal_mul_I]
  · exact Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_cpow_mul hs (by fun_prop) fun θ => by
      rw [Complex.norm_exp_ofReal_mul_I]

/-- The transform of `1_{[−1,1]}g` for even `g` is the extension `ψ_g` at `2πw/c`. -/
theorem fourier_winLift_eq_psi {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1))
    (heven : ∀ v ∈ Icc (-1 : ℝ) 1, g (-v) = g v) (w : ℝ) :
    𝓕 (Cvs.Prolate.RungSpanBernsteinNikolskii.winLift g) w = ((psi c g (2 * π * w / c) : ℝ) : ℂ) := by
  rw [Cvs.Prolate.RungSpanBernsteinNikolskii.fourier_winLift hg]
  have hsin : ∫ t in (-1 : ℝ)..1, g t * Real.sin (2 * π * w * t) = 0 := by
    have h1 := intervalIntegral.integral_comp_neg (a := -1) (b := 1)
      (fun t => g t * Real.sin (2 * π * w * t))
    simp only [neg_neg] at h1
    have h2 : ∫ t in (-1 : ℝ)..1, g (-t) * Real.sin (2 * π * w * -t)
        = -∫ t in (-1 : ℝ)..1, g t * Real.sin (2 * π * w * t) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      rw [heven t ht, show 2 * π * w * -t = -(2 * π * w * t) by ring, Real.sin_neg]; ring
    linarith
  rw [hsin, Complex.ofReal_zero, zero_mul, sub_zero]
  refine congrArg (fun x : ℝ => (x : ℂ)) ?_
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only
  refine congrArg (g t * ·) (congrArg Real.cos ?_)
  field_simp

/-! ### The band-limited extension against the cosine integral -/

/-- **Disjoint spectra**: for `ψ_g` with `g` even and continuous on `[−1, 1]`, `k ≥ 1` and `Re s < 0`,
`∫_ℝ ψ_g(t) C(kct, s) dt = 0`. -/
theorem integral_psi_mul_cosM {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1))
    (heven : ∀ v ∈ Icc (-1 : ℝ) 1, g (-v) = g v) {k : ℝ} (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 0) :
    ∫ t, ((psi c g t : ℝ) : ℂ) * cosM (k * c * t) s = 0 := by
  have hk0 : 0 < k := by linarith
  set A := Cvs.Prolate.RungSpanBernsteinNikolskii.winLift g with hAdef
  set B := tailB k s with hBdef
  have hA := Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_winLift hg
  have hA2 := Cvs.Prolate.RungSpanBernsteinNikolskii.memLp_winLift hg
  have hB := integrable_tailB hk0 hs
  have hB2 := memLp_tailB hk0 hs
  -- `A·B = 0` pointwise
  have hAB : ∫ v, conj (A v) * B v = 0 := by
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) (Eventually.of_forall fun v => ?_)).trans
      (integral_zero ℝ ℂ)
    by_cases hv : v ∈ Icc (-1 : ℝ) 1
    · have : v ∉ Ioi k := fun h => by linarith [hv.2, (show k < v from h)]
      show conj (A v) * B v = 0
      rw [hBdef, tailB, indicator_of_notMem this, mul_zero]
    · show conj (A v) * B v = 0
      rw [hAdef, Cvs.Prolate.RungSpanBernsteinNikolskii.winLift, indicator_of_notMem hv, map_zero, zero_mul]
  have hP := integral_conj_fourier_mul hA hA2 hB hB2
  rw [hAB] at hP
  have hFA : ∀ w, 𝓕 A w = ((psi c g (2 * π * w / c) : ℝ) : ℂ) := fun w => fourier_winLift_eq_psi hc hg heven w
  have hreal : ∀ w, conj (𝓕 A w) = 𝓕 A w := fun w => by rw [hFA, Complex.conj_ofReal]
  have hP' : ∫ w, 𝓕 A w * 𝓕 B w = 0 := by
    rw [← hP]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show 𝓕 A w * 𝓕 B w = conj (𝓕 A w) * 𝓕 B w
    rw [hreal]
  -- integrability of `h = 𝓕A·𝓕B`
  have hFA2 : MemLp (𝓕 A) 2 volume :=
    (Lp.memLp _).ae_eq (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hA hA2)
  have hFB2 : MemLp (𝓕 B) 2 volume :=
    (Lp.memLp _).ae_eq (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hB hB2)
  have hh : Integrable (fun w => 𝓕 A w * 𝓕 B w) := hFA2.integrable_mul hFB2
  have hhn : Integrable (fun w => 𝓕 A w * 𝓕 B (-w)) := by
    have := hh.comp_neg
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only [hFA]
    rw [show 2 * π * -w / c = -(2 * π * w / c) by ring, Cvs.Prolate.RungSpanBernsteinNikolskii.psi_neg]
  have hneg : ∫ w, 𝓕 A w * 𝓕 B (-w) = ∫ w, 𝓕 A w * 𝓕 B w := by
    rw [← integral_neg_eq_self (fun w => 𝓕 A w * 𝓕 B w) volume]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hFA]
    rw [show 2 * π * -w / c = -(2 * π * w / c) by ring, Cvs.Prolate.RungSpanBernsteinNikolskii.psi_neg]
  -- the cosine part in the frequency variable
  have hw : ∫ w, 𝓕 A w * cosM (2 * π * k * w) s = 0 := by
    have e : ∀ w, 𝓕 A w * cosM (2 * π * k * w) s = (𝓕 A w * 𝓕 B w + 𝓕 A w * 𝓕 B (-w)) / 2 := fun w => by
      rw [← fourier_tailB_add_neg hk0 hs w]; ring
    simp only [e]
    rw [integral_div, integral_add hh hhn, hneg, hP']; simp
  -- back to `t = 2πw/c`
  have hcv := Measure.integral_comp_mul_left (fun t => ((psi c g t : ℝ) : ℂ) * cosM (k * c * t) s) (2 * π / c)
  have e2 : ∀ w : ℝ, ((psi c g (2 * π / c * w) : ℝ) : ℂ) * cosM (k * c * (2 * π / c * w)) s
      = 𝓕 A w * cosM (2 * π * k * w) s := fun w => by
    rw [hFA, show k * c * (2 * π / c * w) = 2 * π * k * w by field_simp,
      show 2 * π / c * w = 2 * π * w / c by ring]
  simp only [e2, hw] at hcv
  have hne : |(2 * π / c)⁻¹| ≠ 0 := by
    have : (0 : ℝ) < 2 * π / c := by positivity
    exact abs_ne_zero.2 (inv_ne_zero this.ne')
  rw [eq_comm, smul_eq_zero] at hcv
  rcases hcv with h | h
  · exact absurd (by exact_mod_cast h) hne
  · exact h

/-! ### The exterior representation -/

/-- `‖C(yt, s)‖ ≤ 2(1/(−Re s) + (1 + ‖s − 1‖/(1 − Re s))/y)/(1 + |t|)` for `y > 0`, `Re s < 0`. -/
theorem norm_cosM_le_one_add {s : ℂ} (hs : s.re < 0) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖cosM (y * t) s‖ ≤ 2 * (1 / (-s.re) + (1 + ‖s - 1‖ / (1 - s.re)) / y) / (1 + |t|) := by
  set A := 1 / (-s.re) with hA
  set B := (1 + ‖s - 1‖ / (1 - s.re)) / y with hB
  have hA0 : 0 < A := by rw [hA]; exact one_div_pos.2 (by linarith)
  have hB0 : 0 < B := by
    rw [hB]; have : 0 < 1 - s.re := by linarith
    positivity
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt |t| 1 with ht | ht
  · have h1 := Cvs.Upstream.TrigMellinIntegralsContinuation.norm_cosM_le hs (y * t)
    nlinarith [norm_nonneg (cosM (y * t) s), abs_nonneg t]
  · have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
    have h2 := Cvs.Upstream.TrigMellinIntegralsContinuation.norm_cosM_le_div hs (mul_ne_zero hy.ne' ht0)
    rw [abs_mul, abs_of_pos hy] at h2
    have h3 : ‖cosM (y * t) s‖ * |t| ≤ B := by
      have ht1 : 0 < |t| := by linarith
      rw [le_div_iff₀ (by positivity)] at h2
      rw [hB, le_div_iff₀ hy]; nlinarith
    nlinarith [norm_nonneg (cosM (y * t) s)]

/-- **The exterior representation**: for `ψ = ψ_g` (`g` even and continuous on `[−1, 1]`), `G = ψ` on `[−1, 1]`,
`k ≥ 1` and `Re s < 0`, `∫₁^∞ θ^{s−1}ψ_G(kθ) dθ = −2∫₁^∞ ψ(t)C(kct, s) dt`. -/
theorem integral_cpow_psi_eq {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1))
    (heven : ∀ v ∈ Icc (-1 : ℝ) 1, g (-v) = g v) {G : ℝ → ℝ} (hG : ∀ t ∈ Icc (-1 : ℝ) 1, G t = psi c g t)
    {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 0) :
    ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * ((psi c G (k * θ) : ℝ) : ℂ)
      = -2 * ∫ t in Ioi (1 : ℝ), ((psi c g t : ℝ) : ℂ) * cosM (k * c * t) s := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkc : 0 < (k : ℝ) * c := by positivity
  set ψ := psi c g with hψ
  have hψc : Continuous ψ := Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi hg
  set Ψ : ℝ → ℂ := fun t => ((ψ t : ℝ) : ℂ) * cosM (k * c * t) s with hΨ
  -- `Ψ` is integrable on `ℝ`
  have hΨi : Integrable Ψ := by
    set C := 2 * (1 / (-s.re) + (1 + ‖s - 1‖ / (1 - s.re)) / (k * c)) with hC
    have hsq := Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hg
    have hdom : Integrable fun t : ℝ => ψ t ^ 2 / 2 + C ^ 2 * (1 + t ^ 2)⁻¹ :=
      (hsq.div_const 2).add (integrable_inv_one_add_sq.const_mul _)
    refine hdom.mono' ((Complex.continuous_ofReal.comp hψc).mul
      ((Cvs.Upstream.TrigMellinIntegralsContinuation.continuous_cosM hs).comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hb := norm_cosM_le_one_add hs hkc t
    rw [← hC] at hb
    simp only [hΨ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hC0 : 0 ≤ C := by
      rw [hC]; have : 0 < 1 - s.re := by linarith
      have : 0 < -s.re := by linarith
      positivity
    have h1 : ‖cosM (k * c * t) s‖ * (1 + |t|) ≤ C := by rwa [le_div_iff₀ (by positivity)] at hb
    have h2 : (1 + |t|) ^ 2 ≥ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have h3 : ‖cosM (k * c * t) s‖ ^ 2 ≤ C ^ 2 * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have := mul_le_mul h1 h1 (by positivity) hC0
      nlinarith [norm_nonneg (cosM (k * c * t) s), sq_nonneg (‖cosM (k * c * t) s‖)]
    nlinarith [sq_nonneg (|ψ t| - ‖cosM (k * c * t) s‖), sq_abs (ψ t), abs_nonneg (ψ t)]
  -- the full-line integral vanishes; split it
  have h0 : ∫ t, Ψ t = 0 := integral_psi_mul_cosM hc hg heven hk1 hs
  have hΨeven : ∀ t, Ψ (-t) = Ψ t := fun t => by
    simp only [hΨ]
    rw [hψ, Cvs.Prolate.RungSpanBernsteinNikolskii.psi_neg, show (k : ℝ) * c * -t = -(k * c * t) by ring, Cvs.Upstream.TrigMellinIntegralsContinuation.cosM_neg]
  have hsplit1 := intervalIntegral.integral_Iic_add_Ioi (b := -1) hΨi.integrableOn hΨi.integrableOn
  have hsplit2 : ∫ t in Ioi (-1 : ℝ), Ψ t = (∫ t in Ioc (-1 : ℝ) 1, Ψ t) + ∫ t in Ioi (1 : ℝ), Ψ t := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (-1 : ℝ) ≤ 1)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hΨi.integrableOn hΨi.integrableOn
  have hrefl : ∫ t in Iic (-1 : ℝ), Ψ t = ∫ t in Ioi (1 : ℝ), Ψ t := by
    rw [← integral_comp_neg_Ioi 1 Ψ]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hΨeven t
  have hmid : ∫ t in Ioc (-1 : ℝ) 1, Ψ t = -2 * ∫ t in Ioi (1 : ℝ), Ψ t := by
    rw [hsplit2, hrefl, h0] at hsplit1
    linear_combination hsplit1
  -- Fubini on the left side
  have hcongr : ∀ θ : ℝ, psi c G (k * θ) = psi c ψ (k * θ) := fun θ => by
    unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    simp only
    rw [hG t ht]
  have hF : ∀ θ : ℝ, ((psi c ψ (k * θ) : ℝ) : ℂ)
      = ∫ t in Ioc (-1 : ℝ) 1, ((ψ t * Real.cos (k * c * t * θ) : ℝ) : ℂ) := fun θ => by
    unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
    rw [intervalIntegral.integral_of_le (by norm_num), integral_complex_ofReal]
    refine congrArg (fun x : ℝ => (x : ℂ)) ?_
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only
    exact congrArg (ψ t * ·) (congrArg Real.cos (by ring))
  simp only [hcongr, hF]
  rw [← hmid]
  have hint : Integrable
      (Function.uncurry fun (θ t : ℝ) => (θ : ℂ) ^ (s - 1) * ((ψ t * Real.cos (k * c * t * θ) : ℝ) : ℂ))
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := ψ) (s := Icc (-1 : ℝ) 1)
      hψc.continuousOn
    have hdom : Integrable (fun p : ℝ × ℝ => p.1 ^ (s.re - 1) * M)
        ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
      have h1 := (Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_rpow_re hs).mul_prod (μ := volume.restrict (Ioi (1 : ℝ)))
        (ν := volume.restrict (Ioc (-1 : ℝ) 1)) (g := fun _ : ℝ => M)
        (integrable_const (μ := volume.restrict (Ioc (-1 : ℝ) 1)) M)
      exact h1
    rw [Measure.prod_restrict]
    rw [Measure.prod_restrict] at hdom
    have hcont : ContinuousOn (Function.uncurry fun (θ t : ℝ) =>
        (θ : ℂ) ^ (s - 1) * ((ψ t * Real.cos (k * c * t * θ) : ℝ) : ℂ)) (Ioi (1 : ℝ) ×ˢ Ioc (-1 : ℝ) 1) := by
      intro p hp
      have hp0 : 0 < p.1 := lt_trans one_pos hp.1
      refine ContinuousAt.continuousWithinAt ?_
      show ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 1) * ((ψ p.2 * Real.cos (k * c * p.2 * p.1) : ℝ) : ℂ)) p
      refine ContinuousAt.mul ?_ ?_
      · exact ContinuousAt.comp (g := fun θ : ℝ => (θ : ℂ) ^ (s - 1)) (f := Prod.fst)
          (Cvs.Route.Visibility.ProjectionShareSawtooth.hasDerivAt_ofReal_cpow hp0 (s - 1)).continuousAt continuous_fst.continuousAt
      · exact (Complex.continuous_ofReal.comp ((hψc.comp continuous_snd).mul
          (Real.continuous_cos.comp (by fun_prop)))).continuousAt
    refine hdom.mono' (hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioc))
      ((ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).2 (Eventually.of_forall fun p hp => ?_))
    show ‖(p.1 : ℂ) ^ (s - 1) * ((ψ p.2 * Real.cos (k * c * p.2 * p.1) : ℝ) : ℂ)‖ ≤ p.1 ^ (s.re - 1) * M
    have hp0 : 0 < p.1 := lt_trans one_pos hp.1
    rw [norm_mul, Cvs.Upstream.TrigMellinIntegralsContinuation.norm_cpow_sub_one hp0, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hp0.le _)
    calc |ψ p.2| * |Real.cos (k * c * p.2 * p.1)| ≤ M * 1 := by
          refine mul_le_mul ?_ (abs_cos_le_one _) (abs_nonneg _)
            ((abs_nonneg _).trans (hM 0 ⟨by norm_num, by norm_num⟩))
          have := hM p.2 ⟨hp.2.1.le, hp.2.2⟩
          rwa [Real.norm_eq_abs] at this
      _ = M := mul_one M
  refine (setIntegral_congr_fun measurableSet_Ioi fun θ _ => (integral_const_mul _ _).symm).trans ?_
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [hΨ, Cvs.Upstream.TrigMellinIntegralsContinuation.cosM]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  push_cast
  ring_nf

end Cvs.Prolate.Mellin.ModeExteriorRepresentation

end
