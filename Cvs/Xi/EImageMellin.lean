import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin transform of the E-image

`E_G` is a Riemann sum of `G` with step `a/θ`, so `|E_G(θ)| ≤ K/θ` when `∫₀¹ G = 0`, and `logScale E_G ∈ L¹ ∩ L²`.
On `Re w < 1`, `M[E_G](w) = a^w ζ₁(1 − w) (dslope g 1)(1 − w)`, hence `M[E_G(n·)](1 − s) Mv(s) = n^{s−1} ζ₁(s) H(s)`.
-/

namespace Cvs.Xi.EImageMellin

open Real Set Filter Topology MeasureTheory Asymptotics
open Complex (I)
open Cvs.Xi.EImageWindowPoisson (eimage eimage_of_lt eimage_congr)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.WeilForm.MellinProfileStrips (gM Hfun differentiableOn_gM gM_one)
open Cvs.L2a.TailLogScaleTest (logScale)

/-! ### The E-image as a sum over `range ⌊θ/a⌋₊` -/

/-- `E_G(θ) = (a/θ) Σ_{n < ⌊θ/a⌋₊} G((n + 1)a/θ)`. -/
theorem eimage_eq_sum_range (a : ℝ) (G : ℝ → ℝ) (θ : ℝ) :
    eimage a G θ = a / θ * ∑ n ∈ Finset.range ⌊θ / a⌋₊, G ((n + 1) * a / θ) := by
  unfold eimage
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast; ring_nf

/-- **Measurability** of `E_G` for measurable `G`. -/
theorem measurable_eimage (a : ℝ) {G : ℝ → ℝ} (hGm : Measurable G) : Measurable (eimage a G) := by
  have hf : Measurable fun p : ℝ × ℕ => ∑ n ∈ Finset.range p.2, G ((n + 1) * a / p.1) :=
    measurable_from_prod_countable_left fun N => by
      show Measurable fun θ : ℝ => ∑ n ∈ Finset.range N, G ((n + 1) * a / θ)
      fun_prop
  have e : eimage a G = fun θ => a / θ * (fun p : ℝ × ℕ =>
      ∑ n ∈ Finset.range p.2, G ((n + 1) * a / p.1)) (θ, ⌊θ / a⌋₊) := by
    funext θ; exact eimage_eq_sum_range a G θ
  rw [e]
  exact (measurable_const.div measurable_id).mul
    (hf.comp (measurable_id.prodMk (Nat.measurable_floor.comp (measurable_id.div_const a))))

/-- `E_G` is measurable when `G` is continuous on `[0, 1]`. -/
theorem measurable_eimage_of_continuousOn {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hGc : ContinuousOn G (Icc 0 1)) : Measurable (eimage a G) := by
  set G' : ℝ → ℝ := fun u => G (projIcc (0 : ℝ) 1 zero_le_one u)
  have hG' : Continuous G' := hGc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun u => (projIcc (0 : ℝ) 1 zero_le_one u).2
  rw [eimage_congr ha (H := G') fun s hs => by
    simp [G', projIcc_of_mem zero_le_one (Ioc_subset_Icc_self hs)]]
  exact measurable_eimage a hG'.measurable

/-! ### The Riemann-sum bound -/

/-- A `C¹` profile on `[0, 1]` is bounded and Lipschitz there. -/
theorem exists_bound_lipschitz {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) :
    ∃ L M, 0 ≤ L ∧ 0 ≤ M ∧ (∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |G y - G x| ≤ L * |y - x|)
      ∧ ∀ u ∈ Icc (0 : ℝ) 1, |G u| ≤ M := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hG₁
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  refine ⟨max L 0, max M 0, le_max_right _ _, le_max_right _ _, fun x hx y hy => ?_,
    fun u hu => (hM u hu).trans (le_max_left _ _)⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G) (f' := G₁)
    (fun z hz => (hG z hz).hasDerivWithinAt) (fun z hz => (hL z hz).trans (le_max_left L 0))
    (convex_Icc 0 1) hx hy
  simpa [Real.norm_eq_abs] using h

/-- **`|E_G(θ)| ≤ K/θ`** for a `C¹` profile with `∫₀¹ G = 0`: `E_G` is a Riemann sum of `G` with
step `a/θ`. -/
theorem abs_eimage_le {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    ∃ K, 0 ≤ K ∧ ∀ θ, 0 < θ → |eimage a G θ| ≤ K / θ := by
  obtain ⟨L, M, hL0, hM0, hLip, hM⟩ := exists_bound_lipschitz hG hG₁
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  have hGii : IntervalIntegrable G volume 0 1 := hGc.intervalIntegrable_of_Icc zero_le_one
  have hsub : ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ 1 → IntervalIntegrable G volume c d := fun c d hc hcd hd =>
    hGii.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hc hd)
  refine ⟨(L + M) * a, by positivity, fun θ hθ => ?_⟩
  rcases lt_or_ge θ a with hθa | hθa
  · rw [eimage_of_lt ha hθa, abs_zero]; positivity
  set h := a / θ with hh
  have hh0 : 0 < h := by positivity
  set N := ⌊θ / a⌋₊ with hN
  have hNh : (N : ℝ) * h ≤ 1 := by
    have := Nat.floor_le (div_nonneg hθ.le ha.le)
    rw [hh, ← mul_div_assoc, div_le_one hθ]
    rw [le_div_iff₀ ha] at this; linarith
  have hNh' : 1 < ((N : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (θ / a)
    rw [hh, ← mul_div_assoc, one_lt_div hθ]
    rw [div_lt_iff₀ ha] at this; linarith
  have hE : eimage a G θ = ∑ n ∈ Finset.range N, h * G ((n + 1) * h) := by
    rw [eimage_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hh, mul_div_assoc]
  have hmem : ∀ n ∈ Finset.range N, ∀ x ∈ Icc ((n : ℝ) * h) ((n + 1) * h), x ∈ Icc (0 : ℝ) 1 := by
    intro n hn x hx
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hn
    refine ⟨le_trans (by positivity) hx.1, hx.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_right hn' hh0.le).trans hNh
  have hpiece : ∀ n ∈ Finset.range N,
      |h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u| ≤ L * h * h := by
    intro n hn
    have hnh : (n : ℝ) * h ≤ (n + 1) * h := by nlinarith
    have hint := hsub _ _ (by positivity) hnh (hmem n hn _ (right_mem_Icc.2 hnh)).2
    have e : h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u
        = ∫ u in ((n : ℝ) * h)..((n + 1) * h), (G ((n + 1) * h) - G u) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint, intervalIntegral.integral_const,
        smul_eq_mul]
      ring_nf
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ) * h) (b := (n + 1) * h)
      (C := L * h) (f := fun u => G ((n + 1) * h) - G u) fun x hx => by
        rw [uIoc_of_le hnh] at hx
        have hx' : x ∈ Icc ((n : ℝ) * h) ((n + 1) * h) := Ioc_subset_Icc_self hx
        rw [Real.norm_eq_abs]
        refine (hLip _ (hmem n hn _ hx') _ (hmem n hn _ (right_mem_Icc.2 hnh))).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hL0
        rw [abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1]
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [show ((n : ℝ) + 1) * h - n * h = h by ring, abs_of_pos hh0]
  have hsplit : ∫ u in (0 : ℝ)..(N * h), G u
      = ∑ n ∈ Finset.range N, ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := G) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * h) (n := N) fun k hk => by
        have hkh : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
        exact hsub _ _ (by positivity) hkh
          (by push_cast; exact (hmem k (Finset.mem_range.2 hk) _ (right_mem_Icc.2 (by
            push_cast at hkh; exact hkh))).2)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at this
    exact this.symm
  have htail : |∫ u in ((N : ℝ) * h)..1, G u| ≤ M * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N : ℝ) * h) (b := 1)
      (C := M) (f := G) fun x hx => by
        rw [uIoc_of_le hNh] at hx
        rw [Real.norm_eq_abs]
        exact hM x ⟨le_trans (by positivity) hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 - N * h by linarith)] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    nlinarith
  have hadd : (∫ u in (0 : ℝ)..(N * h), G u) + ∫ u in ((N : ℝ) * h)..1, G u = 0 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hsub _ _ le_rfl (by positivity) hNh)
      (hsub _ _ (by positivity) hNh le_rfl), hGi]
  have hdecomp : eimage a G θ = (∑ n ∈ Finset.range N,
      (h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u))
        - ∫ u in ((N : ℝ) * h)..1, G u := by
    rw [hE, Finset.sum_sub_distrib, ← hsplit]; linarith
  have hS : |∑ n ∈ Finset.range N,
      (h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u)| ≤ L * h := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpiece).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (N : ℝ) * (L * h * h) = L * h * (N * h) := by ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left hNh (by positivity)).trans_eq (mul_one _)
  rw [hdecomp]
  refine (abs_sub _ _).trans ?_
  have : (L + M) * a / θ = L * h + M * h := by rw [hh]; ring
  rw [this]
  linarith

/-! ### `logScale E_G ∈ L¹ ∩ L²` -/

/-- **`logScale E_G` is integrable and square-integrable.** -/
theorem integrable_logScale_eimage {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    Integrable (logScale (eimage a G)) ∧ MemLp (logScale (eimage a G)) 2 volume := by
  obtain ⟨K, hK0, hK⟩ := abs_eimage_le ha hG hG₁ hGi
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  have hEm := measurable_eimage_of_continuousOn ha hGc
  set c := Real.log a - 1
  set d : ℝ → ℝ := (Ioi c).indicator fun s => K * exp (-(1 / 2) * s) with hd
  have hdm : Measurable d := (measurable_const.mul (measurable_exp.comp
    (measurable_const.mul measurable_id))).indicator measurableSet_Ioi
  have hdi : Integrable d := (integrable_indicator_iff measurableSet_Ioi).2
    ((exp_neg_integrableOn_Ioi c (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K)
  have hdL : MemLp d 2 volume := by
    rw [memLp_two_iff_integrable_sq hdm.aestronglyMeasurable]
    have e : (fun s => d s ^ 2) = (Ioi c).indicator fun s => K ^ 2 * exp (-1 * s) := by
      funext s
      by_cases h : s ∈ Ioi c
      · rw [hd, indicator_of_mem h, indicator_of_mem h, mul_pow, sq (exp _), ← exp_add]; ring_nf
      · rw [hd, indicator_of_notMem h, indicator_of_notMem h]; ring
    rw [e]
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((exp_neg_integrableOn_Ioi c (by norm_num : (0 : ℝ) < 1)).const_mul _)
  have hfm : AEStronglyMeasurable (logScale (eimage a G)) volume := by
    unfold logScale
    exact ((hEm.comp measurable_exp).mul
      (measurable_exp.comp (measurable_id.div_const 2))).aestronglyMeasurable
  have hpt : ∀ s, |logScale (eimage a G) s| ≤ d s := by
    intro s
    unfold logScale
    by_cases h : s ∈ Ioi c
    · rw [hd, indicator_of_mem h, abs_mul, abs_of_pos (exp_pos _)]
      calc |eimage a G (exp s)| * exp (s / 2) ≤ K / exp s * exp (s / 2) :=
            mul_le_mul_of_nonneg_right (hK _ (exp_pos s)) (exp_pos _).le
        _ = K * exp (-(1 / 2) * s) := by
            rw [div_mul_eq_mul_div, div_eq_iff (exp_pos _).ne', mul_assoc, ← exp_add]; ring_nf
    · have hs : s < Real.log a := by simp only [mem_Ioi, not_lt] at h; linarith
      have h0 : eimage a G (exp s) = 0 := eimage_of_lt ha ((exp_lt_exp.2 hs).trans_eq (exp_log ha)) G
      rw [hd, indicator_of_notMem h, h0, zero_mul, abs_zero]
  refine ⟨hdi.mono' hfm (Eventually.of_forall fun s => ?_), hdL.of_le hfm (Eventually.of_forall fun s => ?_)⟩
  · rw [Real.norm_eq_abs]; exact hpt s
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact (hpt s).trans (le_abs_self _)

/-! ### Mellin transforms of reciprocal dilates -/

/-- `M[θ⁻¹ φ(b/θ)](w) = b^{w−1} M[φ](1 − w)` for `b > 0`. -/
theorem mellin_inv_dil (φ : ℝ → ℂ) {b : ℝ} (hb : 0 < b) (w : ℂ) :
    mellin (fun θ : ℝ => (θ : ℂ)⁻¹ * φ (b * θ⁻¹)) w = (b : ℂ) ^ (w - 1) * mellin φ (1 - w) := by
  have e : (fun θ : ℝ => (θ : ℂ)⁻¹ * φ (b * θ⁻¹))
      = fun θ : ℝ => (θ : ℂ) ^ (-1 : ℂ) • φ (b * θ⁻¹) := by
    funext θ; rw [Complex.cpow_neg_one, smul_eq_mul]
  rw [e, mellin_cpow_smul, mellin_comp_inv (fun y => φ (b * y)), mellin_comp_mul_left φ _ hb,
    smul_eq_mul]
  congr 2 <;> ring

/-- `θ⁻¹ φ(b/θ)` is Mellin-convergent at `w` when `φ` is at `1 − w`. -/
theorem mellinConvergent_inv_dil {φ : ℝ → ℂ} {b : ℝ} (hb : 0 < b) {w : ℂ}
    (hφ : MellinConvergent φ (1 - w)) :
    MellinConvergent (fun θ : ℝ => (θ : ℂ)⁻¹ * φ (b * θ⁻¹)) w := by
  have e : (fun θ : ℝ => (θ : ℂ)⁻¹ * φ (b * θ⁻¹))
      = fun θ : ℝ => (θ : ℂ) ^ (-1 : ℂ) • φ (b * θ ^ (-1 : ℝ)) := by
    funext θ; rw [Complex.cpow_neg_one, smul_eq_mul, Real.rpow_neg_one]
  rw [e]
  refine MellinConvergent.cpow_smul.2 ?_
  refine (MellinConvergent.comp_rpow (f := fun y => φ (b * y)) (a := -1) (by norm_num)).2 ?_
  refine (MellinConvergent.comp_mul_left (f := φ) hb).2 ?_
  convert hφ using 1
  push_cast; ring

/-- The indicator `1_{(0,1]} G` of a profile continuous on `[0, 1]` is Mellin-convergent on `Re s > 0`. -/
theorem mellinConvergent_indicator {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1)) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (fun u : ℝ => (((Ioc (0 : ℝ) 1).indicator G u : ℝ) : ℂ)) s := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  have e : (fun u : ℝ => (((Ioc (0 : ℝ) 1).indicator G u : ℝ) : ℂ))
      = (Ioc (0 : ℝ) 1).indicator (fun u => (G u : ℂ)) := by
    funext u; by_cases h : u ∈ Ioc (0 : ℝ) 1 <;> simp [h]
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0) ?_ ?_ (by linarith) ?_ hs
  · refine (Integrable.integrableOn ?_).locallyIntegrableOn
    rw [e]
    exact (integrable_indicator_iff measurableSet_Ioc).2
      ((Complex.continuous_ofReal.comp_continuousOn hGc).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)
  · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with θ hθ
    have : θ ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.2 hθ) h.2
    simp [this]
  · refine IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases h : θ ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem h]; simpa [Real.norm_eq_abs] using hM θ (Ioc_subset_Icc_self h)
    · rw [indicator_of_notMem h, abs_zero]
      exact (norm_nonneg _).trans (hM 0 (left_mem_Icc.2 zero_le_one))

/-! ### The factorisation on `Re w < 0` -/

/-- On `θ > 0`, `E_G(θ) = a Σ_{n ≥ 0} θ⁻¹ (1_{(0,1]}G)((n + 1)a/θ)`. -/
theorem eimage_eq_tsum {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ((eimage a G θ : ℝ) : ℂ) = (a : ℂ) * ∑' n : ℕ,
      (θ : ℂ)⁻¹ * (((Ioc (0 : ℝ) 1).indicator G (((n : ℝ) + 1) * a * θ⁻¹) : ℝ) : ℂ) := by
  set N := ⌊θ / a⌋₊
  have hzero : ∀ n ∉ Finset.range N,
      (θ : ℂ)⁻¹ * (((Ioc (0 : ℝ) 1).indicator G (((n : ℝ) + 1) * a * θ⁻¹) : ℝ) : ℂ) = 0 := by
    intro n hn
    have hn' : N ≤ n := not_lt.1 (Finset.mem_range.not.1 hn)
    have hlt : θ / a < (n : ℝ) + 1 :=
      (Nat.lt_floor_add_one (θ / a)).trans_le (by exact_mod_cast Nat.add_le_add_right hn' 1)
    have : ((n : ℝ) + 1) * a * θ⁻¹ ∉ Ioc (0 : ℝ) 1 := by
      intro h
      have h2 := h.2
      rw [← div_eq_mul_inv, div_le_one hθ] at h2
      rw [div_lt_iff₀ ha] at hlt
      linarith
    rw [indicator_of_notMem this]; simp
  rw [tsum_eq_sum hzero, eimage_eq_sum_range, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hn
  have hmem : ((n : ℝ) + 1) * a * θ⁻¹ ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [← div_eq_mul_inv, div_le_one hθ]
    have := (hn'.trans (Nat.floor_le (div_nonneg hθ.le ha.le)))
    rw [le_div_iff₀ ha] at this; exact this
  rw [indicator_of_mem hmem, ← div_eq_mul_inv]
  ring

/-- **The factorisation on `Re w < 0`**: `M[E_G](w) = a^w ζ(1 − w) g(1 − w)`. -/
theorem mellinR_eimage_of_re_neg {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1))
    {w : ℂ} (hw : w.re < 0) :
    mellinR (eimage a G) w = (a : ℂ) ^ w * riemannZeta (1 - w) * gM G (1 - w) := by
  set φ : ℝ → ℂ := fun u => (((Ioc (0 : ℝ) 1).indicator G u : ℝ) : ℂ) with hφ
  have hs : 0 < (1 - w).re := by simp; linarith
  have hφc : MellinConvergent φ (1 - w) := mellinConvergent_indicator hGc hs
  have hgM : mellin φ (1 - w) = gM G (1 - w) := rfl
  set b : ℕ → ℝ := fun n => ((n : ℝ) + 1) * a with hbdef
  have hb : ∀ n, 0 < b n := fun n => by positivity
  set T : ℕ → ℝ → ℂ := fun n θ => (θ : ℂ)⁻¹ * φ (b n * θ⁻¹) with hT
  set F : ℕ → ℝ → ℂ := fun n θ => (θ : ℂ) ^ (w - 1) * T n θ with hF
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    mellinConvergent_inv_dil (hb n) hφc
  -- the norm integrals
  set ψ : ℝ → ℂ := fun u => ((‖φ u‖ : ℝ) : ℂ) with hψ
  have hnorm : ∀ n, ∫ θ in Ioi (0 : ℝ), ‖F n θ‖
      = ‖((b n : ℝ) : ℂ) ^ ((w.re : ℂ) - 1)‖ * ‖mellin ψ (1 - w.re)‖ := by
    intro n
    have h1 : (((∫ θ in Ioi (0 : ℝ), ‖F n θ‖ : ℝ)) : ℂ)
        = mellin (fun θ : ℝ => (θ : ℂ)⁻¹ * ψ (b n * θ⁻¹)) (w.re : ℂ) := by
      rw [← integral_complex_ofReal]
      unfold mellin
      refine setIntegral_congr_fun measurableSet_Ioi fun θ (hθ : 0 < θ) => ?_
      simp only [hF, hT, hψ, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
        Complex.norm_cpow_eq_rpow_re_of_pos hθ, Complex.sub_re, Complex.one_re]
      push_cast
      rw [Complex.ofReal_cpow hθ.le, Real.norm_eq_abs, abs_of_pos hθ]
      push_cast; ring
    have h2 := mellin_inv_dil ψ (hb n) (w.re : ℂ)
    rw [h2] at h1
    have h3 := congrArg (fun z : ℂ => ‖z‖) h1
    simp only [Complex.norm_real, Real.norm_eq_abs] at h3
    rw [← norm_mul, ← h3, abs_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
  have hsum : Summable fun n => ∫ θ in Ioi (0 : ℝ), ‖F n θ‖ := by
    have e : ∀ n : ℕ, ∫ θ in Ioi (0 : ℝ), ‖F n θ‖
        = ((n : ℝ) + 1) ^ (w.re - 1) * (a ^ (w.re - 1) * ‖mellin ψ (1 - w.re)‖) := by
      intro n
      rw [hnorm, Complex.norm_cpow_eq_rpow_re_of_pos (hb n), Complex.sub_re, Complex.ofReal_re,
        Complex.one_re, hbdef]
      dsimp only
      rw [Real.mul_rpow (by positivity) ha.le]; ring
    simp_rw [e]
    refine Summable.mul_right _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show w.re - 1 < -1 by linarith))
    simpa using this
  have hE : mellinR (eimage a G) w = (a : ℂ) * ∑' n, mellin (T n) w := by
    have h1 : mellinR (eimage a G) w = ∫ θ in Ioi (0 : ℝ), (a : ℂ) * ∑' n, F n θ := by
      unfold mellinR mellin
      refine setIntegral_congr_fun measurableSet_Ioi fun θ (hθ : 0 < θ) => ?_
      show (θ : ℂ) ^ (w - 1) • ((eimage a G θ : ℝ) : ℂ) = _
      rw [smul_eq_mul, eimage_eq_tsum ha G hθ, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      congr 1; funext n
      simp only [hF, hT, hbdef, hφ]
      ring
    rw [h1, integral_const_mul, ← integral_tsum_of_summable_integral_norm hFi hsum]
    rfl
  have hT' : ∀ n, mellin (T n) w = ((n : ℂ) + 1) ^ (w - 1) * (a : ℂ) ^ (w - 1) * gM G (1 - w) := by
    intro n
    rw [mellin_inv_dil φ (hb n) w, hgM, hbdef]
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) ha.le]
    push_cast; ring
  have hz : riemannZeta (1 - w) = ∑' n : ℕ, ((n : ℂ) + 1) ^ (w - 1) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith)]
    congr 1; funext n
    rw [one_div, ← Complex.cpow_neg, neg_sub]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hE]
  simp_rw [hT']
  rw [tsum_mul_right, tsum_mul_right, ← hz, Complex.cpow_sub _ _ ha0, Complex.cpow_one]
  field_simp

/-! ### The factorisation on `Re w < 1` -/

/-- Locally integrable on `(0, ∞)`: a measurable function with `|F(θ)| ≤ K/θ` there. -/
theorem locallyIntegrableOn_of_le_div {F : ℝ → ℝ} (hFm : Measurable F) {K : ℝ}
    (hK : ∀ θ, 0 < θ → |F θ| ≤ K / θ) : LocallyIntegrableOn (fun θ => (F θ : ℂ)) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkc
  rcases k.eq_empty_or_nonempty with rfl | hne
  · exact integrableOn_empty
  obtain ⟨c, hck, hc⟩ := hkc.exists_isLeast hne
  have hc0 : 0 < c := hk hck
  refine Measure.integrableOn_of_bounded (M := |K| / c) hkc.measure_lt_top.ne
    (Complex.measurable_ofReal.comp hFm).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hkc.measurableSet).2 (Eventually.of_forall fun θ hθ => ?_)
  have hθ0 : 0 < θ := hk hθ
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (hK θ hθ0).trans ((div_le_div_of_nonneg_right (le_abs_self K) hθ0.le).trans ?_)
  exact div_le_div_of_nonneg_left (abs_nonneg _) hc0 (hc hθ)

/-- **The Mellin factorisation of the E-image**: on `Re w < 1`,
`M[E_G](w) = a^w ζ₁(1 − w) (dslope g 1)(1 − w)`. -/
theorem mellinR_eimage {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {w : ℂ} (hw : w.re < 1) :
    mellinR (eimage a G) w = (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w) := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := abs_eimage_le ha hG hG₁ hGi
  have hEm := measurable_eimage_of_continuousOn ha hGc
  set U : Set ℂ := {w | w.re < 1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hloc := locallyIntegrableOn_of_le_div hEm hK
  have hL : DifferentiableOn ℂ (mellinR (eimage a G)) U := by
    intro z (hz : z.re < 1)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := z.re - 1) hloc ?_ hz ?_
      (by linarith)
    · refine IsBigO.of_bound K ?_
      filter_upwards [eventually_gt_atTop 0] with θ hθ
      rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_neg_one,
        abs_of_pos (inv_pos.2 hθ), ← div_eq_mul_inv]
      exact hK θ hθ
    · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with θ (hθ : θ < a)
      simp [eimage_of_lt ha hθ]
  have hopen1 : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (dslope (gM G) 1) {s | -1 < s.re} :=
    (Complex.differentiableOn_dslope (hopen1.mem_nhds (by show (-1 : ℝ) < (1 : ℂ).re; norm_num))).2
      (differentiableOn_gM hG hG₁ hG0)
  have hR : DifferentiableOn ℂ
      (fun w : ℂ => (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w)) U := by
    intro z (hz : z.re < 1)
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (a : ℂ) ^ w) z :=
      differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast ha.ne'))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => riemannZeta₁ (1 - w)) z :=
      differentiable_riemannZeta₁.differentiableAt.comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => dslope (gM G) 1 (1 - w)) z := by
      have hz' : (1 - z) ∈ {s : ℂ | -1 < s.re} := by show -1 < (1 - z).re; simp; linarith
      exact ((hd.differentiableAt (hopen1.mem_nhds hz'))).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    exact (h1.mul h2).mul h3
  have hconv : Convex ℝ U := convex_halfSpace_re_lt 1
  have hmem : (-1 : ℂ) ∈ U := by show (-1 : ℂ).re < 1; norm_num
  have hev : mellinR (eimage a G) =ᶠ[𝓝 (-1 : ℂ)]
      fun w : ℂ => (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w) := by
    have hopen0 : IsOpen {w : ℂ | w.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen0.mem_nhds (show (-1 : ℂ).re < 0 by norm_num)] with z (hz : z.re < 0)
    rw [mellinR_eimage_of_re_neg ha hGc hz]
    have hz1 : 1 - z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [riemannZeta_eq_inv_sub_mul hz1, dslope_of_ne _ hz1, slope_def_module, gM_one hGi, sub_zero,
      smul_eq_mul]
    ring
  exact (hL.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hU)
    hconv.isPreconnected hmem hev hw

/-- **Dilates**: for `n ≥ 1` and `Re s > 0`, `M[E_G(n·)](1 − s) Mv(s) = n^{s−1} ζ₁(s) H(s)`. -/
theorem mellinR_eimage_dil {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) (v : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {s : ℂ} (hs : 0 < s.re) :
    mellinR (fun θ => eimage a G (n * θ)) (1 - s) * mellinR v s
      = (n : ℂ) ^ (s - 1) * riemannZeta₁ s * Hfun a G v s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : mellinR (fun θ => eimage a G (n * θ)) (1 - s)
      = (n : ℂ) ^ (-(1 - s)) * mellinR (eimage a G) (1 - s) := by
    unfold mellinR
    exact mellin_comp_mul_left (fun θ => ((eimage a G θ : ℝ) : ℂ)) (1 - s) hn0
  rw [h1, mellinR_eimage ha hG hG₁ hG0 hGi (by simp; linarith), sub_sub_cancel, neg_sub]
  unfold Hfun
  ring

end Cvs.Xi.EImageMellin
