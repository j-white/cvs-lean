import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.VerticalLineShift
import Cvs.Zeta.ZetaDerivStripGrowth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole functionals of the E-image

`P₋F = MF(0)` for every `F`, so `P₋E = ME(0) = g′(1)`; `P₊v = Mv(1)` for compactly supported `v`.
`∫₀^Y E = −(a/2) g(0) + O(Y^{−1/4})`: Parseval against `1_(0,Y]`, whose transform is `Y^s/s`, then a
shift of the line from `Re s = ½` to `Re s = −¼` across the pole at `0`, with residue `ζ₁(0)·a·(−g(0))`.
-/

namespace Cvs.Xi.EImagePoleFunctionals

open Real Set Filter Topology MeasureTheory
open Complex (I)
open Cvs.Xi.EImageWindowPoisson (eimage)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR poleP poleM poleP_eq_of_tendsto integral_mul_eq_mellin)
open Cvs.WeilForm.MellinProfileStrips (gM gM_one norm_gM_le differentiableOn_gM mellinR_indicator rpow_le_corners)
open Cvs.Xi.EImageMellin (mellinR_eimage integrable_logScale_eimage)
open Cvs.Zeta.VerticalLineShift (integrable_of_decay integral_vline_sub_of_pole vline_re vline_im)
open Cvs.L2a.TailLogScaleTest (logScale)

/-! ### The pole functionals as Mellin values -/

/-- `MF(0) = P₋F` for every real `F`. -/
theorem mellinR_zero (F : ℝ → ℝ) : mellinR F 0 = (poleM F : ℂ) := by
  unfold mellinR mellin poleM
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  simp only [zero_sub, Complex.cpow_neg_one, smul_eq_mul, Complex.ofReal_div]
  ring

/-- `P₋F = Re MF(0)`. -/
theorem poleM_eq_mellinR (F : ℝ → ℝ) : poleM F = (mellinR F 0).re := by
  rw [mellinR_zero, Complex.ofReal_re]

/-- `MF(1) = ∫_{θ>0} F`. -/
theorem mellinR_one (F : ℝ → ℝ) : mellinR F 1 = ((∫ θ in Ioi (0 : ℝ), F θ : ℝ) : ℂ) := by
  unfold mellinR mellin
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  simp

/-- `P₊v = Re Mv(1)` when `v` vanishes off `[α, β]`. -/
theorem poleP_of_support {v : ℝ → ℝ} {α β : ℝ} (hsupp : ∀ θ ∉ Icc α β, v θ = 0) :
    poleP v = (mellinR v 1).re := by
  rw [mellinR_one, Complex.ofReal_re]
  refine poleP_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop (max β 0)] with Y hY
  rw [intervalIntegral.integral_of_le ((le_max_right _ _).trans hY)]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun θ hθ => hsupp θ fun h => ?_
  exact hθ.2 ⟨hθ.1, h.2.trans ((le_max_left _ _).trans hY)⟩

/-- **`P₋E = g′(1)`**: `ME(0) = a⁰ ζ₁(1) (dslope g 1)(1)`. -/
theorem poleM_eimage {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    poleM (eimage a G) = (deriv (gM G) 1).re := by
  rw [poleM_eq_mellinR, mellinR_eimage ha hG hG₁ hG0 hGi (by simp)]
  simp [dslope_same]

/-! ### The cut-off `1_(0,Y]` -/

/-- `M[1_(0,Y]](s) = Y^s/s` for `Re s > 0`. -/
theorem mellinR_indicator_Ioc {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 0 < s.re) :
    mellinR ((Ioc (0 : ℝ) Y).indicator fun _ => (1 : ℝ)) s = (Y : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [mellinR_indicator measurableSet_Ioc Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hY.le]
  simp only [Complex.ofReal_one, mul_one]
  rw [integral_cpow (Or.inl (by simp; linarith)), sub_add_cancel, Complex.ofReal_zero,
    Complex.zero_cpow hs0, sub_zero]

/-- `logScale 1_(0,Y] = 1_(−∞, log Y] e^{x/2}`. -/
theorem logScale_indicator_Ioc {Y : ℝ} (hY : 0 < Y) :
    logScale ((Ioc (0 : ℝ) Y).indicator fun _ => (1 : ℝ))
      = (Iic (Real.log Y)).indicator fun x => exp (1 / 2 * x) := by
  funext x
  unfold logScale
  by_cases h : x ≤ Real.log Y
  · have hm : exp x ∈ Ioc (0 : ℝ) Y := ⟨exp_pos x, (Real.le_log_iff_exp_le hY).1 h⟩
    rw [indicator_of_mem hm, indicator_of_mem (mem_Iic.2 h), one_mul]
    ring_nf
  · have hm : exp x ∉ Ioc (0 : ℝ) Y := fun hm => h ((Real.le_log_iff_exp_le hY).2 hm.2)
    rw [indicator_of_notMem hm, indicator_of_notMem (fun h' => h (mem_Iic.1 h')), zero_mul]

/-- `logScale 1_(0,Y]` is integrable and square-integrable. -/
theorem integrable_logScale_indicator_Ioc {Y : ℝ} (hY : 0 < Y) :
    Integrable (logScale ((Ioc (0 : ℝ) Y).indicator fun _ => (1 : ℝ)))
      ∧ MemLp (logScale ((Ioc (0 : ℝ) Y).indicator fun _ => (1 : ℝ))) 2 volume := by
  rw [logScale_indicator_Ioc hY]
  have hm : Measurable fun x : ℝ => exp (1 / 2 * x) := by fun_prop
  refine ⟨(integrable_indicator_iff measurableSet_Iic).2
    (integrableOn_exp_mul_Iic (by norm_num) _), ?_⟩
  rw [memLp_two_iff_integrable_sq ((hm.indicator measurableSet_Iic).aestronglyMeasurable)]
  have e : (fun x => ((Iic (Real.log Y)).indicator (fun x => exp (1 / 2 * x)) x) ^ 2)
      = (Iic (Real.log Y)).indicator fun x => exp (1 * x) := by
    funext x
    by_cases h : x ∈ Iic (Real.log Y)
    · rw [indicator_of_mem h, indicator_of_mem h, sq, ← exp_add]; ring_nf
    · rw [indicator_of_notMem h, indicator_of_notMem h]; ring
  rw [e]
  exact (integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_mul_Iic (by norm_num) _)

/-! ### The kernel `ζ₁(s) a^{1−s} (dslope g 1)(s)/s` on the strip `−¼ ≤ Re s ≤ ½` -/

/-- `ζ₁(0) = ½`. -/
theorem riemannZeta₁_zero : riemannZeta₁ 0 = 1 / 2 := by
  rw [riemannZeta₁, riemannZeta₀, if_neg zero_ne_one, riemannZeta_zero]
  norm_num

/-- `‖a^{1−s} (dslope g 1)(s) s⁻¹‖ ≤ C (1 + |Im s|)^{−3}` on `−½ ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem norm_kernel_le {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖(a : ℂ) ^ (1 - s) * dslope (gM G) 1 s * s⁻¹‖ ≤ C * (1 + |s.im|) ^ (-3 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := norm_gM_le hG hG₁ hG0
  set A := a ^ (3 / 2 : ℝ) + a ^ (-1 : ℝ)
  have hA0 : 0 ≤ A := by positivity
  refine ⟨8 * (A * |C₁|), fun s h1 h2 h3 => ?_⟩
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
  have hV : ‖s⁻¹‖ ≤ 1 / t := by
    rw [norm_inv, one_div]
    exact inv_anti₀ ht (by simpa [ht_def] using Complex.abs_im_le_norm s)
  have hinv : 1 / t ^ 3 ≤ 8 / (1 + t) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 1 + t ≤ 2 * t := by linarith
    have : (1 + t) ^ 3 ≤ (2 * t) ^ 3 := by gcongr
    nlinarith
  have hrp : (1 + t) ^ (-3 : ℝ) = 1 / (1 + t) ^ 3 := by
    rw [Real.rpow_neg (by positivity), one_div]; norm_cast
  calc ‖(a : ℂ) ^ (1 - s) * dslope (gM G) 1 s * s⁻¹‖
        = ‖(a : ℂ) ^ (1 - s)‖ * ‖dslope (gM G) 1 s‖ * ‖s⁻¹‖ := by simp only [norm_mul]
    _ ≤ A * (|C₁| / t / t) * (1 / t) := by gcongr
    _ = (A * |C₁|) * (1 / t ^ 3) := by field_simp
    _ ≤ (A * |C₁|) * (8 / (1 + t) ^ 3) := by gcongr
    _ = 8 * (A * |C₁|) * (1 + t) ^ (-3 : ℝ) := by rw [hrp]; ring

/-- `‖ζ₁(s) a^{1−s} (dslope g 1)(s) s⁻¹‖ ≤ B (1 + |Im s|)^{−9/8}` on `−¼ ≤ Re s ≤ ½`, `|Im s| ≥ 1`. -/
theorem norm_zeta₁_kernel_le {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    ∃ B, ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖riemannZeta₁ s * ((a : ℂ) ^ (1 - s) * dslope (gM G) 1 s * s⁻¹)‖
        ≤ B * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := by
  obtain ⟨C, hC⟩ := norm_kernel_le ha hG hG₁ hG0 hGi
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_zeta₁_mul_le (σ₀ := -1 / 4) (σ₁ := 1 / 2)
    (T₀ := 1) (CH := C) (H := fun s => (a : ℂ) ^ (1 - s) * dslope (gM G) 1 s * s⁻¹)
    (by norm_num) (by norm_num) (by norm_num)
    (fun s h1 h2 h3 => hC s (by linarith) (by linarith) h3)
  refine ⟨B, fun s h1 h2 h3 => ?_⟩
  have h := hB s h1 h2 (by simpa using h3)
  have e : (-(5 / 4 + (-1 / 4 : ℝ) / 2)) = -(9 / 8) := by norm_num
  rwa [e] at h

/-! ### `∫₀^Y E = −(a/2) g(0) + O(Y^{−1/4})` -/

/-- **`|∫₀^Y E + (a/2) g(0)| ≤ C Y^{−1/4}`** for `Y > 0`. -/
theorem abs_integral_eimage_add_le {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    ∃ C, ∀ Y : ℝ, 0 < Y →
      |(∫ θ in (0 : ℝ)..Y, eimage a G θ) + a / 2 * (gM G 0).re| ≤ C * Y ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨B, hB⟩ := norm_zeta₁_kernel_le ha hG hG₁ hG0 hGi
  set K : ℂ → ℂ := fun s => riemannZeta₁ s * ((a : ℂ) ^ (1 - s) * dslope (gM G) 1 s * s⁻¹)
    with hK
  have hB' : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖K s‖ ≤ |B| * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := fun s h1 h2 h3 =>
    (hB s h1 h2 h3).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
  set I₀ : ℝ := ∫ y : ℝ, ‖K (((-1 / 4 : ℝ) : ℂ) + y * I)‖ with hI₀
  refine ⟨I₀ / (2 * π), fun Y hY => ?_⟩
  -- the meromorphic integrand `Φ(s)/s`, `Φ(s) = Y^s ζ₁(s) a^{1−s} (dslope g 1)(s)`
  set Φ : ℂ → ℂ := fun s =>
    (Y : ℂ) ^ s * (riemannZeta₁ s * ((a : ℂ) ^ (1 - s) * dslope (gM G) 1 s)) with hΦ
  have hΦs : ∀ s : ℂ, Φ s / s = (Y : ℂ) ^ s * K s := by
    intro s; simp only [hΦ, hK, div_eq_mul_inv]; ring
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (dslope (gM G) 1) {s | -1 < s.re} :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds (by show (-1 : ℝ) < (1 : ℂ).re; norm_num))).2
      (differentiableOn_gM hG hG₁ hG0)
  have hΦd : DifferentiableOn ℂ Φ {s | -1 < s.re} := by
    intro s hs
    have hY' : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ s) s :=
      differentiableAt_id.const_cpow (Or.inl hY0)
    have hA : DifferentiableAt ℂ (fun s : ℂ => (a : ℂ) ^ (1 - s)) s :=
      ((differentiableAt_const _).sub differentiableAt_id).const_cpow
        (Or.inl (by exact_mod_cast ha.ne'))
    exact hY'.differentiableWithinAt.mul
      (differentiable_riemannZeta₁.differentiableAt.differentiableWithinAt.mul
        (hA.differentiableWithinAt.mul (hd s hs)))
  -- decay on the strip
  set DY : ℝ := Y ^ (-1 / 4 : ℝ) + Y ^ (1 / 2 : ℝ) + Y ^ (-1 / 4 : ℝ) + Y ^ (1 / 2 : ℝ) with hDY
  have hDY0 : 0 ≤ DY := by positivity
  have hdecay : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖Φ s / s‖ ≤ DY * |B| * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := by
    intro s h1 h2 h3
    rw [hΦs, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY, mul_assoc]
    exact mul_le_mul (rpow_le_corners hY ⟨le_rfl, le_rfl⟩ h1 h2) (hB' s h1 h2 h3)
      (norm_nonneg _) hDY0
  have hdecΦ : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖Φ s‖ ≤ DY * |B| * (1 + |s.im|) ^ (-(1 / 8 : ℝ)) := by
    intro s h1 h2 h3
    have hs0 : s ≠ 0 := by rintro rfl; simp at h3; linarith
    have e : Φ s = s * (Φ s / s) := by field_simp
    have hn : ‖s‖ ≤ 1 + |s.im| :=
      (Complex.norm_le_abs_re_add_abs_im s).trans
        (by gcongr; exact abs_le.mpr ⟨by linarith, by linarith⟩)
    have hp : (1 + |s.im|) ^ (-(1 / 8 : ℝ)) = (1 + |s.im|) * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := by
      rw [show (-(1 / 8 : ℝ)) = 1 + -(9 / 8) by norm_num, Real.rpow_add (by positivity),
        Real.rpow_one]
    rw [e, norm_mul, hp]
    calc ‖s‖ * ‖Φ s / s‖ ≤ (1 + |s.im|) * (DY * |B| * (1 + |s.im|) ^ (-(9 / 8 : ℝ))) :=
          mul_le_mul hn (hdecay s h1 h2 h3) (norm_nonneg _) (by positivity)
      _ = DY * |B| * ((1 + |s.im|) * (1 + |s.im|) ^ (-(9 / 8 : ℝ))) := by ring
  -- continuity and integrability on vertical lines off `0`
  have hcont : ∀ σ : ℝ, -1 < σ → σ ≠ 0 →
      Continuous fun y : ℝ => Φ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I) := by
    intro σ hσ hσ0
    have hl : Continuous fun y : ℝ => (σ : ℂ) + y * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    refine (hΦd.continuousOn.comp_continuous hl fun y => ?_).div hl fun y h => hσ0 ?_
    · show -1 < ((σ : ℂ) + y * I).re
      rw [vline_re]; exact hσ
    · simpa using congrArg Complex.re h
  have hint : ∀ σ : ℝ, -1 / 4 ≤ σ → σ ≤ 1 / 2 → σ ≠ 0 →
      Integrable fun y : ℝ => Φ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I) := by
    intro σ h1 h2 hσ0
    refine integrable_of_decay (hcont σ (by linarith) hσ0) (T₀ := 1) (B := DY * |B|)
      (κ := 9 / 8) (by norm_num) fun y hy => ?_
    have := hdecay ((σ : ℂ) + y * I) (by rw [vline_re]; exact h1) (by rw [vline_re]; exact h2)
      (by rw [vline_im]; exact hy)
    rwa [vline_im] at this
  -- Parseval against `1_(0,Y]`
  set ι : ℝ → ℝ := (Ioc (0 : ℝ) Y).indicator fun _ => (1 : ℝ) with hι
  have h1 : ∫ θ in (0 : ℝ)..Y, eimage a G θ = ∫ θ in Ioi (0 : ℝ), eimage a G θ * ι θ := by
    rw [intervalIntegral.integral_of_le hY.le]
    have e : (fun θ => eimage a G θ * ι θ) = (Ioc (0 : ℝ) Y).indicator (eimage a G) := by
      funext θ
      by_cases h : θ ∈ Ioc (0 : ℝ) Y <;> simp [hι, h]
    rw [e, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hE := integrable_logScale_eimage ha hG hG₁ hGi
  have hιL := integrable_logScale_indicator_Ioc hY
  have hP := integral_mul_eq_mellin hE.1 hE.2 hιL.1 hιL.2
  have hpt : ∀ t : ℝ, mellinR (eimage a G) (1 - (1 / 2 + t * I)) * mellinR ι (1 / 2 + t * I)
      = Φ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    have e : ((1 / 2 : ℝ) : ℂ) + t * I = 1 / 2 + t * I := by push_cast; ring
    rw [e]
    set s : ℂ := 1 / 2 + t * I
    have hsre : s.re = 1 / 2 := by simp [s]
    rw [mellinR_indicator_Ioc hY (by rw [hsre]; norm_num),
      mellinR_eimage ha hG hG₁ hG0 hGi (by rw [Complex.sub_re, Complex.one_re, hsre]; norm_num),
      sub_sub_cancel]
    simp only [hΦ, div_eq_mul_inv]
    ring
  rw [← hι] at hP
  simp_rw [hpt] at hP
  have hre := integral_re (𝕜 := ℂ) (hint (1 / 2) (by norm_num) le_rfl (by norm_num))
  simp only [RCLike.re_to_complex] at hre
  rw [hre] at hP
  -- the shift from `Re s = ½` to `Re s = −¼` across `0`
  have hΦd' : DifferentiableOn ℂ Φ {s | -1 / 4 - 1 / 4 < s.re ∧ s.re < 1 / 2 + 1 / 4} :=
    hΦd.mono fun s hs => by
      simp only [mem_ofPred_eq] at hs ⊢; linarith [hs.1]
  have hpole := integral_vline_sub_of_pole (φ := Φ) (σ₁ := -1 / 4) (σ₂ := 1 / 2) (x₀ := 0)
    (δ := 1 / 4) (κ := 1 / 8) (T₀ := 1) (B := DY * |B|) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hΦd' hdecΦ
  simp only [Complex.ofReal_zero, sub_zero] at hpole
  set U := ∫ y : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + y * I) / (((1 / 2 : ℝ) : ℂ) + y * I) with hU
  set R := ∫ y : ℝ, Φ (((-1 / 4 : ℝ) : ℂ) + y * I) / (((-1 / 4 : ℝ) : ℂ) + y * I) with hR
  have hUR : U = R + 2 * (π : ℂ) * Φ 0 := sub_eq_iff_eq_add'.mp hpole
  -- the residue `Φ(0) = −(a/2) g(0)`
  have hdsl : dslope (gM G) 1 0 = -gM G 0 := by
    rw [dslope_of_ne _ zero_ne_one, slope_def_module, gM_one hGi]; simp
  have hΦ0 : 2 * (π : ℂ) * Φ 0 = ((2 * π * (-(a / 2)) : ℝ) : ℂ) * gM G 0 := by
    simp only [hΦ, Complex.cpow_zero, riemannZeta₁_zero, sub_zero, Complex.cpow_one, hdsl]
    push_cast; ring
  -- the remainder on `Re s = −¼`
  have hRn : ‖R‖ ≤ Y ^ (-(1 / 4 : ℝ)) * I₀ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    rw [hI₀, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hΦs, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY, vline_re]
    norm_num
  have hmain : (∫ θ in (0 : ℝ)..Y, eimage a G θ) + a / 2 * (gM G 0).re = 1 / (2 * π) * R.re := by
    rw [h1, hP, hUR, Complex.add_re, hΦ0, Complex.re_ofReal_mul]
    field_simp
    ring
  rw [hmain, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (2 * π) * |R.re| ≤ 1 / (2 * π) * (Y ^ (-(1 / 4 : ℝ)) * I₀) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm R).trans hRn) (by positivity)
    _ = I₀ / (2 * π) * Y ^ (-(1 / 4 : ℝ)) := by ring

/-- **`∫₀^Y E → −(a/2) g(0)`.** -/
theorem tendsto_integral_eimage {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, eimage a G θ) atTop (𝓝 (-(a / 2) * (gM G 0).re)) := by
  obtain ⟨C, hC⟩ := abs_integral_eimage_add_le ha hG hG₁ hG0 hGi
  have hlim : Tendsto (fun Y : ℝ => C * Y ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with Y hY
  rw [Real.norm_eq_abs]
  convert hC Y hY using 2
  ring

/-- **`P₊E = −(a/2) g(0)`.** -/
theorem poleP_eimage {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    poleP (eimage a G) = -(a / 2) * (gM G 0).re :=
  poleP_eq_of_tendsto (tendsto_integral_eimage ha hG hG₁ hG0 hGi)

end Cvs.Xi.EImagePoleFunctionals
