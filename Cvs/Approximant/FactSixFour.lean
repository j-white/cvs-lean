import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.StripApproxFromHermite
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.RecentredTransform
import Cvs.Limit.ConstantMinimiserLink
import Cvs.Limit.MomentSpineXiCoefficients
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.XiOffRealLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Fact 6.4: Connes' `k̂_λ` converges to `Ξ` uniformly on closed substrips of `|Im z| < 1/2`

Connes' `k_λ` (arXiv:2602.04022 (17)), `λ = √x`, is the prolate test `Cvs.Approximant.ConnesVectorRealScale.connesK` reflected and
scaled by `x^{3/4}`. With `k̂(z) = ∫ k(u) u^{iz} d^*u`, the rescaled `(overlap/16) k̂_λ` is within an
explicit per-scale error of `Ξ` on `|Im z| ≤ a < 1`, and the error tends to `0` for `a < 1/2`.
-/

noncomputable section

open Real Set Filter MeasureTheory Topology

namespace Cvs.Approximant.FactSixFour
open Cvs.ZeroCounting

open Cvs.L2a.TailLogScaleTest (logScale)

/-- The scalar `β_x = 32 x^{−3/4}/overlap(2πx)` that matches Connes' test to `Φ`. -/
def beta (x : ℝ) : ℝ :=
  32 * (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ * x ^ (-(3 / 4 : ℝ))

/-- The prolate profile behind Connes' test at scale `x`. -/
abbrev profile (x : ℝ) : ℝ → ℝ := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1

theorem beta_ne_zero {x : ℝ} (hx : 16 ≤ x) : beta x ≠ 0 := by
  have h := Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hx0 : 0 < x := by linarith
  have hpos : 0 < 1 / 20 * x ^ (1 / 4 : ℝ) := by positivity
  have hb : (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ ≠ 0 := fun h0 => by
    rw [h0, abs_zero] at h; linarith
  unfold beta
  exact mul_ne_zero (mul_ne_zero (by norm_num) hb) (Real.rpow_pos_of_pos hx0 _).ne'

/-- **Fact 6.4 at one scale, for the recentred test**: for `x ≥ 16` and `|Im z| ≤ a < 1`,
`(2/β_x)` times the recentred transform of Connes' test is within `2√(profileErr) + windowErr`
of `Ξ(z)`. -/
theorem norm_two_div_mul_phase_connesK_sub_Xi_le {x a : ℝ} (hx : 16 ≤ x) (ha : a < 1) {z : ℂ}
    (hz : |z.im| ≤ a) :
    ‖((2 / beta x : ℝ) : ℂ) * (Cvs.Finite.RecentredTransform.phase (Real.log x) z *
        FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Approximant.ConnesVectorRealScale.connesK x)) z)
        - Cvs.Limit.ZeroFreeApproximantsRH.Xi z‖
      ≤ 2 * √(Cvs.Approximant.StripApproxFromHermite.profileErr x a
            (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ (profile x))
        + Cvs.Approximant.StripApproxFromHermite.windowErr x a := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hL0 : 0 < L := by linarith
  have hx4 : 4 / π ≤ x := by
    have : 4 / π ≤ 2 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    linarith
  set b := (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ with hb
  set β := beta x with hβdef
  have hβ : β = 32 * b * x ^ (-(3 / 4 : ℝ)) := rfl
  have hβ0 : β ≠ 0 := beta_ne_zero hx
  have hG : ContinuousOn (profile x) (Icc 0 1) :=
    (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
  set k := Cvs.Approximant.ConnesVectorRealScale.connesK x with hk
  have hkO : k = Cvs.Approximant.StripApproxFromHermite.kOf x (profile x) := rfl
  set f : ℝ → ℝ := (Ioc 0 L).indicator k with hf
  set h : ℝ → ℝ := fun t => β * Cvs.Xi.XiOffRealLine.phiWindow L t with hh
  have hkf : k =ᵐ[volume] f := by
    filter_upwards [Cvs.Approximant.ConnesVectorRealScale.connesK_ae_supp hx0] with s hs
    by_cases hm : s ∈ Ioc (0:ℝ) L
    · simp [hf, indicator_of_mem hm]
    · rw [hf, indicator_of_notMem hm]; exact hs hm
  have hFLk : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf k) z
      = FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z :=
    Cvs.Limit.ConstantMinimiserLink.fourierLaplace_cf_congr_ae hkf z
  have hFLh : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z
      = (β : ℂ) * FourierLaplace.fourierLaplace
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Xi.XiOffRealLine.phiWindow L)) z :=
    Cvs.Finite.DisplacementIdentity.fourierLaplace_cf_const_mul β _ z
  have hfm : MemLp f 2 volume :=
    (Cvs.Approximant.ConnesVectorRealScale.connesK_memLp hx0).indicator measurableSet_Ioc.nullMeasurableSet
  have hhm : MemLp h 2 volume := (Cvs.Approximant.StripApproxFromHermite.memLp_phiWindow L).const_mul β
  have hfs : ∀ s ∉ Ioc (0:ℝ) L, f s = 0 := fun s hs => by rw [hf, indicator_of_notMem hs]
  have hhs : ∀ s ∉ Ioc (0:ℝ) L, h s = 0 := fun s hs => by
    simp only [hh, Cvs.Xi.XiOffRealLine.phiWindow, indicator_of_notMem hs, mul_zero]
  -- the energy of the difference
  have hdiff : (∫ t : ℝ, (f t - h t) ^ 2)
      = ∫ t in (0:ℝ)..L, (Cvs.Approximant.StripApproxFromHermite.kOf x (profile x) t
          - 32 * b * x ^ (-(3 / 4 : ℝ)) * Cvs.Approximant.StripApproxFromHermite.phiShift L t) ^ 2 := by
    have e : (fun t : ℝ => (f t - h t) ^ 2) = (Ioc 0 L).indicator (fun t =>
        (Cvs.Approximant.StripApproxFromHermite.kOf x (profile x) t
          - 32 * b * x ^ (-(3 / 4 : ℝ)) * Cvs.Approximant.StripApproxFromHermite.phiShift L t) ^ 2) := by
      funext t
      by_cases hm : t ∈ Ioc (0:ℝ) L
      · simp only [hf, hh, Cvs.Xi.XiOffRealLine.phiWindow, indicator_of_mem hm, hkO, hβ,
          Cvs.Approximant.StripApproxFromHermite.phiShift]
      · simp only [hf, hh, Cvs.Xi.XiOffRealLine.phiWindow, indicator_of_notMem hm, mul_zero,
          sub_zero]
        norm_num
    rw [e, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hL0.le]
  have hQ := Cvs.Approximant.StripApproxFromHermite.integral_kOf_sub_phiShift_sq_le hx4 b hG
  set Q := 2 * (harmonic ⌊x⌋₊ : ℝ)
      * (∫ u in Icc (0 : ℝ) 1, (profile x u - b * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2)
    + 2 * (32 * b * x ^ (-(3 / 4 : ℝ))) ^ 2 * ∫ t in (0:ℝ)..L, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2
    with hQdef
  -- the split
  set P := Cvs.Finite.RecentredTransform.phase L z with hP
  set W := P * FourierLaplace.fourierLaplace
    (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Xi.XiOffRealLine.phiWindow L)) z with hW
  have hsplit : ((2 / β : ℝ) : ℂ) * (P * FourierLaplace.fourierLaplace
        (Cvs.WeilForm.SelfConvolutionTransform.cf k) z) - Cvs.Limit.ZeroFreeApproximantsRH.Xi z
      = ((2 / β : ℝ) : ℂ) * (P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
          - P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z)
        + (2 * W - Cvs.Limit.ZeroFreeApproximantsRH.Xi z) := by
    rw [hFLk, hFLh, hW]
    have : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0
    push_cast
    field_simp
    ring
  have hexp : Real.exp (|z.im| * L / 2) ≤ Real.exp (a * L / 2) :=
    Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_right hz hL0.le; linarith)
  have h1 : ‖((2 / β : ℝ) : ℂ) * (P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
          - P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z)‖
      ≤ 2 * √(Cvs.Approximant.StripApproxFromHermite.profileErr x a b (profile x)) := by
    have hb' := Cvs.Route.GroundRouteJointGap.norm_phase_mul_sub_le hL0.le hfm hhm hfs hhs z
    rw [hdiff] at hb'
    calc ‖((2 / β : ℝ) : ℂ) * (P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
            - P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z)‖
        = 2 / |β| * ‖P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
            - P * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
      _ ≤ 2 / |β| * (√Q * √L * Real.exp (a * L / 2)) := by
          refine mul_le_mul_of_nonneg_left (hb'.trans ?_) (by positivity)
          gcongr
      _ = 2 / |β| * √L * √Q * Real.exp (a * L / 2) := by ring
      _ = 2 * √(Cvs.Approximant.StripApproxFromHermite.profileErr x a b (profile x)) := by
          rw [Cvs.Approximant.StripApproxFromHermite.sqrt_combine hβ0 hL0.le]; rfl
  have h3 := Cvs.Xi.XiOffRealLine.norm_two_mul_phase_mul_sub_Xi_le hL0.le ha hz
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add h1 ?_)
  simpa [Cvs.Approximant.StripApproxFromHermite.phiMax, Cvs.Approximant.StripApproxFromHermite.windowErr] using h3

/-- The per-scale error `2√(profileErr) + windowErr` of Connes' test tends to `0` for `a < 1/2`. -/
theorem tendsto_connesErr {a : ℝ} (ha : a < 1 / 2) :
    Tendsto (fun x => 2 * √(Cvs.Approximant.StripApproxFromHermite.profileErr x a
        (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ (profile x))
      + Cvs.Approximant.StripApproxFromHermite.windowErr x a) atTop (𝓝 0) := by
  have h1 := ((Real.continuous_sqrt.tendsto 0).comp
    (Cvs.Approximant.StripApproxFromHermite.tendsto_profileErr ha (fun x => profile x)
      (fun x => (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹) (b₀ := 1 / 20) (C := 80217 / 4)
      (by norm_num)
      (by filter_upwards [eventually_ge_atTop 16] with x hx using
        Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx)
      (by filter_upwards [eventually_ge_atTop 16] with x hx using
        Cvs.Approximant.SpineNearQuarticHermite.integral_spineG_sub_sq_le_rpow hx))).const_mul 2
  have h3 := Cvs.Approximant.StripApproxFromHermite.tendsto_windowErr (a := a) (by linarith)
  have h := h1.add h3
  simp only [Function.comp_def, Real.sqrt_zero, mul_zero, add_zero] at h
  exact h

/-- **Fact 6.4 for the recentred test**: `(2/β_x)` times the recentred transform of Connes' test
converges to `Ξ` uniformly on every closed substrip `|Im z| ≤ a` with `a < 1/2`. -/
theorem tendstoUniformlyOn_connesK {a : ℝ} (ha : a < 1 / 2) :
    TendstoUniformlyOn (fun x z => ((2 / beta x : ℝ) : ℂ) * (Cvs.Finite.RecentredTransform.phase
        (Real.log x) z * FourierLaplace.fourierLaplace
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Approximant.ConnesVectorRealScale.connesK x)) z))
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop {z : ℂ | |z.im| ≤ a} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_connesErr ha).eventually (gt_mem_nhds hε), eventually_ge_atTop 16]
    with x hxε hx z hz
  rw [dist_comm, dist_eq_norm]
  exact (norm_two_div_mul_phase_connesK_sub_Xi_le hx (by linarith) hz).trans_lt hxε

/-- Connes' `k_λ`, `λ = √x`, on `ℝ_+^*`: the prolate test reflected by `u ↦ 1/u` about the centre
of `[λ⁻¹, λ]` and scaled by `x^{3/4}`. -/
def kLambda (x : ℝ) : ℝ → ℝ :=
  fun u => x ^ (3 / 4 : ℝ) * Cvs.Approximant.ConnesVectorRealScale.connesK x (Real.log x / 2 - Real.log u)

/-- Connes' transform `k̂(z) = ∫ k(u) u^{iz} d^*u`, written in the variable `u = e^t`. -/
def mellinHat (k : ℝ → ℝ) (z : ℂ) : ℂ :=
  FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf fun t => k (Real.exp t)) z

/-- **`k̂_λ` is the recentred transform of the prolate test at `−z`**, times `x^{3/4}`. -/
theorem mellinHat_kLambda (x : ℝ) (z : ℂ) :
    mellinHat (kLambda x) z = ((x ^ (3 / 4 : ℝ) : ℝ) : ℂ) * (Cvs.Finite.RecentredTransform.phase
      (Real.log x) (-z) * FourierLaplace.fourierLaplace
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Approximant.ConnesVectorRealScale.connesK x)) (-z)) := by
  unfold mellinHat FourierLaplace.fourierLaplace Cvs.Finite.RecentredTransform.phase
  set c : ℝ := Real.log x / 2 with hc
  set K := Cvs.Approximant.ConnesVectorRealScale.connesK x
  have hshift := MeasureTheory.integral_sub_left_eq_self (μ := (volume : Measure ℝ))
    (fun s : ℝ => ((x ^ (3 / 4 : ℝ) * K s : ℝ) : ℂ)
      * Complex.exp (Complex.I * z * ((c - s : ℝ) : ℂ))) c
  simp only [sub_sub_cancel] at hshift
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, kLambda, Real.log_exp]
  rw [hshift, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only []
  rw [show Complex.I * z * ((c - s : ℝ) : ℂ)
      = -(Complex.I * -z * ((Real.log x : ℝ) : ℂ) / 2) + Complex.I * -z * (s : ℂ) by
        rw [hc]; push_cast; ring,
    Complex.exp_add]
  push_cast
  ring

/-- The normalising scalar of `k̂_λ` is `overlap(2πx)/16 = (2/β_x) x^{−3/4}`. -/
theorem overlap_div_mul_rpow {x : ℝ} (hx : 16 ≤ x) :
    Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x) / 16 * x ^ (3 / 4 : ℝ) = 2 / beta x := by
  have hx0 : 0 < x := by linarith
  have hβ0 := beta_ne_zero hx
  have hb : (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ ≠ 0 := by
    intro h0; apply hβ0; unfold beta; rw [h0]; ring
  have ho : Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x) ≠ 0 := fun h => hb (by rw [h, inv_zero])
  have hr : x ^ (-(3 / 4 : ℝ)) * x ^ (3 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  unfold beta
  field_simp
  linear_combination 32 * hr

/-- **Fact 6.4 at one scale** (Connes, arXiv:2602.04022 §6.5): for `x ≥ 16` and `|Im z| ≤ a < 1`,
`(overlap(2πx)/16) k̂_λ(z)` is within `2√(profileErr) + windowErr` of `Ξ(z)`. -/
theorem norm_mellinHat_kLambda_sub_Xi_le {x a : ℝ} (hx : 16 ≤ x) (ha : a < 1) {z : ℂ}
    (hz : |z.im| ≤ a) :
    ‖((Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x) / 16 : ℝ) : ℂ) * mellinHat (kLambda x) z
        - Cvs.Limit.ZeroFreeApproximantsRH.Xi z‖
      ≤ 2 * √(Cvs.Approximant.StripApproxFromHermite.profileErr x a
            (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ (profile x))
        + Cvs.Approximant.StripApproxFromHermite.windowErr x a := by
  have hz' : |(-z).im| ≤ a := by rw [Complex.neg_im, abs_neg]; exact hz
  have h := norm_two_div_mul_phase_connesK_sub_Xi_le hx ha hz'
  rw [Cvs.Limit.MomentSpineXiCoefficients.Xi_neg] at h
  rw [mellinHat_kLambda, ← mul_assoc, ← Complex.ofReal_mul, overlap_div_mul_rpow hx]
  exact h

/-- **Fact 6.4** (Connes, arXiv:2602.04022 §6.5): `(overlap(2πx)/16) k̂_λ → Ξ` uniformly on every
closed substrip `|Im z| ≤ a`, `a < 1/2`, of the open strip `|Im z| < 1/2`. -/
theorem tendstoUniformlyOn_mellinHat_kLambda {a : ℝ} (ha : a < 1 / 2) :
    TendstoUniformlyOn (fun x z => ((Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x) / 16 : ℝ) : ℂ)
        * mellinHat (kLambda x) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop {z : ℂ | |z.im| ≤ a} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_connesErr ha).eventually (gt_mem_nhds hε), eventually_ge_atTop 16]
    with x hxε hx z hz
  rw [dist_comm, dist_eq_norm]
  exact (norm_mellinHat_kLambda_sub_Xi_le hx (by linarith) hz).trans_lt hxε

end Cvs.Approximant.FactSixFour
