import Mathlib
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.ColumnWaveSquareIntegral
import Cvs.Prolate.Hardy.ExteriorWeightAverages

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `u`-oscillating part of `G_c` integrates to `o(1)`

The averages `∫ wa cos 2cu`, `∫ wb cos 2cu`, `∫ wd sin 2cu` are measurable in `x`, bounded by `∫ω` on `|x| ≤ ℓ`,
and tend to `0` pointwise; with `|X|, |Y| ≤ 3` and `X = Y = 0` off `[−ℓ, ℓ]`, dominated convergence gives
`∫ (−X²∫wa cos 2cu + Y²∫wb cos 2cu − XY∫wd sin 2cu)/2 dx → 0`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.OscillatingPartVanishes
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell)
open Cvs.Prolate.Hardy.ExteriorWeightAverages (wa wb wd om pP qQ)
open Cvs.Prolate.Hardy.ColumnWaveSquareIntegral (xX yY iA iB iD gG)

theorem measurable_w (k : ℝ → ℝ) (hk : Continuous k) {p : ℝ × ℝ → ℝ} (hp : Measurable p) :
    Measurable fun q : ℝ × ℝ => p q / (π ^ 2 * (q.2 ^ 2 - q.1 ^ 2) ^ 2) * k q.2 :=
  by
    have hk' : Measurable fun q : ℝ × ℝ => k q.2 := hk.measurable.comp measurable_snd
    have hd : Measurable fun q : ℝ × ℝ => π ^ 2 * (q.2 ^ 2 - q.1 ^ 2) ^ 2 := by fun_prop
    exact Measurable.mul (Measurable.div hp hd) hk'

theorem sm_int {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable fun x => ∫ u in Ioi 1, f (x, u) :=
  hf.stronglyMeasurable.integral_prod_right'

theorem sm_iA (c : ℝ) : StronglyMeasurable (iA c) :=
  sm_int (f := fun q => wa q.1 q.2 * Real.cos (2 * c * q.2))
    (measurable_w (fun u => Real.cos (2 * c * u)) (by fun_prop) (p := fun q => q.2 ^ 2) (by fun_prop))

theorem sm_iB (c : ℝ) : StronglyMeasurable (iB c) :=
  sm_int (f := fun q => wb q.1 q.2 * Real.cos (2 * c * q.2))
    (measurable_w (fun u => Real.cos (2 * c * u)) (by fun_prop) (p := fun q => q.1 ^ 2) (by fun_prop))

theorem sm_iD (c : ℝ) : StronglyMeasurable (iD c) :=
  sm_int (f := fun q => wd q.1 q.2 * Real.sin (2 * c * q.2))
    (measurable_w (fun u => Real.sin (2 * c * u)) (by fun_prop) (p := fun q => 2 * q.2 * q.1) (by fun_prop))

theorem sm_pP : StronglyMeasurable pP := by
  have := sm_int (f := fun q => wa q.1 q.2 * (fun _ => (1 : ℝ)) q.2)
    (measurable_w (fun _ => (1 : ℝ)) continuous_const (p := fun q => q.2 ^ 2) (by fun_prop))
  simp only [mul_one] at this
  exact this

theorem sm_qQ : StronglyMeasurable qQ := by
  have := sm_int (f := fun q => wb q.1 q.2 * (fun _ => (1 : ℝ)) q.2)
    (measurable_w (fun _ => (1 : ℝ)) continuous_const (p := fun q => q.1 ^ 2) (by fun_prop))
  simp only [mul_one] at this
  exact this

/-- `∫_{u>1} ω`. -/
def iOm : ℝ := ∫ u in Ioi 1, om u

theorem abs_int_le {x : ℝ} {w : ℝ → ℝ → ℝ} (hw : ∀ u, 1 ≤ u → |w x u| ≤ om u) {k : ℝ → ℝ}
    (hk : ∀ u, |k u| ≤ 1) : |∫ u in Ioi 1, w x u * k u| ≤ iOm := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_om ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hw u (le_of_lt hu)
  have h2 := hk u
  have : 0 ≤ om u := (abs_nonneg _).trans h1
  nlinarith [abs_nonneg (w x u), abs_nonneg (k u)]

theorem abs_iA_le (c : ℝ) {x : ℝ} (hx : |x| ≤ ell) : |iA c x| ≤ iOm :=
  abs_int_le (w := wa) (fun _ hu => Cvs.Prolate.Hardy.ExteriorWeightAverages.abs_wa_le hx hu) (fun _ => abs_cos_le_one _)

theorem abs_iB_le (c : ℝ) {x : ℝ} (hx : |x| ≤ ell) : |iB c x| ≤ iOm :=
  abs_int_le (w := wb) (fun _ hu => Cvs.Prolate.Hardy.ExteriorWeightAverages.abs_wb_le hx hu) (fun _ => abs_cos_le_one _)

theorem abs_iD_le (c : ℝ) {x : ℝ} (hx : |x| ≤ ell) : |iD c x| ≤ iOm :=
  abs_int_le (w := wd) (fun _ hu => Cvs.Prolate.Hardy.ExteriorWeightAverages.abs_wd_le hx hu) (fun _ => abs_sin_le_one _)

theorem abs_pP_le {x : ℝ} (hx : |x| ≤ ell) : |pP x| ≤ iOm := by
  have := abs_int_le (w := wa) (fun _ hu => Cvs.Prolate.Hardy.ExteriorWeightAverages.abs_wa_le hx hu) (k := fun _ => 1) (fun _ => by simp)
  simpa [pP] using this

theorem abs_qQ_le {x : ℝ} (hx : |x| ≤ ell) : |qQ x| ≤ iOm := by
  have := abs_int_le (w := wb) (fun _ hu => Cvs.Prolate.Hardy.ExteriorWeightAverages.abs_wb_le hx hu) (k := fun _ => 1) (fun _ => by simp)
  simpa [qQ] using this

theorem tendsto_iA {x : ℝ} (hx : |x| ≤ ell) : Tendsto (fun c => iA c x) atTop (𝓝 0) := by
  have h := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wa hx (k := fun _ => 1) continuous_const (fun _ => by simp)
  simp only [mul_one] at h
  exact Cvs.Prolate.Hardy.ExteriorWeightAverages.tendsto_u_cos h

theorem tendsto_iB {x : ℝ} (hx : |x| ≤ ell) : Tendsto (fun c => iB c x) atTop (𝓝 0) := by
  have h := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wb hx (k := fun _ => 1) continuous_const (fun _ => by simp)
  simp only [mul_one] at h
  exact Cvs.Prolate.Hardy.ExteriorWeightAverages.tendsto_u_cos h

theorem tendsto_iD {x : ℝ} (hx : |x| ≤ ell) : Tendsto (fun c => iD c x) atTop (𝓝 0) := by
  have h := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wd hx (k := fun _ => 1) continuous_const (fun _ => by simp)
  simp only [mul_one] at h
  exact Cvs.Prolate.Hardy.ExteriorWeightAverages.tendsto_u_sin h

/-- The `u`-oscillating part of `G_c`. -/
def errF (c x : ℝ) : ℝ := (-(xX c x ^ 2) * iA c x + yY c x ^ 2 * iB c x - xX c x * yY c x * iD c x) / 2

/-- The `u`-averaged part of `G_c`. -/
def mainF (c x : ℝ) : ℝ := (xX c x ^ 2 * pP x + yY c x ^ 2 * qQ x) / 2

theorem abs_errF_le (c x : ℝ) :
    |errF c x| ≤ 27 / 2 * iOm * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) x := by
  rcases le_or_gt (|x|) ell with hx | hx
  · rw [indicator_of_mem (show x ∈ Icc (-ell) ell from abs_le.1 hx), mul_one]
    have hX := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.abs_xX_le c x
    have hY := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.abs_yY_le c x
    have h1 := abs_iA_le c hx
    have h2 := abs_iB_le c hx
    have h3 := abs_iD_le c hx
    have hX2 : xX c x ^ 2 ≤ 9 := by nlinarith [sq_abs (xX c x), abs_nonneg (xX c x)]
    have hY2 : yY c x ^ 2 ≤ 9 := by nlinarith [sq_abs (yY c x), abs_nonneg (yY c x)]
    have hXY : |xX c x * yY c x| ≤ 9 := by
      rw [abs_mul]; nlinarith [abs_nonneg (xX c x), abs_nonneg (yY c x)]
    unfold errF
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have t1 : |-(xX c x ^ 2) * iA c x| ≤ 9 * iOm := by
      rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith [abs_nonneg (iA c x), sq_nonneg (xX c x)]
    have t2 : |yY c x ^ 2 * iB c x| ≤ 9 * iOm := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]; nlinarith [abs_nonneg (iB c x), sq_nonneg (yY c x)]
    have t3 : |xX c x * yY c x * iD c x| ≤ 9 * iOm := by
      rw [abs_mul]; nlinarith [abs_nonneg (iD c x), abs_nonneg (xX c x * yY c x)]
    have := abs_sub (-(xX c x ^ 2) * iA c x + yY c x ^ 2 * iB c x) (xX c x * yY c x * iD c x)
    have := abs_add_le (-(xX c x ^ 2) * iA c x) (yY c x ^ 2 * iB c x)
    linarith
  · have hnot : x ∉ Icc (-ell) ell := fun h => by have := abs_le.2 h; linarith
    rw [indicator_of_notMem hnot, mul_zero]
    unfold errF
    rw [Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.xX_zero hx, Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.yY_zero hx]
    simp

theorem tendsto_errF (x : ℝ) : Tendsto (fun c => errF c x) atTop (𝓝 0) := by
  rcases le_or_gt (|x|) ell with hx | hx
  · have hb : ∀ c, |errF c x| ≤ 9 / 2 * (|iA c x| + |iB c x| + |iD c x|) := by
      intro c
      have hX := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.abs_xX_le c x
      have hY := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.abs_yY_le c x
      have hX2 : xX c x ^ 2 ≤ 9 := by nlinarith [sq_abs (xX c x), abs_nonneg (xX c x)]
      have hY2 : yY c x ^ 2 ≤ 9 := by nlinarith [sq_abs (yY c x), abs_nonneg (yY c x)]
      have hXY : |xX c x * yY c x| ≤ 9 := by
        rw [abs_mul]; nlinarith [abs_nonneg (xX c x), abs_nonneg (yY c x)]
      unfold errF
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have t1 : |-(xX c x ^ 2) * iA c x| ≤ 9 * |iA c x| := by
        rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith [abs_nonneg (iA c x)]
      have t2 : |yY c x ^ 2 * iB c x| ≤ 9 * |iB c x| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]; nlinarith [abs_nonneg (iB c x)]
      have t3 : |xX c x * yY c x * iD c x| ≤ 9 * |iD c x| := by
        rw [abs_mul]; nlinarith [abs_nonneg (iD c x)]
      have := abs_sub (-(xX c x ^ 2) * iA c x + yY c x ^ 2 * iB c x) (xX c x * yY c x * iD c x)
      have := abs_add_le (-(xX c x ^ 2) * iA c x) (yY c x ^ 2 * iB c x)
      linarith
    have hlim : Tendsto (fun c => 9 / 2 * (|iA c x| + |iB c x| + |iD c x|)) atTop (𝓝 0) := by
      have := (((tendsto_iA hx).abs.add (tendsto_iB hx).abs).add (tendsto_iD hx).abs).const_mul (9 / 2)
      simpa using this
    exact squeeze_zero_norm (fun c => by rw [Real.norm_eq_abs]; exact hb c) hlim
  · have : ∀ c, errF c x = 0 := fun c => by
      unfold errF; rw [Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.xX_zero hx, Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.yY_zero hx]; simp
    simp [this]

/-- **The `u`-oscillation integrates to `o(1)`**: `∫ errF_c → 0`. -/
theorem tendsto_integral_errF : Tendsto (fun c => ∫ x, errF c x) atTop (𝓝 0) := by
  have hbound : Integrable (fun x => 27 / 2 * iOm * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) x) :=
    ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := (1 : ℝ)) (s := Icc (-ell) ell) (μ := volume) measure_Icc_lt_top.ne)).const_mul _
  have h := tendsto_integral_filter_of_dominated_convergence (l := atTop) (F := errF) (f := fun _ => (0 : ℝ))
    (fun x => 27 / 2 * iOm * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) x)
    (Filter.Eventually.of_forall fun c => by
      unfold errF
      have hX := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.measurable_xX c
      have hY := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.measurable_yY c
      exact (((((hX.pow_const 2).neg.mul (sm_iA c).measurable).add
        ((hY.pow_const 2).mul (sm_iB c).measurable)).sub
          ((hX.mul hY).mul (sm_iD c).measurable)).div_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_errF_le c x)
    hbound (Filter.Eventually.of_forall tendsto_errF)
  simpa using h

end Cvs.Prolate.Hardy.OscillatingPartVanishes

end
