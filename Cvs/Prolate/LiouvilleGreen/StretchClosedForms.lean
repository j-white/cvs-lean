import Mathlib
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The stretch `m(t) = ½∫_{½}^t 1/a` between closed forms

With `a² = p(c²p + (σ − c²))`, `p = 1 − t² ≥ 1 − t`: where `c²p ≥ 2|σ − c²|`, `cp/√2 ≤ a ≤ √2 cp` and
`∫ dt/(1 − t)` is a logarithm; near a Bessel or Airy end the `1/√(1 − t)` and `1/√(t* − t)` primitives cost `O(1/c)`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.TopRungDepthBound (af qf af_pos af_sq)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (qf_eq stretch continuous_af)

namespace Cvs.Prolate.LiouvilleGreen.StretchClosedForms

variable {c σ : ℝ}

/-- `∫_u^v 1/(1 − t) = log((1 − u)/(1 − v))` for `u ≤ v < 1`. -/
theorem integral_inv_one_sub {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    ∫ t in u..v, 1 / (1 - t) = Real.log ((1 - u) / (1 - v)) := by
  have hd : ∀ t ∈ uIcc u v, HasDerivAt (fun t => -Real.log (1 - t)) (1 / (1 - t)) t := by
    intro t ht
    rw [uIcc_of_le huv] at ht
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have := ((hasDerivAt_id t).const_sub 1).log h1.ne'
    refine this.neg.congr_deriv ?_
    simp only [id]; field_simp
  have hc : ContinuousOn (fun t : ℝ => 1 / (1 - t)) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => 1 - t) continuousOn_const
      (continuousOn_const.sub continuousOn_id) fun t ht => (by linarith [ht.2] : (0 : ℝ) < 1 - t).ne'
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, Real.log_div (by linarith) (by linarith)]
  ring

/-- `∫_u^v 1/√(e − t) = 2√(e − u) − 2√(e − v)` for `u ≤ v < e`. -/
theorem integral_inv_sqrt_sub {u v e : ℝ} (huv : u ≤ v) (hv : v < e) :
    ∫ t in u..v, 1 / √(e - t) = 2 * √(e - u) - 2 * √(e - v) := by
  have hd : ∀ t ∈ uIcc u v, HasDerivAt (fun t => -2 * √(e - t)) (1 / √(e - t)) t := by
    intro t ht
    rw [uIcc_of_le huv] at ht
    have h1 : 0 < e - t := by linarith [ht.2]
    have h := (((hasDerivAt_id t).const_sub e).sqrt h1.ne').const_mul (-2)
    refine h.congr_deriv ?_
    have : √(e - t) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
    simp only [id]
    field_simp
  have hc : ContinuousOn (fun t : ℝ => 1 / √(e - t)) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact continuousOn_const.div (by fun_prop) fun t ht => (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- `1/a` is integrable on `[u, v]` where `0 ≤ u`, `v² < 1` and `q(v) > 0`. -/
theorem intervalIntegrable_inv_af (_hc : c ≠ 0) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) v) :
    IntervalIntegrable (fun t => 1 / af c ((c ^ 2 - σ) / c) t) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le huv]
  refine continuousOn_const.div (continuous_af c _).continuousOn fun t ht => ?_
  have hm := Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.mem_allowed (c := c) (σ := σ) hu hv hq ht
  exact (af_pos hm.1 hm.2).ne'

/-- **Additivity of the stretch**: `m(v) = m(u) + ½∫_u^v 1/a`. -/
theorem stretch_add (hc : c ≠ 0) {u v : ℝ} (hu : 1 / 2 ≤ u) (huv : u ≤ v) (hv : v ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) v) :
    stretch c σ v = stretch c σ u + 1 / 2 * ∫ t in u..v, 1 / af c ((c ^ 2 - σ) / c) t := by
  unfold stretch
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_af hc (by norm_num) hu (by nlinarith) (hq.trans_le (Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing.qf_le_qf (by linarith) huv)))
    (intervalIntegrable_inv_af hc (by linarith) huv hv hq)]
  ring

/-- **The stretch is monotone**. -/
theorem stretch_mono (hc : c ≠ 0) {u v : ℝ} (hu : 1 / 2 ≤ u) (huv : u ≤ v) (hv : v ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) v) : stretch c σ u ≤ stretch c σ v := by
  rw [stretch_add hc hu huv hv hq]
  have : 0 ≤ ∫ t in u..v, 1 / af c ((c ^ 2 - σ) / c) t :=
    intervalIntegral.integral_nonneg huv fun t _ => div_nonneg zero_le_one (Real.sqrt_nonneg _)
  linarith

/-- **Comparison on `[u, v]`**: a pointwise `1/a ≤ g` integrates. -/
theorem integral_inv_af_le {u v : ℝ} (hc : c ≠ 0) {g : ℝ → ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) v) (hg : IntervalIntegrable g volume u v)
    (hpt : ∀ t ∈ Icc u v, 1 / af c ((c ^ 2 - σ) / c) t ≤ g t) :
    ∫ t in u..v, 1 / af c ((c ^ 2 - σ) / c) t ≤ ∫ t in u..v, g t :=
  integral_mono_on huv (intervalIntegrable_inv_af hc hu huv hv hq) hg hpt

/-- **Comparison on `[u, v]`**: a pointwise `g ≤ 1/a` integrates. -/
theorem le_integral_inv_af {u v : ℝ} (hc : c ≠ 0) {g : ℝ → ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) v) (hg : IntervalIntegrable g volume u v)
    (hpt : ∀ t ∈ Icc u v, g t ≤ 1 / af c ((c ^ 2 - σ) / c) t) :
    ∫ t in u..v, g t ≤ ∫ t in u..v, 1 / af c ((c ^ 2 - σ) / c) t :=
  integral_mono_on huv hg (intervalIntegrable_inv_af hc hu huv hv hq) hpt

/-- `a² = p(c²p + (σ − c²))`. -/
theorem af_sq_eq (hc : c ≠ 0) {t : ℝ} (ht : t ^ 2 < 1) (hq : 0 < qf c ((c ^ 2 - σ) / c) t) :
    af c ((c ^ 2 - σ) / c) t ^ 2 = (1 - t ^ 2) * (c ^ 2 * (1 - t ^ 2) + (σ - c ^ 2)) := by
  rw [af_sq ht hq, qf_eq hc]; ring

/-- **The log ceiling**: if `2|σ − c²| ≤ c²(1 − t)` with `½ ≤ t < 1`, then `2m(t) ≤ (√2/c) log(1/(2(1 − t)))`. -/
theorem two_stretch_le_log (hc : 0 < c) {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1)
    (hD : 2 * |σ - c ^ 2| ≤ c ^ 2 * (1 - t)) :
    2 * stretch c σ t ≤ √2 / c * Real.log (1 / (2 * (1 - t))) := by
  set K := (c ^ 2 - σ) / c
  have hc2 : 0 < c ^ 2 := by positivity
  have hpt : ∀ r ∈ Icc (1 / 2 : ℝ) t, 1 / af c K r ≤ √2 / c * (1 / (1 - r)) := by
    intro r hr
    have hr1 : 0 < 1 - r := by linarith [hr.2]
    have hp : 1 - r ≤ 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have hD' : 2 * |σ - c ^ 2| ≤ c ^ 2 * (1 - r ^ 2) := hD.trans (by nlinarith [hr.1, hr.2])
    have hq : 0 < qf c K r := by
      rw [qf_eq hc.ne']
      have := neg_abs_le (σ - c ^ 2)
      nlinarith
    have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
    have ha := af_pos hr2 hq
    have ha2 := af_sq_eq (σ := σ) hc.ne' hr2 hq
    have hlow : c ^ 2 * (1 - r) ^ 2 / 2 ≤ af c K r ^ 2 := by
      rw [ha2]
      have := neg_abs_le (σ - c ^ 2)
      have h1 : c ^ 2 * (1 - r ^ 2) / 2 ≤ c ^ 2 * (1 - r ^ 2) + (σ - c ^ 2) := by linarith
      have h2 : (1 - r) ^ 2 ≤ (1 - r ^ 2) * (1 - r ^ 2) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    have hal : c * (1 - r) / √2 ≤ af c K r := by
      rw [div_le_iff₀ (by positivity)]
      have : (c * (1 - r)) ^ 2 ≤ (af c K r * √2) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp this
    calc 1 / af c K r ≤ 1 / (c * (1 - r) / √2) := one_div_le_one_div_of_le (by positivity) hal
      _ = √2 / c * (1 / (1 - r)) := by field_simp
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hqt : 0 < qf c K t := by
    rw [qf_eq hc.ne']
    have := neg_abs_le (σ - c ^ 2)
    have h1 : c ^ 2 * (1 - t) ≤ c ^ 2 * (1 - t ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hc2.le
    have h2 : 0 < c ^ 2 * (1 - t) := mul_pos hc2 (by linarith)
    linarith
  have hg : IntervalIntegrable (fun r => √2 / c * (1 / (1 - r))) volume (1 / 2) t := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le ht]
    exact continuousOn_const.mul (ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun r : ℝ => 1 - r) continuousOn_const
      (continuousOn_const.sub continuousOn_id) fun r hr => (by linarith [hr.2] : (0 : ℝ) < 1 - r).ne')
  have h := integral_inv_af_le hc.ne' (by norm_num) ht ht2 hqt hg hpt
  rw [intervalIntegral.integral_const_mul, integral_inv_one_sub ht ht1] at h
  unfold stretch
  have e : (1 - 1 / 2 : ℝ) / (1 - t) = 1 / (2 * (1 - t)) := by field_simp; ring
  rw [e] at h
  linarith

/-- **The log floor**: if `|σ − c²| ≤ c²(1 − t)` with `½ ≤ t < 1`, then `2m(t) ≥ (1/(2√2c)) log(1/(2(1 − t)))`. -/
theorem log_le_two_stretch (hc : 0 < c) {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1)
    (hD : |σ - c ^ 2| ≤ c ^ 2 * (1 - t)) (hq : 0 < qf c ((c ^ 2 - σ) / c) t) :
    1 / (2 * √2 * c) * Real.log (1 / (2 * (1 - t))) ≤ 2 * stretch c σ t := by
  set K := (c ^ 2 - σ) / c
  have hpt : ∀ r ∈ Icc (1 / 2 : ℝ) t, 1 / (2 * √2 * c) * (1 / (1 - r)) ≤ 1 / af c K r := by
    intro r hr
    have hr1 : 0 < 1 - r := by linarith [hr.2]
    have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
    have hqr : 0 < qf c K r := hq.trans_le (Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing.qf_le_qf (by linarith [hr.1]) hr.2)
    have ha := af_pos hr2 hqr
    have ha2 := af_sq_eq (σ := σ) hc.ne' hr2 hqr
    have hup : af c K r ^ 2 ≤ (2 * √2 * c * (1 - r)) ^ 2 := by
      rw [ha2, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      have h1 : σ - c ^ 2 ≤ c ^ 2 * (1 - r ^ 2) := (le_abs_self _).trans
        (hD.trans (mul_le_mul_of_nonneg_left (by nlinarith [hr.1, hr.2]) (sq_nonneg c)))
      have h2 : 1 - r ^ 2 ≤ 2 * (1 - r) := by nlinarith [hr.1]
      have h3 : 0 ≤ 1 - r ^ 2 := by nlinarith
      have h4 : (1 - r ^ 2) * (c ^ 2 * (1 - r ^ 2) + (σ - c ^ 2)) ≤ 2 * c ^ 2 * (1 - r ^ 2) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h1 h3]
      have h5 : (1 - r ^ 2) ^ 2 ≤ (2 * (1 - r)) ^ 2 := pow_le_pow_left₀ h3 h2 2
      nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)]
    have hau : af c K r ≤ 2 * √2 * c * (1 - r) :=
      (pow_le_pow_iff_left₀ ha.le (by positivity) two_ne_zero).mp hup
    calc 1 / (2 * √2 * c) * (1 / (1 - r)) = 1 / (2 * √2 * c * (1 - r)) := by field_simp
      _ ≤ 1 / af c K r := one_div_le_one_div_of_le ha hau
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hg : IntervalIntegrable (fun r => 1 / (2 * √2 * c) * (1 / (1 - r))) volume (1 / 2) t := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le ht]
    exact continuousOn_const.mul (ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun r : ℝ => 1 - r) continuousOn_const
      (continuousOn_const.sub continuousOn_id) fun r hr => (by linarith [hr.2] : (0 : ℝ) < 1 - r).ne')
  have h := le_integral_inv_af hc.ne' (by norm_num) ht ht2 hq hg hpt
  rw [intervalIntegral.integral_const_mul, integral_inv_one_sub ht ht1] at h
  unfold stretch
  have e : (1 - 1 / 2 : ℝ) / (1 - t) = 1 / (2 * (1 - t)) := by field_simp; ring
  rw [e] at h
  linarith

/-- **The crude floor**: for `½ ≤ t < 1`, `q(t) > 0` and `σ − c²/4 ≤ Q²c²`, `2m(t) ≥ (t − ½)/(Qc)`. -/
theorem crude_le_two_stretch (hc : 0 < c) {t Q : ℝ} (hQ : 0 < Q) (ht : 1 / 2 ≤ t) (ht1 : t < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t) (hσ : σ - c ^ 2 / 4 ≤ Q ^ 2 * c ^ 2) :
    (t - 1 / 2) / (Q * c) ≤ 2 * stretch c σ t := by
  set K := (c ^ 2 - σ) / c
  have hpt : ∀ r ∈ Icc (1 / 2 : ℝ) t, 1 / (Q * c) ≤ 1 / af c K r := by
    intro r hr
    have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
    have hqr : 0 < qf c K r := hq.trans_le (Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing.qf_le_qf (by linarith [hr.1]) hr.2)
    have ha := af_pos hr2 hqr
    apply one_div_le_one_div_of_le ha
    have : af c K r ^ 2 ≤ (Q * c) ^ 2 := by
      have hqr' := hqr
      rw [qf_eq hc.ne'] at hqr'
      rw [af_sq hr2 hqr, qf_eq hc.ne', mul_pow]
      have h0 : c ^ 2 / 4 ≤ c ^ 2 * r ^ 2 := by
        have : (1 : ℝ) / 4 ≤ r ^ 2 := by nlinarith [hr.1]
        nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg c)]
      have h1 : σ - c ^ 2 * r ^ 2 ≤ Q ^ 2 * c ^ 2 := by linarith
      have h3 : 1 - r ^ 2 ≤ 1 := by nlinarith
      have := mul_le_mul h3 h1 hqr'.le zero_le_one
      linarith
    exact (pow_le_pow_iff_left₀ ha.le (by positivity) two_ne_zero).mp this
  have ht2 : t ^ 2 < 1 := by nlinarith
  have h := le_integral_inv_af hc.ne' (by norm_num) ht ht2 hq (intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  unfold stretch
  have e : (t - 1 / 2) * (1 / (Q * c)) = (t - 1 / 2) / (Q * c) := by ring
  linarith

/-- **The Bessel-side ceiling**: for `0 < D = σ − c² ≤ c²/2` and `1 − D/c² ≤ t < 1`,
`2m(t) ≤ (1/c) log(c²/(2D)) + 2/c`. -/
theorem two_stretch_le_bessel (hc : 0 < c) (hD : c ^ 2 < σ) (hD2 : σ - c ^ 2 ≤ c ^ 2 / 2) {t : ℝ}
    (ht : 1 - (σ - c ^ 2) / c ^ 2 ≤ t) (ht1 : t < 1) :
    2 * stretch c σ t ≤ 1 / c * Real.log (c ^ 2 / (2 * (σ - c ^ 2))) + 2 / c := by
  set K := (c ^ 2 - σ) / c
  set D := σ - c ^ 2 with hDd
  have hc2 : 0 < c ^ 2 := by positivity
  have hD0 : 0 < D := by linarith
  set tm := 1 - D / c ^ 2
  have hDc : D / c ^ 2 ≤ 1 / 2 := by rw [div_le_iff₀ hc2]; linarith
  have htm : 1 / 2 ≤ tm := by simp only [tm]; linarith
  have htm1 : tm < 1 := by simp only [tm]; have := div_pos hD0 hc2; linarith
  have hqpos : ∀ r, r ^ 2 < 1 → 0 < qf c K r := fun r hr => by
    rw [qf_eq hc.ne']; nlinarith
  have ht2 : t ^ 2 < 1 := by nlinarith
  have htm2 : tm ^ 2 < 1 := by nlinarith
  have hadd := stretch_add (σ := σ) hc.ne' htm ht ht2 (hqpos t ht2)
  -- the first piece
  have hp1 : ∀ r ∈ Icc (1 / 2 : ℝ) tm, 1 / af c K r ≤ 1 / c * (1 / (1 - r)) := by
    intro r hr
    have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
    have ha := af_pos hr2 (hqpos r hr2)
    have hr1 : 0 ≤ 1 - r := by linarith [hr.2]
    have hsq : (c * (1 - r)) ^ 2 ≤ af c K r ^ 2 := by
      rw [af_sq_eq hc.ne' hr2 (hqpos r hr2)]
      have h1 : 1 - r ≤ 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
      nlinarith [mul_le_mul h1 h1 hr1 (by nlinarith), sq_nonneg c]
    have hca : c * (1 - r) ≤ af c K r :=
      (pow_le_pow_iff_left₀ (by positivity) ha.le two_ne_zero).mp hsq
    have hr1' : 0 < 1 - r := by linarith [hr.2]
    calc 1 / af c K r ≤ 1 / (c * (1 - r)) := one_div_le_one_div_of_le (by positivity) hca
      _ = 1 / c * (1 / (1 - r)) := by rw [one_div_mul_one_div]
  have hg1 : IntervalIntegrable (fun r => 1 / c * (1 / (1 - r))) volume (1 / 2) tm := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le htm]
    exact continuousOn_const.mul (ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun r : ℝ => 1 - r) continuousOn_const
      (continuousOn_const.sub continuousOn_id) fun r hr => (by linarith [hr.2] : (0 : ℝ) < 1 - r).ne')
  have h1 := integral_inv_af_le hc.ne' (by norm_num) htm htm2 (hqpos tm htm2) hg1 hp1
  rw [intervalIntegral.integral_const_mul, integral_inv_one_sub htm htm1] at h1
  have e1 : (1 - 1 / 2 : ℝ) / (1 - tm) = c ^ 2 / (2 * D) := by
    rw [show (1 : ℝ) - tm = D / c ^ 2 by simp only [tm]; ring]
    have := hD0.ne'
    field_simp
    ring
  rw [e1] at h1
  -- the second piece
  have hp2 : ∀ r ∈ Icc tm t, 1 / af c K r ≤ 1 / √D * (1 / √(1 - r)) := by
    intro r hr
    have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
    have hr1 : 0 < 1 - r := by linarith [hr.2]
    have ha := af_pos hr2 (hqpos r hr2)
    rw [one_div_mul_one_div, ← Real.sqrt_mul hD0.le]
    apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
    rw [show af c K r = √(af c K r ^ 2) by rw [Real.sqrt_sq ha.le]]
    apply Real.sqrt_le_sqrt
    rw [af_sq_eq hc.ne' hr2 (hqpos r hr2)]
    have h1 : 1 - r ≤ 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have h0 : 0 ≤ c ^ 2 * (1 - r ^ 2) := by have : 0 ≤ 1 - r ^ 2 := by linarith
                                            positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hD0.le]
  have hg2 : IntervalIntegrable (fun r => 1 / √D * (1 / √(1 - r))) volume tm t := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le ht]
    exact continuousOn_const.mul (continuousOn_const.div (by fun_prop)
      fun r hr => (Real.sqrt_pos.mpr (by linarith [hr.2])).ne')
  have h2 := integral_inv_af_le hc.ne' (by linarith) ht ht2 (hqpos t ht2) hg2 hp2
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub ht ht1] at h2
  have h3 : 1 / √D * (2 * √(1 - tm) - 2 * √(1 - t)) ≤ 2 / c := by
    have e : √(1 - tm) = √D / c := by
      simp only [tm]; rw [show (1 : ℝ) - (1 - D / c ^ 2) = D / c ^ 2 by ring, Real.sqrt_div' _ hc2.le,
        Real.sqrt_sq hc.le]
    rw [e]
    have : 0 ≤ √(1 - t) := Real.sqrt_nonneg _
    have hsD : 0 < √D := Real.sqrt_pos.mpr hD0
    calc 1 / √D * (2 * (√D / c) - 2 * √(1 - t)) ≤ 1 / √D * (2 * (√D / c)) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 / c := by field_simp
  unfold stretch at hadd ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The Airy-side ceiling**: for `p* = (c² − σ)/c² ∈ (0, 3/8]` and `√(1 − 2p*) ≤ t`, `t² < 1 − p*`,
`2m(t) ≤ (√2/c) log(1/(2p*)) + 2/c`. -/
theorem two_stretch_le_airy (hc : 0 < c) (hσ : σ < c ^ 2) (hp4 : (c ^ 2 - σ) / c ^ 2 ≤ 3 / 8) {t : ℝ}
    (ht : √(1 - 2 * ((c ^ 2 - σ) / c ^ 2)) ≤ t) (htq : t ^ 2 < 1 - (c ^ 2 - σ) / c ^ 2) :
    2 * stretch c σ t ≤ √2 / c * Real.log (1 / (2 * ((c ^ 2 - σ) / c ^ 2))) + 2 / c := by
  set K := (c ^ 2 - σ) / c
  set ps := (c ^ 2 - σ) / c ^ 2 with hps
  have hc2 : 0 < c ^ 2 := by positivity
  have hps0 : 0 < ps := div_pos (by linarith) hc2
  have hσps : σ = c ^ 2 * (1 - ps) := by rw [hps]; field_simp; ring
  set ts := √(1 - 2 * ps)
  have hts2 : ts ^ 2 = 1 - 2 * ps := Real.sq_sqrt (by linarith)
  have hts : 1 / 2 ≤ ts := by
    have : (1 / 2 : ℝ) ^ 2 ≤ ts ^ 2 := by rw [hts2]; linarith
    nlinarith [Real.sqrt_nonneg (1 - 2 * ps)]
  have hts1 : ts < 1 := by nlinarith [Real.sqrt_nonneg (1 - 2 * ps)]
  set te := √(1 - ps)
  have hte2 : te ^ 2 = 1 - ps := Real.sq_sqrt (by linarith)
  have hte0 : 0 ≤ te := Real.sqrt_nonneg _
  have htte : t < te := by nlinarith
  have hqpos : ∀ r, 0 ≤ r → r ^ 2 < 1 - ps → 0 < qf c K r := fun r _ hr => by
    rw [qf_eq hc.ne', hσps]; nlinarith
  have ht0 : 0 ≤ t := by linarith
  have ht2 : t ^ 2 < 1 := by linarith
  have hts2' : ts ^ 2 < 1 - ps := by rw [hts2]; linarith
  have hadd := stretch_add (σ := σ) hc.ne' hts ht ht2 (hqpos t ht0 htq)
  -- the first piece
  have hp1 : ∀ r ∈ Icc (1 / 2 : ℝ) ts, 1 / af c K r ≤ √2 / c * (1 / (1 - r)) := by
    intro r hr
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have hrq : r ^ 2 < 1 - ps := by nlinarith [hr.2]
    have hr2 : r ^ 2 < 1 := by linarith
    have hr1 : 0 < 1 - r := by linarith [hr.2]
    have ha := af_pos hr2 (hqpos r hr0 hrq)
    have hlow : c ^ 2 * (1 - r) ^ 2 / 2 ≤ af c K r ^ 2 := by
      rw [af_sq_eq hc.ne' hr2 (hqpos r hr0 hrq), hσps]
      have hp : 2 * ps ≤ 1 - r ^ 2 := by nlinarith [hr.2]
      have h1 : 1 - r ≤ 1 - r ^ 2 := by nlinarith [hr.1]
      have e : c ^ 2 * (1 - r ^ 2) + (c ^ 2 * (1 - ps) - c ^ 2) = c ^ 2 * (1 - r ^ 2 - ps) := by ring
      rw [e]
      have h2 : (1 - r ^ 2) / 2 ≤ 1 - r ^ 2 - ps := by linarith
      have h3 : 0 ≤ 1 - r ^ 2 := by linarith
      have h4 : (0 : ℝ) ≤ c ^ 2 * (1 - r ^ 2) := by positivity
      nlinarith [mul_le_mul h1 h1 hr1.le h3, mul_le_mul_of_nonneg_left h2 h4]
    have hal : c * (1 - r) / √2 ≤ af c K r := by
      rw [div_le_iff₀ (by positivity)]
      have : (c * (1 - r)) ^ 2 ≤ (af c K r * √2) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp this
    calc 1 / af c K r ≤ 1 / (c * (1 - r) / √2) := one_div_le_one_div_of_le (by positivity) hal
      _ = √2 / c * (1 / (1 - r)) := by field_simp
  have hg1 : IntervalIntegrable (fun r => √2 / c * (1 / (1 - r))) volume (1 / 2) ts := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hts]
    exact continuousOn_const.mul (ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun r : ℝ => 1 - r) continuousOn_const
      (continuousOn_const.sub continuousOn_id) fun r hr => (by linarith [hr.2] : (0 : ℝ) < 1 - r).ne')
  have h1 := integral_inv_af_le hc.ne' (by norm_num) hts (by linarith) (hqpos ts (by linarith) hts2') hg1 hp1
  rw [intervalIntegral.integral_const_mul, integral_inv_one_sub hts hts1] at h1
  have h1' : Real.log ((1 - 1 / 2) / (1 - ts)) ≤ Real.log (1 / (2 * ps)) := by
    apply Real.log_le_log (by apply div_pos (by norm_num); linarith)
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have : 2 * ps ≤ 2 * (1 - ts) := by nlinarith
    linarith
  -- the second piece
  have hp2 : ∀ r ∈ Icc ts t, 1 / af c K r ≤ 1 / (c * √ps) * (1 / √(te - r)) := by
    intro r hr
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have hrq : r ^ 2 < 1 - ps := by nlinarith [hr.2]
    have hr2 : r ^ 2 < 1 := by linarith
    have hrt : 0 < te - r := by nlinarith [hr.2]
    have ha := af_pos hr2 (hqpos r hr0 hrq)
    rw [one_div_mul_one_div, mul_assoc, ← Real.sqrt_mul hps0.le]
    apply one_div_le_one_div_of_le (by positivity)
    have hca : c * √(ps * (te - r)) = √(c ^ 2 * (ps * (te - r))) := by
      rw [Real.sqrt_mul hc2.le, Real.sqrt_sq hc.le]
    rw [hca, show af c K r = √(af c K r ^ 2) by rw [Real.sqrt_sq ha.le]]
    apply Real.sqrt_le_sqrt
    rw [af_sq_eq hc.ne' hr2 (hqpos r hr0 hrq), hσps]
    have e : c ^ 2 * (1 - r ^ 2) + (c ^ 2 * (1 - ps) - c ^ 2) = c ^ 2 * (te ^ 2 - r ^ 2) := by rw [hte2]; ring
    rw [e]
    have h1 : te - r ≤ te ^ 2 - r ^ 2 := by nlinarith [hr.1]
    have h2 : ps ≤ 1 - r ^ 2 := by linarith
    have h3 : 0 ≤ te - r := hrt.le
    nlinarith [mul_le_mul h2 h1 h3 (by linarith), sq_nonneg c]
  have hg2 : IntervalIntegrable (fun r => 1 / (c * √ps) * (1 / √(te - r))) volume ts t := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le ht]
    exact continuousOn_const.mul (continuousOn_const.div (by fun_prop)
      fun r hr => (Real.sqrt_pos.mpr (by nlinarith [hr.2])).ne')
  have h2 := integral_inv_af_le hc.ne' (by linarith) ht ht2 (hqpos t ht0 htq) hg2 hp2
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub ht htte] at h2
  have h3 : 1 / (c * √ps) * (2 * √(te - ts) - 2 * √(te - t)) ≤ 2 / c := by
    have hd : te - ts ≤ ps := by
      have : te ^ 2 - ts ^ 2 = ps := by rw [hte2, hts2]; ring
      nlinarith [Real.sqrt_nonneg (1 - 2 * ps)]
    have hsq : √(te - ts) ≤ √ps := Real.sqrt_le_sqrt hd
    have : 0 ≤ √(te - t) := Real.sqrt_nonneg _
    have hsp : 0 < √ps := Real.sqrt_pos.mpr hps0
    calc 1 / (c * √ps) * (2 * √(te - ts) - 2 * √(te - t)) ≤ 1 / (c * √ps) * (2 * √ps) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 / c := by field_simp
  unfold stretch at hadd ⊢
  have hlog := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ √2 / c)
  linarith

end Cvs.Prolate.LiouvilleGreen.StretchClosedForms

end
