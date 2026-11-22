import Mathlib
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Upstream.RiemannLebesgueNonStationary

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior weights `u²`, `x²`, `2ux` over `π²(u² − x²)²` and their `u`-averages

For `|x| ≤ ℓ < 1 ≤ u` each weight is at most `ω(u) = 2/(π²(u − ℓ)²)`, integrable on `u > 1`; the weighted
`cos(2cu)`, `sin(2cu)` averages tend to `0`, and `P(x) + Q(x) = 4ρ(x)` for `P = ∫ u²/(π²(u² − x²)²)`,
`Q = ∫ x²/(π²(u² − x²)²)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.ExteriorWeightAverages
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell)

/-- The weight `u²/(π²(u² − x²)²)`. -/
def wa (x u : ℝ) : ℝ := u ^ 2 / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)

/-- The weight `x²/(π²(u² − x²)²)`. -/
def wb (x u : ℝ) : ℝ := x ^ 2 / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)

/-- The weight `2ux/(π²(u² − x²)²)`. -/
def wd (x u : ℝ) : ℝ := 2 * u * x / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)

/-- The common majorant `ω(u) = 2/(π²(u − ℓ)²)`. -/
def om (u : ℝ) : ℝ := 2 / (π ^ 2 * (u - ell) ^ 2)

theorem ell_lt_one : ell < 1 := by
  unfold Cvs.Prolate.Hardy.ColumnWaveErrorBound.ell
  rw [div_lt_one (by positivity)]
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem den_ge {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) :
    (u - ell) ^ 2 * u ^ 2 ≤ (u ^ 2 - x ^ 2) ^ 2 := by
  have h1 := ell_lt_one
  have hxu : |x| ≤ u := by linarith
  have e : u ^ 2 - x ^ 2 = (u - |x|) * (u + |x|) := by rw [← sq_abs x]; ring
  rw [e, mul_pow]
  have a1 : (u - ell) ^ 2 ≤ (u - |x|) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have a2 : u ^ 2 ≤ (u + |x|) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg x]) 2
  exact mul_le_mul a1 a2 (by positivity) (by positivity)

theorem den_pos {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) : 0 < (u ^ 2 - x ^ 2) ^ 2 := by
  have := den_ge hx hu
  have h1 := ell_lt_one
  have : 0 < (u - ell) ^ 2 * u ^ 2 := by
    have : 0 < u - ell := by linarith
    positivity
  linarith

theorem abs_w_le {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) {p : ℝ} (hp : |p| ≤ 2 * u ^ 2) :
    |p / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)| ≤ om u := by
  have hd := den_ge hx hu
  have hdp := den_pos hx hu
  have h1 := ell_lt_one
  have hue : 0 < u - ell := by linarith
  unfold om
  rw [abs_div, abs_of_pos (show 0 < π ^ 2 * (u ^ 2 - x ^ 2) ^ 2 by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hπ : 0 < π ^ 2 := by positivity
  calc |p| * (π ^ 2 * (u - ell) ^ 2) ≤ 2 * u ^ 2 * (π ^ 2 * (u - ell) ^ 2) := by gcongr
    _ = 2 * (π ^ 2 * ((u - ell) ^ 2 * u ^ 2)) := by ring
    _ ≤ 2 * (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2) := by gcongr

theorem abs_wa_le {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) : |wa x u| ≤ om u :=
  abs_w_le hx hu (by rw [abs_of_nonneg (sq_nonneg u)]; nlinarith [sq_nonneg u])

theorem abs_wb_le {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) : |wb x u| ≤ om u := by
  refine abs_w_le hx hu ?_
  rw [abs_of_nonneg (sq_nonneg x)]
  have : x ^ 2 ≤ u ^ 2 := by
    have h1 := ell_lt_one
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) 2
  nlinarith [sq_nonneg u]

theorem abs_wd_le {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) : |wd x u| ≤ om u := by
  refine abs_w_le hx hu ?_
  have h1 := ell_lt_one
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by linarith : 0 < u)]
  nlinarith [abs_nonneg x]

theorem hasDerivAt_inv_sub {a u : ℝ} (hu : a < u) :
    HasDerivAt (fun u => -1 / (u - a)) (1 / (u - a) ^ 2) u := by
  have h1 : HasDerivAt (fun u : ℝ => u - a) 1 u := by simpa using (hasDerivAt_id u).sub_const a
  have h2 : HasDerivAt (fun u => -1 / (u - a)) ((0 * (u - a) - (-1) * 1) / (u - a) ^ 2) u :=
    (hasDerivAt_const u (-1 : ℝ)).div h1 (by linarith)
  refine h2.congr_deriv ?_
  ring

theorem tendsto_inv_sub (a : ℝ) : Tendsto (fun u : ℝ => -1 / (u - a)) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => u - a) atTop atTop := tendsto_atTop_add_const_right _ (-a) tendsto_id
  have h3 := (h.inv_tendsto_atTop).const_mul (-1)
  rw [mul_zero] at h3
  exact h3.congr fun u => by simp [div_eq_mul_inv]

theorem integrableOn_inv_sub_sq {a : ℝ} (ha : a < 1) : IntegrableOn (fun u => 1 / (u - a) ^ 2) (Ioi 1) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun u hu => hasDerivAt_inv_sub (by linarith [hu.out]))
    (fun u _ => by positivity) (tendsto_inv_sub a)

theorem integral_inv_sub_sq {a : ℝ} (ha : a < 1) : ∫ u in Ioi 1, 1 / (u - a) ^ 2 = 1 / (1 - a) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun u hu => hasDerivAt_inv_sub (by linarith [hu.out]))
    (integrableOn_inv_sub_sq ha) (tendsto_inv_sub a)]
  ring

theorem integrableOn_om : IntegrableOn om (Ioi 1) := by
  have := (integrableOn_inv_sub_sq ell_lt_one).const_mul (2 / π ^ 2)
  refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
  unfold om; field_simp

theorem continuousOn_w {x : ℝ} (hx : |x| ≤ ell) {p : ℝ → ℝ} (hp : Continuous p) :
    ContinuousOn (fun u => p u / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)) (Ioi 1) :=
  hp.continuousOn.div (by fun_prop) fun u hu => by
    have := den_pos hx (le_of_lt hu); positivity

theorem integrableOn_w {x : ℝ} (hx : |x| ≤ ell) {p : ℝ → ℝ} (hp : Continuous p) (hb : ∀ u, 1 ≤ u → |p u| ≤ 2 * u ^ 2)
    {k : ℝ → ℝ} (hk : Continuous k) (hk1 : ∀ u, |k u| ≤ 1) :
    IntegrableOn (fun u => p u / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2) * k u) (Ioi 1) := by
  refine integrableOn_om.mono' (((continuousOn_w hx hp).mul hk.continuousOn).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := abs_w_le hx (le_of_lt hu) (hb u (le_of_lt hu))
  have h2 := hk1 u
  have : 0 ≤ om u := (abs_nonneg _).trans h1
  nlinarith [abs_nonneg (p u / (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)), abs_nonneg (k u)]

theorem bound_a (u : ℝ) : |u ^ 2| ≤ 2 * u ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg u)]; nlinarith [sq_nonneg u]

theorem bound_b {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) : |x ^ 2| ≤ 2 * u ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg x)]
  have h1 := ell_lt_one
  have : x ^ 2 ≤ u ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) 2
  nlinarith [sq_nonneg u]

theorem bound_d {x u : ℝ} (hx : |x| ≤ ell) (hu : 1 ≤ u) : |2 * u * x| ≤ 2 * u ^ 2 := by
  have h1 := ell_lt_one
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by linarith : 0 < u)]
  nlinarith [abs_nonneg x]

theorem integrableOn_wa {x : ℝ} (hx : |x| ≤ ell) {k : ℝ → ℝ} (hk : Continuous k) (hk1 : ∀ u, |k u| ≤ 1) :
    IntegrableOn (fun u => wa x u * k u) (Ioi 1) :=
  integrableOn_w hx (p := fun u => u ^ 2) (by fun_prop) (fun u _ => bound_a u) hk hk1

theorem integrableOn_wb {x : ℝ} (hx : |x| ≤ ell) {k : ℝ → ℝ} (hk : Continuous k) (hk1 : ∀ u, |k u| ≤ 1) :
    IntegrableOn (fun u => wb x u * k u) (Ioi 1) :=
  integrableOn_w hx (p := fun _ => x ^ 2) (by fun_prop) (fun u hu => bound_b hx hu) hk hk1

theorem integrableOn_wd {x : ℝ} (hx : |x| ≤ ell) {k : ℝ → ℝ} (hk : Continuous k) (hk1 : ∀ u, |k u| ≤ 1) :
    IntegrableOn (fun u => wd x u * k u) (Ioi 1) :=
  integrableOn_w hx (p := fun u => 2 * u * x) (by fun_prop) (fun u hu => bound_d hx hu) hk hk1

/-- `P(x) = ∫_{u>1} u²/(π²(u² − x²)²)`. -/
def pP (x : ℝ) : ℝ := ∫ u in Ioi 1, wa x u

/-- `Q(x) = ∫_{u>1} x²/(π²(u² − x²)²)`. -/
def qQ (x : ℝ) : ℝ := ∫ u in Ioi 1, wb x u

/-- **`P + Q = 4ρ`**. -/
theorem pP_add_qQ {x : ℝ} (hx : |x| ≤ ell) : pP x + qQ x = 4 * Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x := by
  have ha := integrableOn_wa hx (k := fun _ => 1) continuous_const (fun _ => by simp)
  have hb := integrableOn_wb hx (k := fun _ => 1) continuous_const (fun _ => by simp)
  simp only [mul_one] at ha hb
  unfold pP qQ Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity
  rw [← integral_add ha hb, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have := den_pos hx (le_of_lt hu)
  unfold wa wb
  field_simp

/-- **The `u`-Riemann–Lebesgue lemma**: weighted `cos(2cu)` averages tend to `0`. -/
theorem tendsto_u_cos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 1)) :
    Tendsto (fun c : ℝ => ∫ u in Ioi 1, f u * Real.cos (2 * c * u)) atTop (𝓝 0) := by
  have h := (Cvs.Upstream.RiemannLebesgueNonStationary.tendsto_integral_mul_cos ((integrable_indicator_iff measurableSet_Ioi).2 hf)).comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  refine h.congr fun c => ?_
  simp only [Function.comp, id]
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; ext u
  by_cases hu : u ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]

/-- Weighted `sin(2cu)` averages tend to `0`. -/
theorem tendsto_u_sin {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 1)) :
    Tendsto (fun c : ℝ => ∫ u in Ioi 1, f u * Real.sin (2 * c * u)) atTop (𝓝 0) := by
  have h := (Cvs.Upstream.RiemannLebesgueNonStationary.tendsto_integral_mul_sin ((integrable_indicator_iff measurableSet_Ioi).2 hf)).comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  refine h.congr fun c => ?_
  simp only [Function.comp, id]
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; ext u
  by_cases hu : u ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]

end Cvs.Prolate.Hardy.ExteriorWeightAverages

end
