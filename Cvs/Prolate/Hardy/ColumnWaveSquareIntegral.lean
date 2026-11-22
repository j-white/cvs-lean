import Mathlib
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorWeightAverages
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Prolate.Hardy.TwoCarrierWaveExplicit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior-column integral of `V_u²` as one `x`-integral

`V_u = (u sin(cu)X − x cos(cu)Y)/(π(u² − x²))` with `X, Y` the cosine and sine carriers on `I` and the lips; so
`∫_{u>1} V_u² = (X²P + Y²Q)/2 + (−X²∫wa cos 2cu + Y²∫wb cos 2cu − XY∫wd sin 2cu)/2`, and by Fubini
`∫_{u>1}‖V_u‖² = ∫ G_c(x) dx`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.ColumnWaveSquareIntegral
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.CarrierBoundaryValues (sR)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (waveV)
open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell)
open Cvs.Prolate.Hardy.TwoCarrierWaveExplicit (colWave vfun)
open Cvs.Prolate.Hardy.ExteriorWeightAverages (wa wb wd om pP qQ)

/-- The cosine carrier `X_c`. -/
def xX (c x : ℝ) : ℝ := cI.indicator (fun x => Real.cos (c * x)) x +
  (symS (1 / 2) ell).indicator (fun x => Real.cos (c * x) - Real.cos (c * (x - sR x))) x

/-- The sine carrier `Y_c`. -/
def yY (c x : ℝ) : ℝ := cI.indicator (fun x => Real.sin (c * x)) x +
  (symS (1 / 2) ell).indicator (fun x => Real.sin (c * x) - Real.sin (c * (x - sR x))) x

theorem vfun_eq (c u x : ℝ) :
    vfun c u x = (u * Real.sin (c * u) * xX c x - x * Real.cos (c * u) * yY c x) / (π * (u ^ 2 - x ^ 2)) := by
  unfold vfun xX yY colWave
  by_cases h1 : x ∈ cI <;> by_cases h2 : x ∈ symS (1 / 2) ell <;>
    simp only [indicator_of_mem, indicator_of_notMem, h1, h2, not_false_eq_true] <;> ring

theorem symS_subset {x : ℝ} (hx : x ∈ symS (1 / 2) ell) : |x| ≤ ell := by
  rcases hx with h | h
  · rw [abs_of_pos (by linarith [h.1])]; exact h.2
  · rw [abs_of_neg (by linarith [h.2])]; linarith [h.1]

theorem cI_subset {x : ℝ} (hx : x ∈ cI) : |x| ≤ ell := by
  have := Cvs.Prolate.Hardy.ColumnWaveErrorBound.half_lt_ell
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

theorem xX_zero {c x : ℝ} (hx : ell < |x|) : xX c x = 0 := by
  have h1 : x ∉ cI := fun h => by linarith [cI_subset h]
  have h2 : x ∉ symS (1 / 2) ell := fun h => by linarith [symS_subset h]
  rw [xX, indicator_of_notMem h1, indicator_of_notMem h2, add_zero]

theorem yY_zero {c x : ℝ} (hx : ell < |x|) : yY c x = 0 := by
  have h1 : x ∉ cI := fun h => by linarith [cI_subset h]
  have h2 : x ∉ symS (1 / 2) ell := fun h => by linarith [symS_subset h]
  rw [yY, indicator_of_notMem h1, indicator_of_notMem h2, add_zero]

theorem abs_ind_le {s : Set ℝ} {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) (x : ℝ) :
    |s.indicator f x| ≤ B := by
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]; exact hf x
  · rw [indicator_of_notMem h, abs_zero]; exact hB

theorem abs_xX_le (c x : ℝ) : |xX c x| ≤ 3 := by
  unfold xX
  have hb : ∀ y, |Real.cos (c * y) - Real.cos (c * (y - sR y))| ≤ 2 := fun y => by
    have e1 := abs_cos_le_one (c * y)
    have e2 := abs_cos_le_one (c * (y - sR y))
    have e3 := abs_sub (Real.cos (c * y)) (Real.cos (c * (y - sR y)))
    linarith
  have h1 := abs_ind_le (s := cI) (f := fun x => Real.cos (c * x)) zero_le_one (fun x => abs_cos_le_one _) x
  have h2 := abs_ind_le (s := symS (1 / 2) ell) (f := fun x => Real.cos (c * x) - Real.cos (c * (x - sR x)))
    (B := 2) (by norm_num) hb x
  have h3 := abs_add_le (cI.indicator (fun x => Real.cos (c * x)) x)
    ((symS (1 / 2) ell).indicator (fun x => Real.cos (c * x) - Real.cos (c * (x - sR x))) x)
  linarith

theorem abs_yY_le (c x : ℝ) : |yY c x| ≤ 3 := by
  unfold yY
  have hb : ∀ y, |Real.sin (c * y) - Real.sin (c * (y - sR y))| ≤ 2 := fun y => by
    have e1 := abs_sin_le_one (c * y)
    have e2 := abs_sin_le_one (c * (y - sR y))
    have e3 := abs_sub (Real.sin (c * y)) (Real.sin (c * (y - sR y)))
    linarith
  have h1 := abs_ind_le (s := cI) (f := fun x => Real.sin (c * x)) zero_le_one (fun x => abs_sin_le_one _) x
  have h2 := abs_ind_le (s := symS (1 / 2) ell) (f := fun x => Real.sin (c * x) - Real.sin (c * (x - sR x)))
    (B := 2) (by norm_num) hb x
  have h3 := abs_add_le (cI.indicator (fun x => Real.sin (c * x)) x)
    ((symS (1 / 2) ell).indicator (fun x => Real.sin (c * x) - Real.sin (c * (x - sR x))) x)
  linarith

theorem measurable_xX (c : ℝ) : Measurable (xX c) := by
  have hs := Cvs.Prolate.Hardy.CarrierBoundaryValues.continuous_sR
  unfold xX
  refine Measurable.add ?_ ?_
  · exact (Continuous.measurable (by fun_prop)).indicator measurableSet_Icc
  · exact (Continuous.measurable (by fun_prop)).indicator (Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _)

theorem measurable_yY (c : ℝ) : Measurable (yY c) := by
  have hs := Cvs.Prolate.Hardy.CarrierBoundaryValues.continuous_sR
  unfold yY
  refine Measurable.add ?_ ?_
  · exact (Continuous.measurable (by fun_prop)).indicator measurableSet_Icc
  · exact (Continuous.measurable (by fun_prop)).indicator (Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _)

/-- The square of `V_u` in the three weights. -/
theorem vfun_sq (c u x : ℝ) :
    vfun c u x ^ 2 = wa x u * Real.sin (c * u) ^ 2 * xX c x ^ 2 + wb x u * Real.cos (c * u) ^ 2 * yY c x ^ 2 -
      wd x u * (Real.sin (c * u) * Real.cos (c * u)) * (xX c x * yY c x) := by
  rw [vfun_eq]
  unfold wa wb wd
  by_cases h : u ^ 2 - x ^ 2 = 0
  · simp [h]
  · field_simp
    ring

/-- The doubled-angle form of `V_u²`. -/
theorem vfun_sq' (c u x : ℝ) :
    vfun c u x ^ 2 = (xX c x ^ 2 * wa x u + yY c x ^ 2 * wb x u) / 2 +
      (-(xX c x ^ 2) * (wa x u * Real.cos (2 * c * u)) + yY c x ^ 2 * (wb x u * Real.cos (2 * c * u)) -
        xX c x * yY c x * (wd x u * Real.sin (2 * c * u))) / 2 := by
  rw [vfun_sq]
  have hs : Real.sin (c * u) ^ 2 = (1 - Real.cos (2 * c * u)) / 2 := by
    rw [show 2 * c * u = 2 * (c * u) by ring, Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (c * u)]; ring
  have hc : Real.cos (c * u) ^ 2 = (1 + Real.cos (2 * c * u)) / 2 := by
    rw [show 2 * c * u = 2 * (c * u) by ring, Real.cos_two_mul]; ring
  have hsc : Real.sin (c * u) * Real.cos (c * u) = Real.sin (2 * c * u) / 2 := by
    rw [show 2 * c * u = 2 * (c * u) by ring, Real.sin_two_mul]; ring
  rw [hs, hc, hsc]
  ring

/-- The `u`-averages `∫ wa cos(2cu)`, `∫ wb cos(2cu)`, `∫ wd sin(2cu)`. -/
def iA (c x : ℝ) : ℝ := ∫ u in Ioi 1, wa x u * Real.cos (2 * c * u)
def iB (c x : ℝ) : ℝ := ∫ u in Ioi 1, wb x u * Real.cos (2 * c * u)
def iD (c x : ℝ) : ℝ := ∫ u in Ioi 1, wd x u * Real.sin (2 * c * u)

/-- The inner `u`-integral `G_c(x)`. -/
def gG (c x : ℝ) : ℝ := (xX c x ^ 2 * pP x + yY c x ^ 2 * qQ x) / 2 +
  (-(xX c x ^ 2) * iA c x + yY c x ^ 2 * iB c x - xX c x * yY c x * iD c x) / 2

/-- **The inner integral** `∫_{u>1} V_u(x)² du = G_c(x)`. -/
theorem integral_vfun_sq (c x : ℝ) : ∫ u in Ioi 1, vfun c u x ^ 2 = gG c x := by
  rcases le_or_gt (|x|) ell with hx | hx
  · have i1 := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wa hx (k := fun _ => 1) continuous_const (fun _ => by simp)
    have i2 := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wb hx (k := fun _ => 1) continuous_const (fun _ => by simp)
    simp only [mul_one] at i1 i2
    have i3 := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wa hx (k := fun u => Real.cos (2 * c * u)) (by fun_prop)
      (fun _ => abs_cos_le_one _)
    have i4 := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wb hx (k := fun u => Real.cos (2 * c * u)) (by fun_prop)
      (fun _ => abs_cos_le_one _)
    have i5 := Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_wd hx (k := fun u => Real.sin (2 * c * u)) (by fun_prop)
      (fun _ => abs_sin_le_one _)
    simp_rw [vfun_sq']
    rw [integral_add, integral_div, integral_div, integral_add, integral_const_mul, integral_const_mul,
      integral_sub, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
    · unfold gG pP qQ iA iB iD; ring
    · exact i3.const_mul _
    · exact i4.const_mul _
    · exact (i3.const_mul _).add (i4.const_mul _)
    · exact i5.const_mul _
    · exact i1.const_mul _
    · exact i2.const_mul _
    · exact ((i1.const_mul _).add (i2.const_mul _)).div_const _
    · exact (((i3.const_mul _).add (i4.const_mul _)).sub (i5.const_mul _)).div_const _
  · have hv : ∀ u, vfun c u x = 0 := fun u => by rw [vfun_eq, xX_zero hx, yY_zero hx]; simp
    simp [hv, gG, xX_zero hx, yY_zero hx]

theorem measurable_vfun (c : ℝ) : Measurable (fun p : ℝ × ℝ => vfun c p.1 p.2) := by
  have h1 : Measurable fun p : ℝ × ℝ => xX c p.2 := (measurable_xX c).comp measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => yY c p.2 := (measurable_yY c).comp measurable_snd
  simp_rw [vfun_eq]
  exact ((((measurable_fst.mul (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_fst))).mul
    h1).sub ((measurable_snd.mul (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_fst))).mul
    h2)).div (measurable_const.mul ((measurable_fst.pow_const 2).sub (measurable_snd.pow_const 2))))

theorem vfun_sq_le {c u x : ℝ} (hu : 1 ≤ u) :
    vfun c u x ^ 2 ≤ 18 * om u * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) x := by
  rcases le_or_gt (|x|) ell with hx | hx
  · rw [indicator_of_mem (show x ∈ Icc (-ell) ell from abs_le.1 hx), mul_one, vfun_eq, div_pow]
    have hd := Cvs.Prolate.Hardy.ExteriorWeightAverages.den_ge hx hu
    have hdp := Cvs.Prolate.Hardy.ExteriorWeightAverages.den_pos hx hu
    have h1 := Cvs.Prolate.Hardy.ExteriorWeightAverages.ell_lt_one
    have hue : 0 < u - ell := by linarith
    have hX := abs_xX_le c x
    have hY := abs_yY_le c x
    have hnum : (u * Real.sin (c * u) * xX c x - x * Real.cos (c * u) * yY c x) ^ 2 ≤ 36 * u ^ 2 := by
      have hxu : |x| ≤ u := by linarith
      have : |u * Real.sin (c * u) * xX c x - x * Real.cos (c * u) * yY c x| ≤ 6 * u := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < u)]
        have e1 := abs_sin_le_one (c * u)
        have e2 := abs_cos_le_one (c * u)
        have a1 : |Real.sin (c * u)| * |xX c x| ≤ 3 := by
          nlinarith [abs_nonneg (Real.sin (c * u)), abs_nonneg (xX c x)]
        have a2 : |Real.cos (c * u)| * |yY c x| ≤ 3 := by
          nlinarith [abs_nonneg (Real.cos (c * u)), abs_nonneg (yY c x)]
        have a3 : u * |Real.sin (c * u)| * |xX c x| ≤ 3 * u := by
          rw [mul_assoc]; nlinarith
        have a4 : |x| * |Real.cos (c * u)| * |yY c x| ≤ 3 * u := by
          rw [mul_assoc]
          have := mul_nonneg (abs_nonneg (Real.cos (c * u))) (abs_nonneg (yY c x))
          nlinarith [abs_nonneg x]
        linarith
      have h6 : 0 ≤ 6 * u := by linarith
      nlinarith [sq_abs (u * Real.sin (c * u) * xX c x - x * Real.cos (c * u) * yY c x),
        abs_nonneg (u * Real.sin (c * u) * xX c x - x * Real.cos (c * u) * yY c x)]
    unfold om
    rw [mul_pow, div_le_iff₀ (by positivity)]
    have hπ : 0 < π ^ 2 := by positivity
    calc (u * Real.sin (c * u) * xX c x - x * Real.cos (c * u) * yY c x) ^ 2 ≤ 36 * u ^ 2 := hnum
      _ = 18 * (2 / (π ^ 2 * (u - ell) ^ 2)) * (π ^ 2 * ((u - ell) ^ 2 * u ^ 2)) := by field_simp; ring
      _ ≤ 18 * (2 / (π ^ 2 * (u - ell) ^ 2)) * (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2) := by gcongr
      _ = 18 * (2 / (π ^ 2 * (u - ell) ^ 2)) * (π ^ 2 * (u ^ 2 - x ^ 2) ^ 2) := rfl
  · rw [vfun_eq, xX_zero hx, yY_zero hx]
    simp only [mul_zero, sub_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have : 0 ≤ om u := by unfold om; positivity
    have : 0 ≤ (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) x := by
      by_cases h : x ∈ Icc (-ell) ell <;> simp [h]
    positivity

theorem integrable_vfun_sq (c : ℝ) :
    Integrable (Function.uncurry fun u x => vfun c u x ^ 2) ((volume.restrict (Ioi 1)).prod volume) := by
  have hg : Integrable (fun p : ℝ × ℝ => 18 * om p.1 * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) p.2)
      ((volume.restrict (Ioi 1)).prod volume) := by
    have := (Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_om.const_mul 18).mul_prod
      ((integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (C := (1 : ℝ)) (s := Icc (-ell) ell) (μ := volume) measure_Icc_lt_top.ne))
    simpa [mul_assoc] using this
  refine hg.mono' ((measurable_vfun c).pow_const 2).aestronglyMeasurable ?_
  have hfst : ∀ᵐ p ∂((volume.restrict (Ioi 1)).prod volume), p.1 ∈ Ioi (1 : ℝ) :=
    QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (1 : ℝ)))
      (ν := (volume : Measure ℝ))) (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hfst] with p hp
  show ‖vfun c p.1 p.2 ^ 2‖ ≤ 18 * om p.1 * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) p.2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact vfun_sq_le (le_of_lt hp)

/-- **Fubini**: `∫_{u>1}‖V_u‖² = ∫ G_c(x) dx`. -/
theorem integral_norm_waveV_sq {c : ℝ} (hc : 0 ≤ c) :
    ∫ u in Ioi 1, ‖waveV c u ell‖ ^ 2 = ∫ x, gG c x := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => Cvs.Prolate.Hardy.TwoCarrierWaveExplicit.norm_waveV_sq hc hu),
    integral_integral_swap (integrable_vfun_sq c)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integral_vfun_sq c x)

end Cvs.Prolate.Hardy.ColumnWaveSquareIntegral

end
