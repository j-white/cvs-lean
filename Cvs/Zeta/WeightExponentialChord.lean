import Mathlib
import Cvs.Zeta.KernelPrefactorBound
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ThetaWeightedTail
import Cvs.Zeta.WeightedIntegralBound

/-!
# The weight against its exponential chord

`t^{−1/2}` and `√2·e^{−(log 2/2)t}` agree at `t = 1` and `t = 2`, and between them the
first is smaller: taking logs, that is concavity of `log`.  The chord integrates in closed
form where the constant weight does not.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.Zeta.WeightExponentialChord
open Cvs.ZeroFree

/-- **`log` lies above its chord.**  On `[1,2]`, `log t ≥ (t−1)·log 2`. -/
theorem log_ge_chord {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) :
    (t - 1) * Real.log 2 ≤ Real.log t := by
  have hcon : ConcaveOn ℝ (Set.Ioi (0:ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hx : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have hy : (2:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have ha : (0:ℝ) ≤ 2 - t := by linarith
  have hb : (0:ℝ) ≤ t - 1 := by linarith
  have hab : (2 - t) + (t - 1) = 1 := by ring
  have h := hcon.2 hx hy ha hb hab
  rw [show (2 - t) • (1:ℝ) + (t - 1) • (2:ℝ) = t by simp; ring] at h
  simpa [Real.log_one] using h

/-- **The weight, under its exponential chord.**  `t^{−1/2} ≤ √2·e^{−(log 2/2)t}` on
`[1,2]`. -/
theorem weight_le_exp_chord {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) :
    t ^ (-(1/2) : ℝ) ≤ Real.sqrt 2 * Real.exp (-(Real.log 2 / 2) * t) := by
  have htpos : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one h1
  have hchord := log_ge_chord h1 h2
  -- both sides are exponentials of their logs
  have hL : t ^ (-(1/2) : ℝ) = Real.exp (-(1/2) * Real.log t) := by
    rw [Real.rpow_def_of_pos htpos]; ring_nf
  have hR : Real.sqrt 2 * Real.exp (-(Real.log 2 / 2) * t)
      = Real.exp (Real.log 2 / 2 + -(Real.log 2 / 2) * t) := by
    rw [Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    ring_nf
  rw [hL, hR]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hchord]

/-- `∫_{Ioi c} e^{−rt} = e^{−rc}/r`, at any positive rate. -/
theorem integral_exp_neg_rate_Ioi {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in Set.Ioi c, Real.exp (-(r * t))) = Real.exp (-(r * c)) / r := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) c hr
  simp only [smul_eq_mul] at h
  rw [h, integral_exp_neg_Ioi]
  ring

theorem exp_neg_rate_integrableOn {r : ℝ} (hr : 0 < r) (c : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(r * t))) (Set.Ioi c) := by
  have h := exp_neg_integrableOn_Ioi c (b := r) hr
  simpa only [neg_mul] using h

/-- `√2 = e^{log 2 / 2}`, so the chord's rate folds into `e^{−π}`. -/
theorem sqrt_two_eq_exp : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
  have hsq : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [← Real.exp_nat_mul,
      show ((2:ℕ):ℝ) * (Real.log 2 / 2) = Real.log 2 by push_cast; ring]
    exact Real.exp_log (by norm_num)
  nth_rewrite 1 [← hsq]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- **The weighted integral, against the chord.**  Below `2` the exponential chord; above
it the constant `0.7072`. -/
theorem weighted_integral_le_chord :
    (∫ t in Set.Ioi (1:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      ≤ (Real.exp (-Real.pi) - Real.sqrt 2 / 2 * Real.exp (-(2 * Real.pi)))
          / (Real.pi + Real.log 2 / 2)
        + 0.7072 * (Real.exp (-(2 * Real.pi)) / Real.pi) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.pi + Real.log 2 / 2 with hcdef
  have hcpos : (0:ℝ) < c := by rw [hcdef]; linarith
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hint := Cvs.Zeta.WeightedIntegralBound.weighted_integrableOn
  have hintA : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) (Set.Ioc (1:ℝ) 2) :=
    hint.mono_set (by rw [Cvs.Zeta.WeightedIntegralBound.Ioi_one_split]; exact Set.subset_union_left)
  have hintB : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) (Set.Ioi (2:ℝ)) :=
    hint.mono_set (by rw [Cvs.Zeta.WeightedIntegralBound.Ioi_one_split]; exact Set.subset_union_right)
  have hsplit := MeasureTheory.setIntegral_union Cvs.Zeta.WeightedIntegralBound.Ioc_Ioi_disjoint
    measurableSet_Ioi hintA hintB
  rw [← Cvs.Zeta.WeightedIntegralBound.Ioi_one_split] at hsplit
  rw [hsplit]
  -- below 2, against the chord
  have hA : (∫ t in Set.Ioc (1:ℝ) 2, t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      ≤ ∫ t in Set.Ioc (1:ℝ) 2, Real.sqrt 2 * Real.exp (-(c * t)) := by
    refine MeasureTheory.setIntegral_mono_on hintA
      (((exp_neg_rate_integrableOn hcpos 1).mono_set
        (by rw [Cvs.Zeta.WeightedIntegralBound.Ioi_one_split]; exact Set.subset_union_left)).const_mul _)
      measurableSet_Ioc ?_
    intro t ht
    have h1 : (1:ℝ) ≤ t := le_of_lt ht.1
    have hw := weight_le_exp_chord h1 ht.2
    have hexp : Real.sqrt 2 * Real.exp (-(Real.log 2 / 2) * t) * Real.exp (-(Real.pi * t))
        = Real.sqrt 2 * Real.exp (-(c * t)) := by
      rw [mul_assoc, ← Real.exp_add, hcdef]; congr 2; ring
    calc t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))
        ≤ Real.sqrt 2 * Real.exp (-(Real.log 2 / 2) * t) * Real.exp (-(Real.pi * t)) := by
          exact mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
      _ = Real.sqrt 2 * Real.exp (-(c * t)) := hexp
  -- above 2, the constant
  have hB : (∫ t in Set.Ioi (2:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      ≤ ∫ t in Set.Ioi (2:ℝ), 0.7072 * Real.exp (-(Real.pi * t)) := by
    refine MeasureTheory.setIntegral_mono_on hintB
      ((Cvs.Zeta.WeightedIntegralBound.exp_neg_pi_integrableOn 2).const_mul _) measurableSet_Ioi ?_
    intro t ht
    have ht2 : (2:ℝ) ≤ t := le_of_lt ht
    have htpos : (0:ℝ) < t := by linarith
    have hb : (2:ℝ) ^ (-(1/2) : ℝ) ≤ 0.7072 := by
      have hpos : (0:ℝ) < (2:ℝ) ^ (-(1/2):ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have hsq : ((2:ℝ) ^ (-(1/2):ℝ)) ^ 2 = 1/2 := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (-(1/2):ℝ)) 2, ← Real.rpow_mul (by norm_num)]
        norm_num
      nlinarith [hpos, hsq]
    have hpow : (t : ℝ) ^ (-(1/2) : ℝ) ≤ 0.7072 :=
      le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) ht2 (by norm_num)) hb
    nlinarith [Real.exp_pos (-(Real.pi * t)), Real.rpow_nonneg htpos.le (-(1/2) : ℝ)]
  -- evaluate the two majorants
  have hAval : (∫ t in Set.Ioc (1:ℝ) 2, Real.sqrt 2 * Real.exp (-(c * t)))
      = Real.sqrt 2 * ((Real.exp (-(c * 1)) - Real.exp (-(c * 2))) / c) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hu := MeasureTheory.setIntegral_union Cvs.Zeta.WeightedIntegralBound.Ioc_Ioi_disjoint
      measurableSet_Ioi
      ((exp_neg_rate_integrableOn hcpos 1).mono_set
        (by rw [Cvs.Zeta.WeightedIntegralBound.Ioi_one_split]; exact Set.subset_union_left))
      ((exp_neg_rate_integrableOn hcpos 1).mono_set
        (by rw [Cvs.Zeta.WeightedIntegralBound.Ioi_one_split]; exact Set.subset_union_right))
    rw [← Cvs.Zeta.WeightedIntegralBound.Ioi_one_split, integral_exp_neg_rate_Ioi hcpos 1,
      integral_exp_neg_rate_Ioi hcpos 2] at hu
    rw [sub_div]
    linarith [hu]
  have hBval : (∫ t in Set.Ioi (2:ℝ), 0.7072 * Real.exp (-(Real.pi * t)))
      = 0.7072 * (Real.exp (-(2 * Real.pi)) / Real.pi) := by
    rw [MeasureTheory.integral_const_mul, Cvs.Zeta.WeightedIntegralBound.integral_exp_neg_pi_Ioi 2]
    congr 2
    ring
  rw [hAval] at hA
  rw [hBval] at hB
  -- the chord's endpoints, in `e^{−π}` and `√2`
  have he1 : Real.exp (-(c * 1)) = Real.exp (-Real.pi) / Real.sqrt 2 := by
    rw [hcdef, sqrt_two_eq_exp, ← Real.exp_sub]
    congr 1; ring
  have he2 : Real.exp (-(c * 2)) = Real.exp (-(2 * Real.pi)) / 2 := by
    rw [show -(c * 2) = -(2 * Real.pi) - Real.log 2 by rw [hcdef]; ring,
      Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  rw [he1, he2] at hA
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfold : Real.sqrt 2 * ((Real.exp (-Real.pi) / Real.sqrt 2
        - Real.exp (-(2 * Real.pi)) / 2) / c)
      = (Real.exp (-Real.pi) - Real.sqrt 2 / 2 * Real.exp (-(2 * Real.pi))) / c := by
    have key : Real.sqrt 2 * (Real.exp (-Real.pi) / Real.sqrt 2
          - Real.exp (-(2 * Real.pi)) / 2)
        = Real.exp (-Real.pi) - Real.sqrt 2 / 2 * Real.exp (-(2 * Real.pi)) := by
      field_simp
    rw [mul_div_assoc', key]
  rw [hfold] at hA
  linarith [hA, hB]

/-- The chord bound, as an explicit numeral. -/
theorem weighted_integral_lt_num :
    (∫ t in Set.Ioi (1:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t))) < 0.0125 := by
  refine lt_of_le_of_lt weighted_integral_le_chord ?_
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h314 : (3.141592:ℝ) < Real.pi := Real.pi_gt_d6
  have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hs2 : (1.41421:ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs2u : Real.sqrt 2 < 1.41422 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hc : (3.488:ℝ) < Real.pi + Real.log 2 / 2 := by linarith
  have hE := Cvs.Zeta.KernelPrefactorBound.exp_pi_gt_2314
  have hepos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hEpos : (0:ℝ) < Real.exp (-Real.pi) := Real.exp_pos _
  have hEub : Real.exp (-Real.pi) < 1 / 23.14 := by
    rw [Real.exp_neg, inv_lt_comm₀ hepos (by norm_num)]; linarith
  have hF : Real.exp (-(2 * Real.pi)) = Real.exp (-Real.pi) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hF]
  set E : ℝ := Real.exp (-Real.pi) with hEdef
  -- the first term, against the lower bounds on `c` and `√2`
  have hden : (0:ℝ) < Real.pi + Real.log 2 / 2 := by linarith
  have hnum : (0:ℝ) < E - Real.sqrt 2 / 2 * E ^ 2 := by
    nlinarith [hEpos, hEub, hs2u, sq_nonneg E]
  have hB0 : (0:ℝ) ≤ E - 0.7071 * E ^ 2 := by nlinarith [hEpos, hEub, sq_nonneg E]
  have hAB : E - Real.sqrt 2 / 2 * E ^ 2 ≤ E - 0.7071 * E ^ 2 := by
    nlinarith [hs2, sq_nonneg E]
  have hT1 : (E - Real.sqrt 2 / 2 * E ^ 2) / (Real.pi + Real.log 2 / 2)
      ≤ (E - 0.7071 * E ^ 2) / 3.488 := by
    calc (E - Real.sqrt 2 / 2 * E ^ 2) / (Real.pi + Real.log 2 / 2)
        ≤ (E - 0.7071 * E ^ 2) / (Real.pi + Real.log 2 / 2) := by gcongr
      _ ≤ (E - 0.7071 * E ^ 2) / 3.488 := by gcongr
  have hT2 : (0.7072:ℝ) * (E ^ 2 / Real.pi) ≤ 0.7072 * (E ^ 2 / 3.141592) := by
    have : E ^ 2 / Real.pi ≤ E ^ 2 / 3.141592 :=
      div_le_div_of_nonneg_left (sq_nonneg E) (by norm_num) h314.le
    linarith
  refine lt_of_le_of_lt (add_le_add hT1 hT2) ?_
  have hE2 : E ^ 2 < (1 / 23.14) ^ 2 := by nlinarith [hEpos, hEub]
  have hexp : (E - 0.7071 * E ^ 2) / 3.488 + 0.7072 * (E ^ 2 / 3.141592)
      = (1 / 3.488) * E + ((0.7072 / 3.141592) - (0.7071 / 3.488)) * E ^ 2 := by ring
  rw [hexp]
  have hc1 : (0:ℝ) < (0.7072 / 3.141592) - (0.7071 / 3.488) := by norm_num
  nlinarith [hEub, hE2, hEpos, hc1]

/-- **The zero-free height with the chord**: `|Im ρ| > 6.24`. -/
theorem abs_im_gt_of_riemannXi_eq_zero {s : ℂ} (h : Cvs.Zeta.riemannXi s = 0) :
    6.24 < |s.im| := by
  refine Cvs.Zeta.ThetaWeightedTail.abs_im_gt_of_weighted h 0.0125 6.24 (by norm_num)
    Cvs.Zeta.WeightedIntegralBound.weighted_integrableOn weighted_integral_lt_num.le (by norm_num) ?_
  norm_num

end Cvs.Zeta.WeightExponentialChord
