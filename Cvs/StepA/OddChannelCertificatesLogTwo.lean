import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Cvs.Upstream.ArctanPolynomialBounds

/-!
# One hundred odd-sector channel certificates at `L = log 2`

    channel `n`, `b = 2n + ½`: a rational `t` with `t·(log 2/2) < π/2 + arctan(b/t)` and the cap
    `2/b − 2b/(b² + t²)` bounded below by a rational, summed over `n < 100`.
-/

noncomputable section

open Real

namespace Cvs.StepA.OddChannelCertificatesLogTwo

/-- Channel `0`: the rational witness inequality. -/
theorem chan_0_witness : (48244 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (((1 / 2 : ℝ) / (48244 / 10000 : ℝ)) - ((1 / 2 : ℝ) / (48244 / 10000 : ℝ))^3/3 + ((1 / 2 : ℝ) / (48244 / 10000 : ℝ))^5/5 - ((1 / 2 : ℝ) / (48244 / 10000 : ℝ))^7/7) := by norm_num

/-- Channel `0`: the pole-free condition. -/
theorem chan_0 : (48244 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((1 / 2 : ℝ) / (48244 / 10000 : ℝ)) := by
  have hw := chan_0_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (48244 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_ge_poly7 (z := ((1 / 2 : ℝ) / (48244 / 10000 : ℝ))) (by norm_num)
  linarith

/-- Channel `0`: the cap. -/
theorem chan_0_cap : (3957491 / 1000000 : ℝ) ≤ 2 / (1 / 2 : ℝ) - 2 * (1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + (48244 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `1`: the rational witness inequality. -/
theorem chan_1_witness : (57012 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (((5 / 2 : ℝ) / (57012 / 10000 : ℝ)) - ((5 / 2 : ℝ) / (57012 / 10000 : ℝ))^3/3 + ((5 / 2 : ℝ) / (57012 / 10000 : ℝ))^5/5 - ((5 / 2 : ℝ) / (57012 / 10000 : ℝ))^7/7) := by norm_num

/-- Channel `1`: the pole-free condition. -/
theorem chan_1 : (57012 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((5 / 2 : ℝ) / (57012 / 10000 : ℝ)) := by
  have hw := chan_1_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (57012 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_ge_poly7 (z := ((5 / 2 : ℝ) / (57012 / 10000 : ℝ))) (by norm_num)
  linarith

/-- Channel `1`: the cap. -/
theorem chan_1_cap : (670979 / 1000000 : ℝ) ≤ 2 / (5 / 2 : ℝ) - 2 * (5 / 2 : ℝ) / ((5 / 2 : ℝ) ^ 2 + (57012 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `2`: the rational witness inequality. -/
theorem chan_2_witness : (62910 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (78539816 / 100000000 : ℝ) - (-((((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) - 1) / (((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) + 1)) - (-((((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) - 1) / (((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) + 1)))^3/3 + (-((((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) - 1) / (((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) + 1)))^5/5) := by norm_num

/-- Channel `2`: the pole-free condition. -/
theorem chan_2 : (62910 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) := by
  have hw := chan_2_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (62910 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_add_pi4 (z := ((9 / 2 : ℝ) / (62910 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := -((((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) - 1) / (((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) + 1))) (by norm_num)
  have hn : Real.arctan ((((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) - 1) / (((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) + 1)) = - Real.arctan (-((((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) - 1) / (((9 / 2 : ℝ) / (62910 / 10000 : ℝ)) + 1))) := by rw [Real.arctan_neg, neg_neg]
  have hq := Cvs.Upstream.ArctanPolynomialBounds.pi_div_four_gt
  linarith

/-- Channel `2`: the cap. -/
theorem chan_2_cap : (294009 / 1000000 : ℝ) ≤ 2 / (9 / 2 : ℝ) - 2 * (9 / 2 : ℝ) / ((9 / 2 : ℝ) ^ 2 + (62910 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `3`: the rational witness inequality. -/
theorem chan_3_witness : (67205 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (78539816 / 100000000 : ℝ) - (-((((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) - 1) / (((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) + 1)) - (-((((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) - 1) / (((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) + 1)))^3/3 + (-((((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) - 1) / (((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) + 1)))^5/5) := by norm_num

/-- Channel `3`: the pole-free condition. -/
theorem chan_3 : (67205 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) := by
  have hw := chan_3_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (67205 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_add_pi4 (z := ((13 / 2 : ℝ) / (67205 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := -((((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) - 1) / (((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) + 1))) (by norm_num)
  have hn : Real.arctan ((((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) - 1) / (((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) + 1)) = - Real.arctan (-((((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) - 1) / (((13 / 2 : ℝ) / (67205 / 10000 : ℝ)) + 1))) := by rw [Real.arctan_neg, neg_neg]
  have hq := Cvs.Upstream.ArctanPolynomialBounds.pi_div_four_gt
  linarith

/-- Channel `3`: the cap. -/
theorem chan_3_cap : (158976 / 1000000 : ℝ) ≤ 2 / (13 / 2 : ℝ) - 2 * (13 / 2 : ℝ) / ((13 / 2 : ℝ) ^ 2 + (67205 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `4`: the rational witness inequality. -/
theorem chan_4_witness : (70443 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (78539816 / 100000000 : ℝ) + (((((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) - 1) / (((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) + 1)) - ((((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) - 1) / (((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) + 1))^3/3 + ((((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) - 1) / (((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) + 1))^5/5 - ((((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) - 1) / (((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) + 1))^7/7) := by norm_num

/-- Channel `4`: the pole-free condition. -/
theorem chan_4 : (70443 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) := by
  have hw := chan_4_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (70443 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_add_pi4 (z := ((17 / 2 : ℝ) / (70443 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_ge_poly7 (z := ((((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) - 1) / (((17 / 2 : ℝ) / (70443 / 10000 : ℝ)) + 1))) (by norm_num)
  have hq := Cvs.Upstream.ArctanPolynomialBounds.pi_div_four_gt
  linarith

/-- Channel `4`: the cap. -/
theorem chan_4_cap : (95803 / 1000000 : ℝ) ≤ 2 / (17 / 2 : ℝ) - 2 * (17 / 2 : ℝ) / ((17 / 2 : ℝ) ^ 2 + (70443 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `5`: the rational witness inequality. -/
theorem chan_5_witness : (72945 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (78539816 / 100000000 : ℝ) + (((((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) - 1) / (((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) + 1)) - ((((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) - 1) / (((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) + 1))^3/3 + ((((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) - 1) / (((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) + 1))^5/5 - ((((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) - 1) / (((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) + 1))^7/7) := by norm_num

/-- Channel `5`: the pole-free condition. -/
theorem chan_5 : (72945 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) := by
  have hw := chan_5_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (72945 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_add_pi4 (z := ((21 / 2 : ℝ) / (72945 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_ge_poly7 (z := ((((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) - 1) / (((21 / 2 : ℝ) / (72945 / 10000 : ℝ)) + 1))) (by norm_num)
  have hq := Cvs.Upstream.ArctanPolynomialBounds.pi_div_four_gt
  linarith

/-- Channel `5`: the cap. -/
theorem chan_5_cap : (62004 / 1000000 : ℝ) ≤ 2 / (21 / 2 : ℝ) - 2 * (21 / 2 : ℝ) / ((21 / 2 : ℝ) ^ 2 + (72945 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `6`: the rational witness inequality. -/
theorem chan_6_witness : (74923 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (78539816 / 100000000 : ℝ) + (((((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) - 1) / (((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) + 1)) - ((((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) - 1) / (((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) + 1))^3/3 + ((((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) - 1) / (((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) + 1))^5/5 - ((((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) - 1) / (((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) + 1))^7/7) := by norm_num

/-- Channel `6`: the pole-free condition. -/
theorem chan_6 : (74923 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) := by
  have hw := chan_6_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (74923 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_add_pi4 (z := ((25 / 2 : ℝ) / (74923 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_ge_poly7 (z := ((((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) - 1) / (((25 / 2 : ℝ) / (74923 / 10000 : ℝ)) + 1))) (by norm_num)
  have hq := Cvs.Upstream.ArctanPolynomialBounds.pi_div_four_gt
  linarith

/-- Channel `6`: the cap. -/
theorem chan_6_cap : (42288 / 1000000 : ℝ) ≤ 2 / (25 / 2 : ℝ) - 2 * (25 / 2 : ℝ) / ((25 / 2 : ℝ) ^ 2 + (74923 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `7`: the rational witness inequality. -/
theorem chan_7_witness : (76519 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (78539816 / 100000000 : ℝ) + (((((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) - 1) / (((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) + 1)) - ((((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) - 1) / (((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) + 1))^3/3 + ((((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) - 1) / (((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) + 1))^5/5 - ((((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) - 1) / (((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) + 1))^7/7) := by norm_num

/-- Channel `7`: the pole-free condition. -/
theorem chan_7 : (76519 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) := by
  have hw := chan_7_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (76519 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_add_pi4 (z := ((29 / 2 : ℝ) / (76519 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_ge_poly7 (z := ((((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) - 1) / (((29 / 2 : ℝ) / (76519 / 10000 : ℝ)) + 1))) (by norm_num)
  have hq := Cvs.Upstream.ArctanPolynomialBounds.pi_div_four_gt
  linarith

/-- Channel `7`: the cap. -/
theorem chan_7_cap : (30044 / 1000000 : ℝ) ≤ 2 / (29 / 2 : ℝ) - 2 * (29 / 2 : ℝ) / ((29 / 2 : ℝ) ^ 2 + (76519 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `8`: the rational witness inequality. -/
theorem chan_8_witness : (77831 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((33 / 2 : ℝ) / (77831 / 10000 : ℝ))) - (1 / ((33 / 2 : ℝ) / (77831 / 10000 : ℝ)))^3/3 + (1 / ((33 / 2 : ℝ) / (77831 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `8`: the pole-free condition. -/
theorem chan_8 : (77831 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((33 / 2 : ℝ) / (77831 / 10000 : ℝ)) := by
  have hw := chan_8_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (77831 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((33 / 2 : ℝ) / (77831 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((33 / 2 : ℝ) / (77831 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `8`: the cap. -/
theorem chan_8_cap : (22061 / 1000000 : ℝ) ≤ 2 / (33 / 2 : ℝ) - 2 * (33 / 2 : ℝ) / ((33 / 2 : ℝ) ^ 2 + (77831 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `9`: the rational witness inequality. -/
theorem chan_9_witness : (78925 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((37 / 2 : ℝ) / (78925 / 10000 : ℝ))) - (1 / ((37 / 2 : ℝ) / (78925 / 10000 : ℝ)))^3/3 + (1 / ((37 / 2 : ℝ) / (78925 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `9`: the pole-free condition. -/
theorem chan_9 : (78925 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((37 / 2 : ℝ) / (78925 / 10000 : ℝ)) := by
  have hw := chan_9_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (78925 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((37 / 2 : ℝ) / (78925 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((37 / 2 : ℝ) / (78925 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `9`: the cap. -/
theorem chan_9_cap : (16646 / 1000000 : ℝ) ≤ 2 / (37 / 2 : ℝ) - 2 * (37 / 2 : ℝ) / ((37 / 2 : ℝ) ^ 2 + (78925 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `10`: the rational witness inequality. -/
theorem chan_10_witness : (79851 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((41 / 2 : ℝ) / (79851 / 10000 : ℝ))) - (1 / ((41 / 2 : ℝ) / (79851 / 10000 : ℝ)))^3/3 + (1 / ((41 / 2 : ℝ) / (79851 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `10`: the pole-free condition. -/
theorem chan_10 : (79851 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((41 / 2 : ℝ) / (79851 / 10000 : ℝ)) := by
  have hw := chan_10_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (79851 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((41 / 2 : ℝ) / (79851 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((41 / 2 : ℝ) / (79851 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `10`: the cap. -/
theorem chan_10_cap : (12852 / 1000000 : ℝ) ≤ 2 / (41 / 2 : ℝ) - 2 * (41 / 2 : ℝ) / ((41 / 2 : ℝ) ^ 2 + (79851 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `11`: the rational witness inequality. -/
theorem chan_11_witness : (80645 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((45 / 2 : ℝ) / (80645 / 10000 : ℝ))) - (1 / ((45 / 2 : ℝ) / (80645 / 10000 : ℝ)))^3/3 + (1 / ((45 / 2 : ℝ) / (80645 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `11`: the pole-free condition. -/
theorem chan_11 : (80645 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((45 / 2 : ℝ) / (80645 / 10000 : ℝ)) := by
  have hw := chan_11_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (80645 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((45 / 2 : ℝ) / (80645 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((45 / 2 : ℝ) / (80645 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `11`: the cap. -/
theorem chan_11_cap : (10119 / 1000000 : ℝ) ≤ 2 / (45 / 2 : ℝ) - 2 * (45 / 2 : ℝ) / ((45 / 2 : ℝ) ^ 2 + (80645 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `12`: the rational witness inequality. -/
theorem chan_12_witness : (81331 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((49 / 2 : ℝ) / (81331 / 10000 : ℝ))) - (1 / ((49 / 2 : ℝ) / (81331 / 10000 : ℝ)))^3/3 + (1 / ((49 / 2 : ℝ) / (81331 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `12`: the pole-free condition. -/
theorem chan_12 : (81331 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((49 / 2 : ℝ) / (81331 / 10000 : ℝ)) := by
  have hw := chan_12_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (81331 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((49 / 2 : ℝ) / (81331 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((49 / 2 : ℝ) / (81331 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `12`: the cap. -/
theorem chan_12_cap : (8102 / 1000000 : ℝ) ≤ 2 / (49 / 2 : ℝ) - 2 * (49 / 2 : ℝ) / ((49 / 2 : ℝ) ^ 2 + (81331 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `13`: the rational witness inequality. -/
theorem chan_13_witness : (81931 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((53 / 2 : ℝ) / (81931 / 10000 : ℝ))) - (1 / ((53 / 2 : ℝ) / (81931 / 10000 : ℝ)))^3/3 + (1 / ((53 / 2 : ℝ) / (81931 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `13`: the pole-free condition. -/
theorem chan_13 : (81931 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((53 / 2 : ℝ) / (81931 / 10000 : ℝ)) := by
  have hw := chan_13_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (81931 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((53 / 2 : ℝ) / (81931 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((53 / 2 : ℝ) / (81931 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `13`: the cap. -/
theorem chan_13_cap : (6584 / 1000000 : ℝ) ≤ 2 / (53 / 2 : ℝ) - 2 * (53 / 2 : ℝ) / ((53 / 2 : ℝ) ^ 2 + (81931 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `14`: the rational witness inequality. -/
theorem chan_14_witness : (82458 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((57 / 2 : ℝ) / (82458 / 10000 : ℝ))) - (1 / ((57 / 2 : ℝ) / (82458 / 10000 : ℝ)))^3/3 + (1 / ((57 / 2 : ℝ) / (82458 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `14`: the pole-free condition. -/
theorem chan_14 : (82458 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((57 / 2 : ℝ) / (82458 / 10000 : ℝ)) := by
  have hw := chan_14_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (82458 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((57 / 2 : ℝ) / (82458 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((57 / 2 : ℝ) / (82458 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `14`: the cap. -/
theorem chan_14_cap : (5420 / 1000000 : ℝ) ≤ 2 / (57 / 2 : ℝ) - 2 * (57 / 2 : ℝ) / ((57 / 2 : ℝ) ^ 2 + (82458 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `15`: the rational witness inequality. -/
theorem chan_15_witness : (82927 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((61 / 2 : ℝ) / (82927 / 10000 : ℝ))) - (1 / ((61 / 2 : ℝ) / (82927 / 10000 : ℝ)))^3/3 + (1 / ((61 / 2 : ℝ) / (82927 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `15`: the pole-free condition. -/
theorem chan_15 : (82927 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((61 / 2 : ℝ) / (82927 / 10000 : ℝ)) := by
  have hw := chan_15_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (82927 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((61 / 2 : ℝ) / (82927 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((61 / 2 : ℝ) / (82927 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `15`: the cap. -/
theorem chan_15_cap : (4513 / 1000000 : ℝ) ≤ 2 / (61 / 2 : ℝ) - 2 * (61 / 2 : ℝ) / ((61 / 2 : ℝ) ^ 2 + (82927 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `16`: the rational witness inequality. -/
theorem chan_16_witness : (83345 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((65 / 2 : ℝ) / (83345 / 10000 : ℝ))) - (1 / ((65 / 2 : ℝ) / (83345 / 10000 : ℝ)))^3/3 + (1 / ((65 / 2 : ℝ) / (83345 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `16`: the pole-free condition. -/
theorem chan_16 : (83345 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((65 / 2 : ℝ) / (83345 / 10000 : ℝ)) := by
  have hw := chan_16_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (83345 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((65 / 2 : ℝ) / (83345 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((65 / 2 : ℝ) / (83345 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `16`: the cap. -/
theorem chan_16_cap : (3797 / 1000000 : ℝ) ≤ 2 / (65 / 2 : ℝ) - 2 * (65 / 2 : ℝ) / ((65 / 2 : ℝ) ^ 2 + (83345 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `17`: the rational witness inequality. -/
theorem chan_17_witness : (83720 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((69 / 2 : ℝ) / (83720 / 10000 : ℝ))) - (1 / ((69 / 2 : ℝ) / (83720 / 10000 : ℝ)))^3/3 + (1 / ((69 / 2 : ℝ) / (83720 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `17`: the pole-free condition. -/
theorem chan_17 : (83720 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((69 / 2 : ℝ) / (83720 / 10000 : ℝ)) := by
  have hw := chan_17_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (83720 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((69 / 2 : ℝ) / (83720 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((69 / 2 : ℝ) / (83720 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `17`: the cap. -/
theorem chan_17_cap : (3223 / 1000000 : ℝ) ≤ 2 / (69 / 2 : ℝ) - 2 * (69 / 2 : ℝ) / ((69 / 2 : ℝ) ^ 2 + (83720 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `18`: the rational witness inequality. -/
theorem chan_18_witness : (84059 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((73 / 2 : ℝ) / (84059 / 10000 : ℝ))) - (1 / ((73 / 2 : ℝ) / (84059 / 10000 : ℝ)))^3/3 + (1 / ((73 / 2 : ℝ) / (84059 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `18`: the pole-free condition. -/
theorem chan_18 : (84059 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((73 / 2 : ℝ) / (84059 / 10000 : ℝ)) := by
  have hw := chan_18_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (84059 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((73 / 2 : ℝ) / (84059 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((73 / 2 : ℝ) / (84059 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `18`: the cap. -/
theorem chan_18_cap : (2759 / 1000000 : ℝ) ≤ 2 / (73 / 2 : ℝ) - 2 * (73 / 2 : ℝ) / ((73 / 2 : ℝ) ^ 2 + (84059 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `19`: the rational witness inequality. -/
theorem chan_19_witness : (84366 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((77 / 2 : ℝ) / (84366 / 10000 : ℝ))) - (1 / ((77 / 2 : ℝ) / (84366 / 10000 : ℝ)))^3/3 + (1 / ((77 / 2 : ℝ) / (84366 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `19`: the pole-free condition. -/
theorem chan_19 : (84366 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((77 / 2 : ℝ) / (84366 / 10000 : ℝ)) := by
  have hw := chan_19_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (84366 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((77 / 2 : ℝ) / (84366 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((77 / 2 : ℝ) / (84366 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `19`: the cap. -/
theorem chan_19_cap : (2380 / 1000000 : ℝ) ≤ 2 / (77 / 2 : ℝ) - 2 * (77 / 2 : ℝ) / ((77 / 2 : ℝ) ^ 2 + (84366 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `20`: the rational witness inequality. -/
theorem chan_20_witness : (84646 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((81 / 2 : ℝ) / (84646 / 10000 : ℝ))) - (1 / ((81 / 2 : ℝ) / (84646 / 10000 : ℝ)))^3/3 + (1 / ((81 / 2 : ℝ) / (84646 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `20`: the pole-free condition. -/
theorem chan_20 : (84646 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((81 / 2 : ℝ) / (84646 / 10000 : ℝ)) := by
  have hw := chan_20_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (84646 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((81 / 2 : ℝ) / (84646 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((81 / 2 : ℝ) / (84646 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `20`: the cap. -/
theorem chan_20_cap : (2066 / 1000000 : ℝ) ≤ 2 / (81 / 2 : ℝ) - 2 * (81 / 2 : ℝ) / ((81 / 2 : ℝ) ^ 2 + (84646 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `21`: the rational witness inequality. -/
theorem chan_21_witness : (84902 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((85 / 2 : ℝ) / (84902 / 10000 : ℝ))) - (1 / ((85 / 2 : ℝ) / (84902 / 10000 : ℝ)))^3/3 + (1 / ((85 / 2 : ℝ) / (84902 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `21`: the pole-free condition. -/
theorem chan_21 : (84902 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((85 / 2 : ℝ) / (84902 / 10000 : ℝ)) := by
  have hw := chan_21_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (84902 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((85 / 2 : ℝ) / (84902 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((85 / 2 : ℝ) / (84902 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `21`: the cap. -/
theorem chan_21_cap : (1805 / 1000000 : ℝ) ≤ 2 / (85 / 2 : ℝ) - 2 * (85 / 2 : ℝ) / ((85 / 2 : ℝ) ^ 2 + (84902 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `22`: the rational witness inequality. -/
theorem chan_22_witness : (85138 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((89 / 2 : ℝ) / (85138 / 10000 : ℝ))) - (1 / ((89 / 2 : ℝ) / (85138 / 10000 : ℝ)))^3/3 + (1 / ((89 / 2 : ℝ) / (85138 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `22`: the pole-free condition. -/
theorem chan_22 : (85138 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((89 / 2 : ℝ) / (85138 / 10000 : ℝ)) := by
  have hw := chan_22_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (85138 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((89 / 2 : ℝ) / (85138 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((89 / 2 : ℝ) / (85138 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `22`: the cap. -/
theorem chan_22_cap : (1587 / 1000000 : ℝ) ≤ 2 / (89 / 2 : ℝ) - 2 * (89 / 2 : ℝ) / ((89 / 2 : ℝ) ^ 2 + (85138 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `23`: the rational witness inequality. -/
theorem chan_23_witness : (85354 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((93 / 2 : ℝ) / (85354 / 10000 : ℝ))) - (1 / ((93 / 2 : ℝ) / (85354 / 10000 : ℝ)))^3/3 + (1 / ((93 / 2 : ℝ) / (85354 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `23`: the pole-free condition. -/
theorem chan_23 : (85354 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((93 / 2 : ℝ) / (85354 / 10000 : ℝ)) := by
  have hw := chan_23_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (85354 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((93 / 2 : ℝ) / (85354 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((93 / 2 : ℝ) / (85354 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `23`: the cap. -/
theorem chan_23_cap : (1401 / 1000000 : ℝ) ≤ 2 / (93 / 2 : ℝ) - 2 * (93 / 2 : ℝ) / ((93 / 2 : ℝ) ^ 2 + (85354 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `24`: the rational witness inequality. -/
theorem chan_24_witness : (85555 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((97 / 2 : ℝ) / (85555 / 10000 : ℝ))) - (1 / ((97 / 2 : ℝ) / (85555 / 10000 : ℝ)))^3/3 + (1 / ((97 / 2 : ℝ) / (85555 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `24`: the pole-free condition. -/
theorem chan_24 : (85555 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((97 / 2 : ℝ) / (85555 / 10000 : ℝ)) := by
  have hw := chan_24_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (85555 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((97 / 2 : ℝ) / (85555 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((97 / 2 : ℝ) / (85555 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `24`: the cap. -/
theorem chan_24_cap : (1244 / 1000000 : ℝ) ≤ 2 / (97 / 2 : ℝ) - 2 * (97 / 2 : ℝ) / ((97 / 2 : ℝ) ^ 2 + (85555 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `25`: the rational witness inequality. -/
theorem chan_25_witness : (85740 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((101 / 2 : ℝ) / (85740 / 10000 : ℝ))) - (1 / ((101 / 2 : ℝ) / (85740 / 10000 : ℝ)))^3/3 + (1 / ((101 / 2 : ℝ) / (85740 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `25`: the pole-free condition. -/
theorem chan_25 : (85740 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((101 / 2 : ℝ) / (85740 / 10000 : ℝ)) := by
  have hw := chan_25_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (85740 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((101 / 2 : ℝ) / (85740 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((101 / 2 : ℝ) / (85740 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `25`: the cap. -/
theorem chan_25_cap : (1109 / 1000000 : ℝ) ≤ 2 / (101 / 2 : ℝ) - 2 * (101 / 2 : ℝ) / ((101 / 2 : ℝ) ^ 2 + (85740 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `26`: the rational witness inequality. -/
theorem chan_26_witness : (85913 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((105 / 2 : ℝ) / (85913 / 10000 : ℝ))) - (1 / ((105 / 2 : ℝ) / (85913 / 10000 : ℝ)))^3/3 + (1 / ((105 / 2 : ℝ) / (85913 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `26`: the pole-free condition. -/
theorem chan_26 : (85913 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((105 / 2 : ℝ) / (85913 / 10000 : ℝ)) := by
  have hw := chan_26_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (85913 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((105 / 2 : ℝ) / (85913 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((105 / 2 : ℝ) / (85913 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `26`: the cap. -/
theorem chan_26_cap : (993 / 1000000 : ℝ) ≤ 2 / (105 / 2 : ℝ) - 2 * (105 / 2 : ℝ) / ((105 / 2 : ℝ) ^ 2 + (85913 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `27`: the rational witness inequality. -/
theorem chan_27_witness : (86074 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((109 / 2 : ℝ) / (86074 / 10000 : ℝ))) - (1 / ((109 / 2 : ℝ) / (86074 / 10000 : ℝ)))^3/3 + (1 / ((109 / 2 : ℝ) / (86074 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `27`: the pole-free condition. -/
theorem chan_27 : (86074 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((109 / 2 : ℝ) / (86074 / 10000 : ℝ)) := by
  have hw := chan_27_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86074 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((109 / 2 : ℝ) / (86074 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((109 / 2 : ℝ) / (86074 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `27`: the cap. -/
theorem chan_27_cap : (893 / 1000000 : ℝ) ≤ 2 / (109 / 2 : ℝ) - 2 * (109 / 2 : ℝ) / ((109 / 2 : ℝ) ^ 2 + (86074 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `28`: the rational witness inequality. -/
theorem chan_28_witness : (86224 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((113 / 2 : ℝ) / (86224 / 10000 : ℝ))) - (1 / ((113 / 2 : ℝ) / (86224 / 10000 : ℝ)))^3/3 + (1 / ((113 / 2 : ℝ) / (86224 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `28`: the pole-free condition. -/
theorem chan_28 : (86224 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((113 / 2 : ℝ) / (86224 / 10000 : ℝ)) := by
  have hw := chan_28_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86224 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((113 / 2 : ℝ) / (86224 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((113 / 2 : ℝ) / (86224 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `28`: the cap. -/
theorem chan_28_cap : (805 / 1000000 : ℝ) ≤ 2 / (113 / 2 : ℝ) - 2 * (113 / 2 : ℝ) / ((113 / 2 : ℝ) ^ 2 + (86224 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `29`: the rational witness inequality. -/
theorem chan_29_witness : (86365 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((117 / 2 : ℝ) / (86365 / 10000 : ℝ))) - (1 / ((117 / 2 : ℝ) / (86365 / 10000 : ℝ)))^3/3 + (1 / ((117 / 2 : ℝ) / (86365 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `29`: the pole-free condition. -/
theorem chan_29 : (86365 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((117 / 2 : ℝ) / (86365 / 10000 : ℝ)) := by
  have hw := chan_29_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86365 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((117 / 2 : ℝ) / (86365 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((117 / 2 : ℝ) / (86365 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `29`: the cap. -/
theorem chan_29_cap : (729 / 1000000 : ℝ) ≤ 2 / (117 / 2 : ℝ) - 2 * (117 / 2 : ℝ) / ((117 / 2 : ℝ) ^ 2 + (86365 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `30`: the rational witness inequality. -/
theorem chan_30_witness : (86496 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((121 / 2 : ℝ) / (86496 / 10000 : ℝ))) - (1 / ((121 / 2 : ℝ) / (86496 / 10000 : ℝ)))^3/3 + (1 / ((121 / 2 : ℝ) / (86496 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `30`: the pole-free condition. -/
theorem chan_30 : (86496 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((121 / 2 : ℝ) / (86496 / 10000 : ℝ)) := by
  have hw := chan_30_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86496 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((121 / 2 : ℝ) / (86496 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((121 / 2 : ℝ) / (86496 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `30`: the cap. -/
theorem chan_30_cap : (662 / 1000000 : ℝ) ≤ 2 / (121 / 2 : ℝ) - 2 * (121 / 2 : ℝ) / ((121 / 2 : ℝ) ^ 2 + (86496 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `31`: the rational witness inequality. -/
theorem chan_31_witness : (86620 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((125 / 2 : ℝ) / (86620 / 10000 : ℝ))) - (1 / ((125 / 2 : ℝ) / (86620 / 10000 : ℝ)))^3/3 + (1 / ((125 / 2 : ℝ) / (86620 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `31`: the pole-free condition. -/
theorem chan_31 : (86620 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((125 / 2 : ℝ) / (86620 / 10000 : ℝ)) := by
  have hw := chan_31_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86620 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((125 / 2 : ℝ) / (86620 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((125 / 2 : ℝ) / (86620 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `31`: the cap. -/
theorem chan_31_cap : (603 / 1000000 : ℝ) ≤ 2 / (125 / 2 : ℝ) - 2 * (125 / 2 : ℝ) / ((125 / 2 : ℝ) ^ 2 + (86620 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `32`: the rational witness inequality. -/
theorem chan_32_witness : (86737 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((129 / 2 : ℝ) / (86737 / 10000 : ℝ))) - (1 / ((129 / 2 : ℝ) / (86737 / 10000 : ℝ)))^3/3 + (1 / ((129 / 2 : ℝ) / (86737 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `32`: the pole-free condition. -/
theorem chan_32 : (86737 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((129 / 2 : ℝ) / (86737 / 10000 : ℝ)) := by
  have hw := chan_32_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86737 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((129 / 2 : ℝ) / (86737 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((129 / 2 : ℝ) / (86737 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `32`: the cap. -/
theorem chan_32_cap : (550 / 1000000 : ℝ) ≤ 2 / (129 / 2 : ℝ) - 2 * (129 / 2 : ℝ) / ((129 / 2 : ℝ) ^ 2 + (86737 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `33`: the rational witness inequality. -/
theorem chan_33_witness : (86847 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((133 / 2 : ℝ) / (86847 / 10000 : ℝ))) - (1 / ((133 / 2 : ℝ) / (86847 / 10000 : ℝ)))^3/3 + (1 / ((133 / 2 : ℝ) / (86847 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `33`: the pole-free condition. -/
theorem chan_33 : (86847 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((133 / 2 : ℝ) / (86847 / 10000 : ℝ)) := by
  have hw := chan_33_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86847 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((133 / 2 : ℝ) / (86847 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((133 / 2 : ℝ) / (86847 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `33`: the cap. -/
theorem chan_33_cap : (504 / 1000000 : ℝ) ≤ 2 / (133 / 2 : ℝ) - 2 * (133 / 2 : ℝ) / ((133 / 2 : ℝ) ^ 2 + (86847 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `34`: the rational witness inequality. -/
theorem chan_34_witness : (86951 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((137 / 2 : ℝ) / (86951 / 10000 : ℝ))) - (1 / ((137 / 2 : ℝ) / (86951 / 10000 : ℝ)))^3/3 + (1 / ((137 / 2 : ℝ) / (86951 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `34`: the pole-free condition. -/
theorem chan_34 : (86951 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((137 / 2 : ℝ) / (86951 / 10000 : ℝ)) := by
  have hw := chan_34_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (86951 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((137 / 2 : ℝ) / (86951 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((137 / 2 : ℝ) / (86951 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `34`: the cap. -/
theorem chan_34_cap : (462 / 1000000 : ℝ) ≤ 2 / (137 / 2 : ℝ) - 2 * (137 / 2 : ℝ) / ((137 / 2 : ℝ) ^ 2 + (86951 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `35`: the rational witness inequality. -/
theorem chan_35_witness : (87050 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((141 / 2 : ℝ) / (87050 / 10000 : ℝ))) - (1 / ((141 / 2 : ℝ) / (87050 / 10000 : ℝ)))^3/3 + (1 / ((141 / 2 : ℝ) / (87050 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `35`: the pole-free condition. -/
theorem chan_35 : (87050 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((141 / 2 : ℝ) / (87050 / 10000 : ℝ)) := by
  have hw := chan_35_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87050 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((141 / 2 : ℝ) / (87050 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((141 / 2 : ℝ) / (87050 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `35`: the cap. -/
theorem chan_35_cap : (426 / 1000000 : ℝ) ≤ 2 / (141 / 2 : ℝ) - 2 * (141 / 2 : ℝ) / ((141 / 2 : ℝ) ^ 2 + (87050 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `36`: the rational witness inequality. -/
theorem chan_36_witness : (87143 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((145 / 2 : ℝ) / (87143 / 10000 : ℝ))) - (1 / ((145 / 2 : ℝ) / (87143 / 10000 : ℝ)))^3/3 + (1 / ((145 / 2 : ℝ) / (87143 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `36`: the pole-free condition. -/
theorem chan_36 : (87143 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((145 / 2 : ℝ) / (87143 / 10000 : ℝ)) := by
  have hw := chan_36_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87143 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((145 / 2 : ℝ) / (87143 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((145 / 2 : ℝ) / (87143 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `36`: the cap. -/
theorem chan_36_cap : (392 / 1000000 : ℝ) ≤ 2 / (145 / 2 : ℝ) - 2 * (145 / 2 : ℝ) / ((145 / 2 : ℝ) ^ 2 + (87143 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `37`: the rational witness inequality. -/
theorem chan_37_witness : (87231 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((149 / 2 : ℝ) / (87231 / 10000 : ℝ))) - (1 / ((149 / 2 : ℝ) / (87231 / 10000 : ℝ)))^3/3 + (1 / ((149 / 2 : ℝ) / (87231 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `37`: the pole-free condition. -/
theorem chan_37 : (87231 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((149 / 2 : ℝ) / (87231 / 10000 : ℝ)) := by
  have hw := chan_37_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87231 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((149 / 2 : ℝ) / (87231 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((149 / 2 : ℝ) / (87231 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `37`: the cap. -/
theorem chan_37_cap : (363 / 1000000 : ℝ) ≤ 2 / (149 / 2 : ℝ) - 2 * (149 / 2 : ℝ) / ((149 / 2 : ℝ) ^ 2 + (87231 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `38`: the rational witness inequality. -/
theorem chan_38_witness : (87316 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((153 / 2 : ℝ) / (87316 / 10000 : ℝ))) - (1 / ((153 / 2 : ℝ) / (87316 / 10000 : ℝ)))^3/3 + (1 / ((153 / 2 : ℝ) / (87316 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `38`: the pole-free condition. -/
theorem chan_38 : (87316 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((153 / 2 : ℝ) / (87316 / 10000 : ℝ)) := by
  have hw := chan_38_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87316 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((153 / 2 : ℝ) / (87316 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((153 / 2 : ℝ) / (87316 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `38`: the cap. -/
theorem chan_38_cap : (336 / 1000000 : ℝ) ≤ 2 / (153 / 2 : ℝ) - 2 * (153 / 2 : ℝ) / ((153 / 2 : ℝ) ^ 2 + (87316 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `39`: the rational witness inequality. -/
theorem chan_39_witness : (87396 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((157 / 2 : ℝ) / (87396 / 10000 : ℝ))) - (1 / ((157 / 2 : ℝ) / (87396 / 10000 : ℝ)))^3/3 + (1 / ((157 / 2 : ℝ) / (87396 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `39`: the pole-free condition. -/
theorem chan_39 : (87396 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((157 / 2 : ℝ) / (87396 / 10000 : ℝ)) := by
  have hw := chan_39_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87396 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((157 / 2 : ℝ) / (87396 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((157 / 2 : ℝ) / (87396 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `39`: the cap. -/
theorem chan_39_cap : (311 / 1000000 : ℝ) ≤ 2 / (157 / 2 : ℝ) - 2 * (157 / 2 : ℝ) / ((157 / 2 : ℝ) ^ 2 + (87396 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `40`: the rational witness inequality. -/
theorem chan_40_witness : (87472 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((161 / 2 : ℝ) / (87472 / 10000 : ℝ))) - (1 / ((161 / 2 : ℝ) / (87472 / 10000 : ℝ)))^3/3 + (1 / ((161 / 2 : ℝ) / (87472 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `40`: the pole-free condition. -/
theorem chan_40 : (87472 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((161 / 2 : ℝ) / (87472 / 10000 : ℝ)) := by
  have hw := chan_40_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87472 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((161 / 2 : ℝ) / (87472 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((161 / 2 : ℝ) / (87472 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `40`: the cap. -/
theorem chan_40_cap : (289 / 1000000 : ℝ) ≤ 2 / (161 / 2 : ℝ) - 2 * (161 / 2 : ℝ) / ((161 / 2 : ℝ) ^ 2 + (87472 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `41`: the rational witness inequality. -/
theorem chan_41_witness : (87544 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((165 / 2 : ℝ) / (87544 / 10000 : ℝ))) - (1 / ((165 / 2 : ℝ) / (87544 / 10000 : ℝ)))^3/3 + (1 / ((165 / 2 : ℝ) / (87544 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `41`: the pole-free condition. -/
theorem chan_41 : (87544 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((165 / 2 : ℝ) / (87544 / 10000 : ℝ)) := by
  have hw := chan_41_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87544 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((165 / 2 : ℝ) / (87544 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((165 / 2 : ℝ) / (87544 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `41`: the cap. -/
theorem chan_41_cap : (269 / 1000000 : ℝ) ≤ 2 / (165 / 2 : ℝ) - 2 * (165 / 2 : ℝ) / ((165 / 2 : ℝ) ^ 2 + (87544 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `42`: the rational witness inequality. -/
theorem chan_42_witness : (87614 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((169 / 2 : ℝ) / (87614 / 10000 : ℝ))) - (1 / ((169 / 2 : ℝ) / (87614 / 10000 : ℝ)))^3/3 + (1 / ((169 / 2 : ℝ) / (87614 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `42`: the pole-free condition. -/
theorem chan_42 : (87614 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((169 / 2 : ℝ) / (87614 / 10000 : ℝ)) := by
  have hw := chan_42_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87614 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((169 / 2 : ℝ) / (87614 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((169 / 2 : ℝ) / (87614 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `42`: the cap. -/
theorem chan_42_cap : (251 / 1000000 : ℝ) ≤ 2 / (169 / 2 : ℝ) - 2 * (169 / 2 : ℝ) / ((169 / 2 : ℝ) ^ 2 + (87614 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `43`: the rational witness inequality. -/
theorem chan_43_witness : (87680 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((173 / 2 : ℝ) / (87680 / 10000 : ℝ))) - (1 / ((173 / 2 : ℝ) / (87680 / 10000 : ℝ)))^3/3 + (1 / ((173 / 2 : ℝ) / (87680 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `43`: the pole-free condition. -/
theorem chan_43 : (87680 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((173 / 2 : ℝ) / (87680 / 10000 : ℝ)) := by
  have hw := chan_43_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87680 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((173 / 2 : ℝ) / (87680 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((173 / 2 : ℝ) / (87680 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `43`: the cap. -/
theorem chan_43_cap : (235 / 1000000 : ℝ) ≤ 2 / (173 / 2 : ℝ) - 2 * (173 / 2 : ℝ) / ((173 / 2 : ℝ) ^ 2 + (87680 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `44`: the rational witness inequality. -/
theorem chan_44_witness : (87744 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((177 / 2 : ℝ) / (87744 / 10000 : ℝ))) - (1 / ((177 / 2 : ℝ) / (87744 / 10000 : ℝ)))^3/3 + (1 / ((177 / 2 : ℝ) / (87744 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `44`: the pole-free condition. -/
theorem chan_44 : (87744 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((177 / 2 : ℝ) / (87744 / 10000 : ℝ)) := by
  have hw := chan_44_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87744 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((177 / 2 : ℝ) / (87744 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((177 / 2 : ℝ) / (87744 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `44`: the cap. -/
theorem chan_44_cap : (219 / 1000000 : ℝ) ≤ 2 / (177 / 2 : ℝ) - 2 * (177 / 2 : ℝ) / ((177 / 2 : ℝ) ^ 2 + (87744 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `45`: the rational witness inequality. -/
theorem chan_45_witness : (87804 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((181 / 2 : ℝ) / (87804 / 10000 : ℝ))) - (1 / ((181 / 2 : ℝ) / (87804 / 10000 : ℝ)))^3/3 + (1 / ((181 / 2 : ℝ) / (87804 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `45`: the pole-free condition. -/
theorem chan_45 : (87804 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((181 / 2 : ℝ) / (87804 / 10000 : ℝ)) := by
  have hw := chan_45_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87804 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((181 / 2 : ℝ) / (87804 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((181 / 2 : ℝ) / (87804 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `45`: the cap. -/
theorem chan_45_cap : (206 / 1000000 : ℝ) ≤ 2 / (181 / 2 : ℝ) - 2 * (181 / 2 : ℝ) / ((181 / 2 : ℝ) ^ 2 + (87804 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `46`: the rational witness inequality. -/
theorem chan_46_witness : (87863 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((185 / 2 : ℝ) / (87863 / 10000 : ℝ))) - (1 / ((185 / 2 : ℝ) / (87863 / 10000 : ℝ)))^3/3 + (1 / ((185 / 2 : ℝ) / (87863 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `46`: the pole-free condition. -/
theorem chan_46 : (87863 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((185 / 2 : ℝ) / (87863 / 10000 : ℝ)) := by
  have hw := chan_46_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87863 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((185 / 2 : ℝ) / (87863 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((185 / 2 : ℝ) / (87863 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `46`: the cap. -/
theorem chan_46_cap : (193 / 1000000 : ℝ) ≤ 2 / (185 / 2 : ℝ) - 2 * (185 / 2 : ℝ) / ((185 / 2 : ℝ) ^ 2 + (87863 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `47`: the rational witness inequality. -/
theorem chan_47_witness : (87918 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((189 / 2 : ℝ) / (87918 / 10000 : ℝ))) - (1 / ((189 / 2 : ℝ) / (87918 / 10000 : ℝ)))^3/3 + (1 / ((189 / 2 : ℝ) / (87918 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `47`: the pole-free condition. -/
theorem chan_47 : (87918 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((189 / 2 : ℝ) / (87918 / 10000 : ℝ)) := by
  have hw := chan_47_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87918 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((189 / 2 : ℝ) / (87918 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((189 / 2 : ℝ) / (87918 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `47`: the cap. -/
theorem chan_47_cap : (181 / 1000000 : ℝ) ≤ 2 / (189 / 2 : ℝ) - 2 * (189 / 2 : ℝ) / ((189 / 2 : ℝ) ^ 2 + (87918 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `48`: the rational witness inequality. -/
theorem chan_48_witness : (87972 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((193 / 2 : ℝ) / (87972 / 10000 : ℝ))) - (1 / ((193 / 2 : ℝ) / (87972 / 10000 : ℝ)))^3/3 + (1 / ((193 / 2 : ℝ) / (87972 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `48`: the pole-free condition. -/
theorem chan_48 : (87972 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((193 / 2 : ℝ) / (87972 / 10000 : ℝ)) := by
  have hw := chan_48_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (87972 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((193 / 2 : ℝ) / (87972 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((193 / 2 : ℝ) / (87972 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `48`: the cap. -/
theorem chan_48_cap : (170 / 1000000 : ℝ) ≤ 2 / (193 / 2 : ℝ) - 2 * (193 / 2 : ℝ) / ((193 / 2 : ℝ) ^ 2 + (87972 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `49`: the rational witness inequality. -/
theorem chan_49_witness : (88024 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((197 / 2 : ℝ) / (88024 / 10000 : ℝ))) - (1 / ((197 / 2 : ℝ) / (88024 / 10000 : ℝ)))^3/3 + (1 / ((197 / 2 : ℝ) / (88024 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `49`: the pole-free condition. -/
theorem chan_49 : (88024 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((197 / 2 : ℝ) / (88024 / 10000 : ℝ)) := by
  have hw := chan_49_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88024 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((197 / 2 : ℝ) / (88024 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((197 / 2 : ℝ) / (88024 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `49`: the cap. -/
theorem chan_49_cap : (160 / 1000000 : ℝ) ≤ 2 / (197 / 2 : ℝ) - 2 * (197 / 2 : ℝ) / ((197 / 2 : ℝ) ^ 2 + (88024 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `50`: the rational witness inequality. -/
theorem chan_50_witness : (88073 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((201 / 2 : ℝ) / (88073 / 10000 : ℝ))) - (1 / ((201 / 2 : ℝ) / (88073 / 10000 : ℝ)))^3/3 + (1 / ((201 / 2 : ℝ) / (88073 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `50`: the pole-free condition. -/
theorem chan_50 : (88073 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((201 / 2 : ℝ) / (88073 / 10000 : ℝ)) := by
  have hw := chan_50_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88073 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((201 / 2 : ℝ) / (88073 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((201 / 2 : ℝ) / (88073 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `50`: the cap. -/
theorem chan_50_cap : (151 / 1000000 : ℝ) ≤ 2 / (201 / 2 : ℝ) - 2 * (201 / 2 : ℝ) / ((201 / 2 : ℝ) ^ 2 + (88073 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `51`: the rational witness inequality. -/
theorem chan_51_witness : (88121 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((205 / 2 : ℝ) / (88121 / 10000 : ℝ))) - (1 / ((205 / 2 : ℝ) / (88121 / 10000 : ℝ)))^3/3 + (1 / ((205 / 2 : ℝ) / (88121 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `51`: the pole-free condition. -/
theorem chan_51 : (88121 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((205 / 2 : ℝ) / (88121 / 10000 : ℝ)) := by
  have hw := chan_51_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88121 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((205 / 2 : ℝ) / (88121 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((205 / 2 : ℝ) / (88121 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `51`: the cap. -/
theorem chan_51_cap : (143 / 1000000 : ℝ) ≤ 2 / (205 / 2 : ℝ) - 2 * (205 / 2 : ℝ) / ((205 / 2 : ℝ) ^ 2 + (88121 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `52`: the rational witness inequality. -/
theorem chan_52_witness : (88167 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((209 / 2 : ℝ) / (88167 / 10000 : ℝ))) - (1 / ((209 / 2 : ℝ) / (88167 / 10000 : ℝ)))^3/3 + (1 / ((209 / 2 : ℝ) / (88167 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `52`: the pole-free condition. -/
theorem chan_52 : (88167 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((209 / 2 : ℝ) / (88167 / 10000 : ℝ)) := by
  have hw := chan_52_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88167 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((209 / 2 : ℝ) / (88167 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((209 / 2 : ℝ) / (88167 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `52`: the cap. -/
theorem chan_52_cap : (135 / 1000000 : ℝ) ≤ 2 / (209 / 2 : ℝ) - 2 * (209 / 2 : ℝ) / ((209 / 2 : ℝ) ^ 2 + (88167 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `53`: the rational witness inequality. -/
theorem chan_53_witness : (88211 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((213 / 2 : ℝ) / (88211 / 10000 : ℝ))) - (1 / ((213 / 2 : ℝ) / (88211 / 10000 : ℝ)))^3/3 + (1 / ((213 / 2 : ℝ) / (88211 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `53`: the pole-free condition. -/
theorem chan_53 : (88211 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((213 / 2 : ℝ) / (88211 / 10000 : ℝ)) := by
  have hw := chan_53_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88211 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((213 / 2 : ℝ) / (88211 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((213 / 2 : ℝ) / (88211 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `53`: the cap. -/
theorem chan_53_cap : (127 / 1000000 : ℝ) ≤ 2 / (213 / 2 : ℝ) - 2 * (213 / 2 : ℝ) / ((213 / 2 : ℝ) ^ 2 + (88211 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `54`: the rational witness inequality. -/
theorem chan_54_witness : (88254 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((217 / 2 : ℝ) / (88254 / 10000 : ℝ))) - (1 / ((217 / 2 : ℝ) / (88254 / 10000 : ℝ)))^3/3 + (1 / ((217 / 2 : ℝ) / (88254 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `54`: the pole-free condition. -/
theorem chan_54 : (88254 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((217 / 2 : ℝ) / (88254 / 10000 : ℝ)) := by
  have hw := chan_54_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88254 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((217 / 2 : ℝ) / (88254 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((217 / 2 : ℝ) / (88254 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `54`: the cap. -/
theorem chan_54_cap : (121 / 1000000 : ℝ) ≤ 2 / (217 / 2 : ℝ) - 2 * (217 / 2 : ℝ) / ((217 / 2 : ℝ) ^ 2 + (88254 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `55`: the rational witness inequality. -/
theorem chan_55_witness : (88295 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((221 / 2 : ℝ) / (88295 / 10000 : ℝ))) - (1 / ((221 / 2 : ℝ) / (88295 / 10000 : ℝ)))^3/3 + (1 / ((221 / 2 : ℝ) / (88295 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `55`: the pole-free condition. -/
theorem chan_55 : (88295 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((221 / 2 : ℝ) / (88295 / 10000 : ℝ)) := by
  have hw := chan_55_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88295 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((221 / 2 : ℝ) / (88295 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((221 / 2 : ℝ) / (88295 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `55`: the cap. -/
theorem chan_55_cap : (114 / 1000000 : ℝ) ≤ 2 / (221 / 2 : ℝ) - 2 * (221 / 2 : ℝ) / ((221 / 2 : ℝ) ^ 2 + (88295 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `56`: the rational witness inequality. -/
theorem chan_56_witness : (88334 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((225 / 2 : ℝ) / (88334 / 10000 : ℝ))) - (1 / ((225 / 2 : ℝ) / (88334 / 10000 : ℝ)))^3/3 + (1 / ((225 / 2 : ℝ) / (88334 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `56`: the pole-free condition. -/
theorem chan_56 : (88334 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((225 / 2 : ℝ) / (88334 / 10000 : ℝ)) := by
  have hw := chan_56_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88334 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((225 / 2 : ℝ) / (88334 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((225 / 2 : ℝ) / (88334 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `56`: the cap. -/
theorem chan_56_cap : (108 / 1000000 : ℝ) ≤ 2 / (225 / 2 : ℝ) - 2 * (225 / 2 : ℝ) / ((225 / 2 : ℝ) ^ 2 + (88334 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `57`: the rational witness inequality. -/
theorem chan_57_witness : (88373 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((229 / 2 : ℝ) / (88373 / 10000 : ℝ))) - (1 / ((229 / 2 : ℝ) / (88373 / 10000 : ℝ)))^3/3 + (1 / ((229 / 2 : ℝ) / (88373 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `57`: the pole-free condition. -/
theorem chan_57 : (88373 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((229 / 2 : ℝ) / (88373 / 10000 : ℝ)) := by
  have hw := chan_57_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88373 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((229 / 2 : ℝ) / (88373 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((229 / 2 : ℝ) / (88373 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `57`: the cap. -/
theorem chan_57_cap : (103 / 1000000 : ℝ) ≤ 2 / (229 / 2 : ℝ) - 2 * (229 / 2 : ℝ) / ((229 / 2 : ℝ) ^ 2 + (88373 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `58`: the rational witness inequality. -/
theorem chan_58_witness : (88410 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((233 / 2 : ℝ) / (88410 / 10000 : ℝ))) - (1 / ((233 / 2 : ℝ) / (88410 / 10000 : ℝ)))^3/3 + (1 / ((233 / 2 : ℝ) / (88410 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `58`: the pole-free condition. -/
theorem chan_58 : (88410 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((233 / 2 : ℝ) / (88410 / 10000 : ℝ)) := by
  have hw := chan_58_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88410 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((233 / 2 : ℝ) / (88410 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((233 / 2 : ℝ) / (88410 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `58`: the cap. -/
theorem chan_58_cap : (98 / 1000000 : ℝ) ≤ 2 / (233 / 2 : ℝ) - 2 * (233 / 2 : ℝ) / ((233 / 2 : ℝ) ^ 2 + (88410 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `59`: the rational witness inequality. -/
theorem chan_59_witness : (88446 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((237 / 2 : ℝ) / (88446 / 10000 : ℝ))) - (1 / ((237 / 2 : ℝ) / (88446 / 10000 : ℝ)))^3/3 + (1 / ((237 / 2 : ℝ) / (88446 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `59`: the pole-free condition. -/
theorem chan_59 : (88446 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((237 / 2 : ℝ) / (88446 / 10000 : ℝ)) := by
  have hw := chan_59_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88446 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((237 / 2 : ℝ) / (88446 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((237 / 2 : ℝ) / (88446 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `59`: the cap. -/
theorem chan_59_cap : (93 / 1000000 : ℝ) ≤ 2 / (237 / 2 : ℝ) - 2 * (237 / 2 : ℝ) / ((237 / 2 : ℝ) ^ 2 + (88446 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `60`: the rational witness inequality. -/
theorem chan_60_witness : (88481 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((241 / 2 : ℝ) / (88481 / 10000 : ℝ))) - (1 / ((241 / 2 : ℝ) / (88481 / 10000 : ℝ)))^3/3 + (1 / ((241 / 2 : ℝ) / (88481 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `60`: the pole-free condition. -/
theorem chan_60 : (88481 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((241 / 2 : ℝ) / (88481 / 10000 : ℝ)) := by
  have hw := chan_60_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88481 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((241 / 2 : ℝ) / (88481 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((241 / 2 : ℝ) / (88481 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `60`: the cap. -/
theorem chan_60_cap : (89 / 1000000 : ℝ) ≤ 2 / (241 / 2 : ℝ) - 2 * (241 / 2 : ℝ) / ((241 / 2 : ℝ) ^ 2 + (88481 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `61`: the rational witness inequality. -/
theorem chan_61_witness : (88514 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((245 / 2 : ℝ) / (88514 / 10000 : ℝ))) - (1 / ((245 / 2 : ℝ) / (88514 / 10000 : ℝ)))^3/3 + (1 / ((245 / 2 : ℝ) / (88514 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `61`: the pole-free condition. -/
theorem chan_61 : (88514 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((245 / 2 : ℝ) / (88514 / 10000 : ℝ)) := by
  have hw := chan_61_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88514 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((245 / 2 : ℝ) / (88514 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((245 / 2 : ℝ) / (88514 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `61`: the cap. -/
theorem chan_61_cap : (84 / 1000000 : ℝ) ≤ 2 / (245 / 2 : ℝ) - 2 * (245 / 2 : ℝ) / ((245 / 2 : ℝ) ^ 2 + (88514 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `62`: the rational witness inequality. -/
theorem chan_62_witness : (88547 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((249 / 2 : ℝ) / (88547 / 10000 : ℝ))) - (1 / ((249 / 2 : ℝ) / (88547 / 10000 : ℝ)))^3/3 + (1 / ((249 / 2 : ℝ) / (88547 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `62`: the pole-free condition. -/
theorem chan_62 : (88547 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((249 / 2 : ℝ) / (88547 / 10000 : ℝ)) := by
  have hw := chan_62_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88547 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((249 / 2 : ℝ) / (88547 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((249 / 2 : ℝ) / (88547 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `62`: the cap. -/
theorem chan_62_cap : (80 / 1000000 : ℝ) ≤ 2 / (249 / 2 : ℝ) - 2 * (249 / 2 : ℝ) / ((249 / 2 : ℝ) ^ 2 + (88547 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `63`: the rational witness inequality. -/
theorem chan_63_witness : (88578 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((253 / 2 : ℝ) / (88578 / 10000 : ℝ))) - (1 / ((253 / 2 : ℝ) / (88578 / 10000 : ℝ)))^3/3 + (1 / ((253 / 2 : ℝ) / (88578 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `63`: the pole-free condition. -/
theorem chan_63 : (88578 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((253 / 2 : ℝ) / (88578 / 10000 : ℝ)) := by
  have hw := chan_63_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88578 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((253 / 2 : ℝ) / (88578 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((253 / 2 : ℝ) / (88578 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `63`: the cap. -/
theorem chan_63_cap : (77 / 1000000 : ℝ) ≤ 2 / (253 / 2 : ℝ) - 2 * (253 / 2 : ℝ) / ((253 / 2 : ℝ) ^ 2 + (88578 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `64`: the rational witness inequality. -/
theorem chan_64_witness : (88609 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((257 / 2 : ℝ) / (88609 / 10000 : ℝ))) - (1 / ((257 / 2 : ℝ) / (88609 / 10000 : ℝ)))^3/3 + (1 / ((257 / 2 : ℝ) / (88609 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `64`: the pole-free condition. -/
theorem chan_64 : (88609 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((257 / 2 : ℝ) / (88609 / 10000 : ℝ)) := by
  have hw := chan_64_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88609 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((257 / 2 : ℝ) / (88609 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((257 / 2 : ℝ) / (88609 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `64`: the cap. -/
theorem chan_64_cap : (73 / 1000000 : ℝ) ≤ 2 / (257 / 2 : ℝ) - 2 * (257 / 2 : ℝ) / ((257 / 2 : ℝ) ^ 2 + (88609 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `65`: the rational witness inequality. -/
theorem chan_65_witness : (88639 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((261 / 2 : ℝ) / (88639 / 10000 : ℝ))) - (1 / ((261 / 2 : ℝ) / (88639 / 10000 : ℝ)))^3/3 + (1 / ((261 / 2 : ℝ) / (88639 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `65`: the pole-free condition. -/
theorem chan_65 : (88639 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((261 / 2 : ℝ) / (88639 / 10000 : ℝ)) := by
  have hw := chan_65_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88639 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((261 / 2 : ℝ) / (88639 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((261 / 2 : ℝ) / (88639 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `65`: the cap. -/
theorem chan_65_cap : (70 / 1000000 : ℝ) ≤ 2 / (261 / 2 : ℝ) - 2 * (261 / 2 : ℝ) / ((261 / 2 : ℝ) ^ 2 + (88639 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `66`: the rational witness inequality. -/
theorem chan_66_witness : (88668 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((265 / 2 : ℝ) / (88668 / 10000 : ℝ))) - (1 / ((265 / 2 : ℝ) / (88668 / 10000 : ℝ)))^3/3 + (1 / ((265 / 2 : ℝ) / (88668 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `66`: the pole-free condition. -/
theorem chan_66 : (88668 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((265 / 2 : ℝ) / (88668 / 10000 : ℝ)) := by
  have hw := chan_66_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88668 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((265 / 2 : ℝ) / (88668 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((265 / 2 : ℝ) / (88668 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `66`: the cap. -/
theorem chan_66_cap : (67 / 1000000 : ℝ) ≤ 2 / (265 / 2 : ℝ) - 2 * (265 / 2 : ℝ) / ((265 / 2 : ℝ) ^ 2 + (88668 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `67`: the rational witness inequality. -/
theorem chan_67_witness : (88696 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((269 / 2 : ℝ) / (88696 / 10000 : ℝ))) - (1 / ((269 / 2 : ℝ) / (88696 / 10000 : ℝ)))^3/3 + (1 / ((269 / 2 : ℝ) / (88696 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `67`: the pole-free condition. -/
theorem chan_67 : (88696 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((269 / 2 : ℝ) / (88696 / 10000 : ℝ)) := by
  have hw := chan_67_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88696 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((269 / 2 : ℝ) / (88696 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((269 / 2 : ℝ) / (88696 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `67`: the cap. -/
theorem chan_67_cap : (64 / 1000000 : ℝ) ≤ 2 / (269 / 2 : ℝ) - 2 * (269 / 2 : ℝ) / ((269 / 2 : ℝ) ^ 2 + (88696 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `68`: the rational witness inequality. -/
theorem chan_68_witness : (88723 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((273 / 2 : ℝ) / (88723 / 10000 : ℝ))) - (1 / ((273 / 2 : ℝ) / (88723 / 10000 : ℝ)))^3/3 + (1 / ((273 / 2 : ℝ) / (88723 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `68`: the pole-free condition. -/
theorem chan_68 : (88723 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((273 / 2 : ℝ) / (88723 / 10000 : ℝ)) := by
  have hw := chan_68_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88723 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((273 / 2 : ℝ) / (88723 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((273 / 2 : ℝ) / (88723 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `68`: the cap. -/
theorem chan_68_cap : (61 / 1000000 : ℝ) ≤ 2 / (273 / 2 : ℝ) - 2 * (273 / 2 : ℝ) / ((273 / 2 : ℝ) ^ 2 + (88723 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `69`: the rational witness inequality. -/
theorem chan_69_witness : (88749 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((277 / 2 : ℝ) / (88749 / 10000 : ℝ))) - (1 / ((277 / 2 : ℝ) / (88749 / 10000 : ℝ)))^3/3 + (1 / ((277 / 2 : ℝ) / (88749 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `69`: the pole-free condition. -/
theorem chan_69 : (88749 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((277 / 2 : ℝ) / (88749 / 10000 : ℝ)) := by
  have hw := chan_69_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88749 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((277 / 2 : ℝ) / (88749 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((277 / 2 : ℝ) / (88749 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `69`: the cap. -/
theorem chan_69_cap : (59 / 1000000 : ℝ) ≤ 2 / (277 / 2 : ℝ) - 2 * (277 / 2 : ℝ) / ((277 / 2 : ℝ) ^ 2 + (88749 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `70`: the rational witness inequality. -/
theorem chan_70_witness : (88775 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((281 / 2 : ℝ) / (88775 / 10000 : ℝ))) - (1 / ((281 / 2 : ℝ) / (88775 / 10000 : ℝ)))^3/3 + (1 / ((281 / 2 : ℝ) / (88775 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `70`: the pole-free condition. -/
theorem chan_70 : (88775 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((281 / 2 : ℝ) / (88775 / 10000 : ℝ)) := by
  have hw := chan_70_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88775 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((281 / 2 : ℝ) / (88775 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((281 / 2 : ℝ) / (88775 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `70`: the cap. -/
theorem chan_70_cap : (56 / 1000000 : ℝ) ≤ 2 / (281 / 2 : ℝ) - 2 * (281 / 2 : ℝ) / ((281 / 2 : ℝ) ^ 2 + (88775 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `71`: the rational witness inequality. -/
theorem chan_71_witness : (88800 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((285 / 2 : ℝ) / (88800 / 10000 : ℝ))) - (1 / ((285 / 2 : ℝ) / (88800 / 10000 : ℝ)))^3/3 + (1 / ((285 / 2 : ℝ) / (88800 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `71`: the pole-free condition. -/
theorem chan_71 : (88800 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((285 / 2 : ℝ) / (88800 / 10000 : ℝ)) := by
  have hw := chan_71_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88800 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((285 / 2 : ℝ) / (88800 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((285 / 2 : ℝ) / (88800 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `71`: the cap. -/
theorem chan_71_cap : (54 / 1000000 : ℝ) ≤ 2 / (285 / 2 : ℝ) - 2 * (285 / 2 : ℝ) / ((285 / 2 : ℝ) ^ 2 + (88800 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `72`: the rational witness inequality. -/
theorem chan_72_witness : (88824 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((289 / 2 : ℝ) / (88824 / 10000 : ℝ))) - (1 / ((289 / 2 : ℝ) / (88824 / 10000 : ℝ)))^3/3 + (1 / ((289 / 2 : ℝ) / (88824 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `72`: the pole-free condition. -/
theorem chan_72 : (88824 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((289 / 2 : ℝ) / (88824 / 10000 : ℝ)) := by
  have hw := chan_72_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88824 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((289 / 2 : ℝ) / (88824 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((289 / 2 : ℝ) / (88824 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `72`: the cap. -/
theorem chan_72_cap : (52 / 1000000 : ℝ) ≤ 2 / (289 / 2 : ℝ) - 2 * (289 / 2 : ℝ) / ((289 / 2 : ℝ) ^ 2 + (88824 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `73`: the rational witness inequality. -/
theorem chan_73_witness : (88848 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((293 / 2 : ℝ) / (88848 / 10000 : ℝ))) - (1 / ((293 / 2 : ℝ) / (88848 / 10000 : ℝ)))^3/3 + (1 / ((293 / 2 : ℝ) / (88848 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `73`: the pole-free condition. -/
theorem chan_73 : (88848 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((293 / 2 : ℝ) / (88848 / 10000 : ℝ)) := by
  have hw := chan_73_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88848 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((293 / 2 : ℝ) / (88848 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((293 / 2 : ℝ) / (88848 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `73`: the cap. -/
theorem chan_73_cap : (50 / 1000000 : ℝ) ≤ 2 / (293 / 2 : ℝ) - 2 * (293 / 2 : ℝ) / ((293 / 2 : ℝ) ^ 2 + (88848 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `74`: the rational witness inequality. -/
theorem chan_74_witness : (88871 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((297 / 2 : ℝ) / (88871 / 10000 : ℝ))) - (1 / ((297 / 2 : ℝ) / (88871 / 10000 : ℝ)))^3/3 + (1 / ((297 / 2 : ℝ) / (88871 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `74`: the pole-free condition. -/
theorem chan_74 : (88871 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((297 / 2 : ℝ) / (88871 / 10000 : ℝ)) := by
  have hw := chan_74_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88871 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((297 / 2 : ℝ) / (88871 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((297 / 2 : ℝ) / (88871 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `74`: the cap. -/
theorem chan_74_cap : (48 / 1000000 : ℝ) ≤ 2 / (297 / 2 : ℝ) - 2 * (297 / 2 : ℝ) / ((297 / 2 : ℝ) ^ 2 + (88871 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `75`: the rational witness inequality. -/
theorem chan_75_witness : (88893 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((301 / 2 : ℝ) / (88893 / 10000 : ℝ))) - (1 / ((301 / 2 : ℝ) / (88893 / 10000 : ℝ)))^3/3 + (1 / ((301 / 2 : ℝ) / (88893 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `75`: the pole-free condition. -/
theorem chan_75 : (88893 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((301 / 2 : ℝ) / (88893 / 10000 : ℝ)) := by
  have hw := chan_75_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88893 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((301 / 2 : ℝ) / (88893 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((301 / 2 : ℝ) / (88893 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `75`: the cap. -/
theorem chan_75_cap : (46 / 1000000 : ℝ) ≤ 2 / (301 / 2 : ℝ) - 2 * (301 / 2 : ℝ) / ((301 / 2 : ℝ) ^ 2 + (88893 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `76`: the rational witness inequality. -/
theorem chan_76_witness : (88915 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((305 / 2 : ℝ) / (88915 / 10000 : ℝ))) - (1 / ((305 / 2 : ℝ) / (88915 / 10000 : ℝ)))^3/3 + (1 / ((305 / 2 : ℝ) / (88915 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `76`: the pole-free condition. -/
theorem chan_76 : (88915 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((305 / 2 : ℝ) / (88915 / 10000 : ℝ)) := by
  have hw := chan_76_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88915 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((305 / 2 : ℝ) / (88915 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((305 / 2 : ℝ) / (88915 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `76`: the cap. -/
theorem chan_76_cap : (44 / 1000000 : ℝ) ≤ 2 / (305 / 2 : ℝ) - 2 * (305 / 2 : ℝ) / ((305 / 2 : ℝ) ^ 2 + (88915 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `77`: the rational witness inequality. -/
theorem chan_77_witness : (88937 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((309 / 2 : ℝ) / (88937 / 10000 : ℝ))) - (1 / ((309 / 2 : ℝ) / (88937 / 10000 : ℝ)))^3/3 + (1 / ((309 / 2 : ℝ) / (88937 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `77`: the pole-free condition. -/
theorem chan_77 : (88937 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((309 / 2 : ℝ) / (88937 / 10000 : ℝ)) := by
  have hw := chan_77_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88937 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((309 / 2 : ℝ) / (88937 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((309 / 2 : ℝ) / (88937 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `77`: the cap. -/
theorem chan_77_cap : (42 / 1000000 : ℝ) ≤ 2 / (309 / 2 : ℝ) - 2 * (309 / 2 : ℝ) / ((309 / 2 : ℝ) ^ 2 + (88937 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `78`: the rational witness inequality. -/
theorem chan_78_witness : (88957 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((313 / 2 : ℝ) / (88957 / 10000 : ℝ))) - (1 / ((313 / 2 : ℝ) / (88957 / 10000 : ℝ)))^3/3 + (1 / ((313 / 2 : ℝ) / (88957 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `78`: the pole-free condition. -/
theorem chan_78 : (88957 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((313 / 2 : ℝ) / (88957 / 10000 : ℝ)) := by
  have hw := chan_78_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88957 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((313 / 2 : ℝ) / (88957 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((313 / 2 : ℝ) / (88957 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `78`: the cap. -/
theorem chan_78_cap : (41 / 1000000 : ℝ) ≤ 2 / (313 / 2 : ℝ) - 2 * (313 / 2 : ℝ) / ((313 / 2 : ℝ) ^ 2 + (88957 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `79`: the rational witness inequality. -/
theorem chan_79_witness : (88978 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((317 / 2 : ℝ) / (88978 / 10000 : ℝ))) - (1 / ((317 / 2 : ℝ) / (88978 / 10000 : ℝ)))^3/3 + (1 / ((317 / 2 : ℝ) / (88978 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `79`: the pole-free condition. -/
theorem chan_79 : (88978 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((317 / 2 : ℝ) / (88978 / 10000 : ℝ)) := by
  have hw := chan_79_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88978 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((317 / 2 : ℝ) / (88978 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((317 / 2 : ℝ) / (88978 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `79`: the cap. -/
theorem chan_79_cap : (39 / 1000000 : ℝ) ≤ 2 / (317 / 2 : ℝ) - 2 * (317 / 2 : ℝ) / ((317 / 2 : ℝ) ^ 2 + (88978 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `80`: the rational witness inequality. -/
theorem chan_80_witness : (88997 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((321 / 2 : ℝ) / (88997 / 10000 : ℝ))) - (1 / ((321 / 2 : ℝ) / (88997 / 10000 : ℝ)))^3/3 + (1 / ((321 / 2 : ℝ) / (88997 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `80`: the pole-free condition. -/
theorem chan_80 : (88997 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((321 / 2 : ℝ) / (88997 / 10000 : ℝ)) := by
  have hw := chan_80_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (88997 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((321 / 2 : ℝ) / (88997 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((321 / 2 : ℝ) / (88997 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `80`: the cap. -/
theorem chan_80_cap : (38 / 1000000 : ℝ) ≤ 2 / (321 / 2 : ℝ) - 2 * (321 / 2 : ℝ) / ((321 / 2 : ℝ) ^ 2 + (88997 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `81`: the rational witness inequality. -/
theorem chan_81_witness : (89017 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((325 / 2 : ℝ) / (89017 / 10000 : ℝ))) - (1 / ((325 / 2 : ℝ) / (89017 / 10000 : ℝ)))^3/3 + (1 / ((325 / 2 : ℝ) / (89017 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `81`: the pole-free condition. -/
theorem chan_81 : (89017 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((325 / 2 : ℝ) / (89017 / 10000 : ℝ)) := by
  have hw := chan_81_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89017 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((325 / 2 : ℝ) / (89017 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((325 / 2 : ℝ) / (89017 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `81`: the cap. -/
theorem chan_81_cap : (36 / 1000000 : ℝ) ≤ 2 / (325 / 2 : ℝ) - 2 * (325 / 2 : ℝ) / ((325 / 2 : ℝ) ^ 2 + (89017 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `82`: the rational witness inequality. -/
theorem chan_82_witness : (89036 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((329 / 2 : ℝ) / (89036 / 10000 : ℝ))) - (1 / ((329 / 2 : ℝ) / (89036 / 10000 : ℝ)))^3/3 + (1 / ((329 / 2 : ℝ) / (89036 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `82`: the pole-free condition. -/
theorem chan_82 : (89036 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((329 / 2 : ℝ) / (89036 / 10000 : ℝ)) := by
  have hw := chan_82_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89036 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((329 / 2 : ℝ) / (89036 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((329 / 2 : ℝ) / (89036 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `82`: the cap. -/
theorem chan_82_cap : (35 / 1000000 : ℝ) ≤ 2 / (329 / 2 : ℝ) - 2 * (329 / 2 : ℝ) / ((329 / 2 : ℝ) ^ 2 + (89036 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `83`: the rational witness inequality. -/
theorem chan_83_witness : (89054 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((333 / 2 : ℝ) / (89054 / 10000 : ℝ))) - (1 / ((333 / 2 : ℝ) / (89054 / 10000 : ℝ)))^3/3 + (1 / ((333 / 2 : ℝ) / (89054 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `83`: the pole-free condition. -/
theorem chan_83 : (89054 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((333 / 2 : ℝ) / (89054 / 10000 : ℝ)) := by
  have hw := chan_83_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89054 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((333 / 2 : ℝ) / (89054 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((333 / 2 : ℝ) / (89054 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `83`: the cap. -/
theorem chan_83_cap : (34 / 1000000 : ℝ) ≤ 2 / (333 / 2 : ℝ) - 2 * (333 / 2 : ℝ) / ((333 / 2 : ℝ) ^ 2 + (89054 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `84`: the rational witness inequality. -/
theorem chan_84_witness : (89072 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((337 / 2 : ℝ) / (89072 / 10000 : ℝ))) - (1 / ((337 / 2 : ℝ) / (89072 / 10000 : ℝ)))^3/3 + (1 / ((337 / 2 : ℝ) / (89072 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `84`: the pole-free condition. -/
theorem chan_84 : (89072 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((337 / 2 : ℝ) / (89072 / 10000 : ℝ)) := by
  have hw := chan_84_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89072 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((337 / 2 : ℝ) / (89072 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((337 / 2 : ℝ) / (89072 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `84`: the cap. -/
theorem chan_84_cap : (33 / 1000000 : ℝ) ≤ 2 / (337 / 2 : ℝ) - 2 * (337 / 2 : ℝ) / ((337 / 2 : ℝ) ^ 2 + (89072 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `85`: the rational witness inequality. -/
theorem chan_85_witness : (89090 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((341 / 2 : ℝ) / (89090 / 10000 : ℝ))) - (1 / ((341 / 2 : ℝ) / (89090 / 10000 : ℝ)))^3/3 + (1 / ((341 / 2 : ℝ) / (89090 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `85`: the pole-free condition. -/
theorem chan_85 : (89090 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((341 / 2 : ℝ) / (89090 / 10000 : ℝ)) := by
  have hw := chan_85_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89090 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((341 / 2 : ℝ) / (89090 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((341 / 2 : ℝ) / (89090 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `85`: the cap. -/
theorem chan_85_cap : (31 / 1000000 : ℝ) ≤ 2 / (341 / 2 : ℝ) - 2 * (341 / 2 : ℝ) / ((341 / 2 : ℝ) ^ 2 + (89090 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `86`: the rational witness inequality. -/
theorem chan_86_witness : (89107 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((345 / 2 : ℝ) / (89107 / 10000 : ℝ))) - (1 / ((345 / 2 : ℝ) / (89107 / 10000 : ℝ)))^3/3 + (1 / ((345 / 2 : ℝ) / (89107 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `86`: the pole-free condition. -/
theorem chan_86 : (89107 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((345 / 2 : ℝ) / (89107 / 10000 : ℝ)) := by
  have hw := chan_86_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89107 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((345 / 2 : ℝ) / (89107 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((345 / 2 : ℝ) / (89107 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `86`: the cap. -/
theorem chan_86_cap : (30 / 1000000 : ℝ) ≤ 2 / (345 / 2 : ℝ) - 2 * (345 / 2 : ℝ) / ((345 / 2 : ℝ) ^ 2 + (89107 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `87`: the rational witness inequality. -/
theorem chan_87_witness : (89123 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((349 / 2 : ℝ) / (89123 / 10000 : ℝ))) - (1 / ((349 / 2 : ℝ) / (89123 / 10000 : ℝ)))^3/3 + (1 / ((349 / 2 : ℝ) / (89123 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `87`: the pole-free condition. -/
theorem chan_87 : (89123 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((349 / 2 : ℝ) / (89123 / 10000 : ℝ)) := by
  have hw := chan_87_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89123 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((349 / 2 : ℝ) / (89123 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((349 / 2 : ℝ) / (89123 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `87`: the cap. -/
theorem chan_87_cap : (29 / 1000000 : ℝ) ≤ 2 / (349 / 2 : ℝ) - 2 * (349 / 2 : ℝ) / ((349 / 2 : ℝ) ^ 2 + (89123 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `88`: the rational witness inequality. -/
theorem chan_88_witness : (89140 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((353 / 2 : ℝ) / (89140 / 10000 : ℝ))) - (1 / ((353 / 2 : ℝ) / (89140 / 10000 : ℝ)))^3/3 + (1 / ((353 / 2 : ℝ) / (89140 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `88`: the pole-free condition. -/
theorem chan_88 : (89140 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((353 / 2 : ℝ) / (89140 / 10000 : ℝ)) := by
  have hw := chan_88_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89140 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((353 / 2 : ℝ) / (89140 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((353 / 2 : ℝ) / (89140 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `88`: the cap. -/
theorem chan_88_cap : (28 / 1000000 : ℝ) ≤ 2 / (353 / 2 : ℝ) - 2 * (353 / 2 : ℝ) / ((353 / 2 : ℝ) ^ 2 + (89140 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `89`: the rational witness inequality. -/
theorem chan_89_witness : (89156 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((357 / 2 : ℝ) / (89156 / 10000 : ℝ))) - (1 / ((357 / 2 : ℝ) / (89156 / 10000 : ℝ)))^3/3 + (1 / ((357 / 2 : ℝ) / (89156 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `89`: the pole-free condition. -/
theorem chan_89 : (89156 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((357 / 2 : ℝ) / (89156 / 10000 : ℝ)) := by
  have hw := chan_89_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89156 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((357 / 2 : ℝ) / (89156 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((357 / 2 : ℝ) / (89156 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `89`: the cap. -/
theorem chan_89_cap : (27 / 1000000 : ℝ) ≤ 2 / (357 / 2 : ℝ) - 2 * (357 / 2 : ℝ) / ((357 / 2 : ℝ) ^ 2 + (89156 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `90`: the rational witness inequality. -/
theorem chan_90_witness : (89172 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((361 / 2 : ℝ) / (89172 / 10000 : ℝ))) - (1 / ((361 / 2 : ℝ) / (89172 / 10000 : ℝ)))^3/3 + (1 / ((361 / 2 : ℝ) / (89172 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `90`: the pole-free condition. -/
theorem chan_90 : (89172 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((361 / 2 : ℝ) / (89172 / 10000 : ℝ)) := by
  have hw := chan_90_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89172 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((361 / 2 : ℝ) / (89172 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((361 / 2 : ℝ) / (89172 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `90`: the cap. -/
theorem chan_90_cap : (26 / 1000000 : ℝ) ≤ 2 / (361 / 2 : ℝ) - 2 * (361 / 2 : ℝ) / ((361 / 2 : ℝ) ^ 2 + (89172 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `91`: the rational witness inequality. -/
theorem chan_91_witness : (89187 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((365 / 2 : ℝ) / (89187 / 10000 : ℝ))) - (1 / ((365 / 2 : ℝ) / (89187 / 10000 : ℝ)))^3/3 + (1 / ((365 / 2 : ℝ) / (89187 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `91`: the pole-free condition. -/
theorem chan_91 : (89187 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((365 / 2 : ℝ) / (89187 / 10000 : ℝ)) := by
  have hw := chan_91_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89187 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((365 / 2 : ℝ) / (89187 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((365 / 2 : ℝ) / (89187 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `91`: the cap. -/
theorem chan_91_cap : (26 / 1000000 : ℝ) ≤ 2 / (365 / 2 : ℝ) - 2 * (365 / 2 : ℝ) / ((365 / 2 : ℝ) ^ 2 + (89187 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `92`: the rational witness inequality. -/
theorem chan_92_witness : (89202 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((369 / 2 : ℝ) / (89202 / 10000 : ℝ))) - (1 / ((369 / 2 : ℝ) / (89202 / 10000 : ℝ)))^3/3 + (1 / ((369 / 2 : ℝ) / (89202 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `92`: the pole-free condition. -/
theorem chan_92 : (89202 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((369 / 2 : ℝ) / (89202 / 10000 : ℝ)) := by
  have hw := chan_92_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89202 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((369 / 2 : ℝ) / (89202 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((369 / 2 : ℝ) / (89202 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `92`: the cap. -/
theorem chan_92_cap : (25 / 1000000 : ℝ) ≤ 2 / (369 / 2 : ℝ) - 2 * (369 / 2 : ℝ) / ((369 / 2 : ℝ) ^ 2 + (89202 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `93`: the rational witness inequality. -/
theorem chan_93_witness : (89217 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((373 / 2 : ℝ) / (89217 / 10000 : ℝ))) - (1 / ((373 / 2 : ℝ) / (89217 / 10000 : ℝ)))^3/3 + (1 / ((373 / 2 : ℝ) / (89217 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `93`: the pole-free condition. -/
theorem chan_93 : (89217 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((373 / 2 : ℝ) / (89217 / 10000 : ℝ)) := by
  have hw := chan_93_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89217 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((373 / 2 : ℝ) / (89217 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((373 / 2 : ℝ) / (89217 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `93`: the cap. -/
theorem chan_93_cap : (24 / 1000000 : ℝ) ≤ 2 / (373 / 2 : ℝ) - 2 * (373 / 2 : ℝ) / ((373 / 2 : ℝ) ^ 2 + (89217 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `94`: the rational witness inequality. -/
theorem chan_94_witness : (89231 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((377 / 2 : ℝ) / (89231 / 10000 : ℝ))) - (1 / ((377 / 2 : ℝ) / (89231 / 10000 : ℝ)))^3/3 + (1 / ((377 / 2 : ℝ) / (89231 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `94`: the pole-free condition. -/
theorem chan_94 : (89231 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((377 / 2 : ℝ) / (89231 / 10000 : ℝ)) := by
  have hw := chan_94_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89231 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((377 / 2 : ℝ) / (89231 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((377 / 2 : ℝ) / (89231 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `94`: the cap. -/
theorem chan_94_cap : (23 / 1000000 : ℝ) ≤ 2 / (377 / 2 : ℝ) - 2 * (377 / 2 : ℝ) / ((377 / 2 : ℝ) ^ 2 + (89231 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `95`: the rational witness inequality. -/
theorem chan_95_witness : (89245 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((381 / 2 : ℝ) / (89245 / 10000 : ℝ))) - (1 / ((381 / 2 : ℝ) / (89245 / 10000 : ℝ)))^3/3 + (1 / ((381 / 2 : ℝ) / (89245 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `95`: the pole-free condition. -/
theorem chan_95 : (89245 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((381 / 2 : ℝ) / (89245 / 10000 : ℝ)) := by
  have hw := chan_95_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89245 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((381 / 2 : ℝ) / (89245 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((381 / 2 : ℝ) / (89245 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `95`: the cap. -/
theorem chan_95_cap : (22 / 1000000 : ℝ) ≤ 2 / (381 / 2 : ℝ) - 2 * (381 / 2 : ℝ) / ((381 / 2 : ℝ) ^ 2 + (89245 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `96`: the rational witness inequality. -/
theorem chan_96_witness : (89259 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((385 / 2 : ℝ) / (89259 / 10000 : ℝ))) - (1 / ((385 / 2 : ℝ) / (89259 / 10000 : ℝ)))^3/3 + (1 / ((385 / 2 : ℝ) / (89259 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `96`: the pole-free condition. -/
theorem chan_96 : (89259 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((385 / 2 : ℝ) / (89259 / 10000 : ℝ)) := by
  have hw := chan_96_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89259 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((385 / 2 : ℝ) / (89259 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((385 / 2 : ℝ) / (89259 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `96`: the cap. -/
theorem chan_96_cap : (22 / 1000000 : ℝ) ≤ 2 / (385 / 2 : ℝ) - 2 * (385 / 2 : ℝ) / ((385 / 2 : ℝ) ^ 2 + (89259 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `97`: the rational witness inequality. -/
theorem chan_97_witness : (89273 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((389 / 2 : ℝ) / (89273 / 10000 : ℝ))) - (1 / ((389 / 2 : ℝ) / (89273 / 10000 : ℝ)))^3/3 + (1 / ((389 / 2 : ℝ) / (89273 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `97`: the pole-free condition. -/
theorem chan_97 : (89273 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((389 / 2 : ℝ) / (89273 / 10000 : ℝ)) := by
  have hw := chan_97_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89273 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((389 / 2 : ℝ) / (89273 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((389 / 2 : ℝ) / (89273 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `97`: the cap. -/
theorem chan_97_cap : (21 / 1000000 : ℝ) ≤ 2 / (389 / 2 : ℝ) - 2 * (389 / 2 : ℝ) / ((389 / 2 : ℝ) ^ 2 + (89273 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `98`: the rational witness inequality. -/
theorem chan_98_witness : (89286 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((393 / 2 : ℝ) / (89286 / 10000 : ℝ))) - (1 / ((393 / 2 : ℝ) / (89286 / 10000 : ℝ)))^3/3 + (1 / ((393 / 2 : ℝ) / (89286 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `98`: the pole-free condition. -/
theorem chan_98 : (89286 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((393 / 2 : ℝ) / (89286 / 10000 : ℝ)) := by
  have hw := chan_98_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89286 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((393 / 2 : ℝ) / (89286 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((393 / 2 : ℝ) / (89286 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `98`: the cap. -/
theorem chan_98_cap : (20 / 1000000 : ℝ) ≤ 2 / (393 / 2 : ℝ) - 2 * (393 / 2 : ℝ) / ((393 / 2 : ℝ) ^ 2 + (89286 / 10000 : ℝ) ^ 2) := by norm_num

/-- Channel `99`: the rational witness inequality. -/
theorem chan_99_witness : (89299 / 10000 : ℝ) * (3465735904 / 10000000000 : ℝ) < (1570796 / 1000000 : ℝ) + (157079632 / 100000000 : ℝ) - ((1 / ((397 / 2 : ℝ) / (89299 / 10000 : ℝ))) - (1 / ((397 / 2 : ℝ) / (89299 / 10000 : ℝ)))^3/3 + (1 / ((397 / 2 : ℝ) / (89299 / 10000 : ℝ)))^5/5) := by norm_num

/-- Channel `99`: the pole-free condition. -/
theorem chan_99 : (89299 / 10000 : ℝ) * (Real.log 2 / 2) < π / 2 + Real.arctan ((397 / 2 : ℝ) / (89299 / 10000 : ℝ)) := by
  have hw := chan_99_witness
  have hl := Cvs.Upstream.ArctanPolynomialBounds.half_log_two_lt
  have hp6 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt6
  have ht : (0:ℝ) < (89299 / 10000 : ℝ) := by norm_num
  have hm := mul_lt_mul_of_pos_left hl ht
  have he := Cvs.Upstream.ArctanPolynomialBounds.arctan_eq_pi2_sub (z := ((397 / 2 : ℝ) / (89299 / 10000 : ℝ))) (by norm_num)
  have ha := Cvs.Upstream.ArctanPolynomialBounds.arctan_le_poly5 (z := (1 / ((397 / 2 : ℝ) / (89299 / 10000 : ℝ)))) (by norm_num)
  have hp8 := Cvs.Upstream.ArctanPolynomialBounds.pi_div_two_gt8
  linarith

/-- Channel `99`: the cap. -/
theorem chan_99_cap : (20 / 1000000 : ℝ) ≤ 2 / (397 / 2 : ℝ) - 2 * (397 / 2 : ℝ) / ((397 / 2 : ℝ) ^ 2 + (89299 / 10000 : ℝ) ^ 2) := by norm_num

end Cvs.StepA.OddChannelCertificatesLogTwo
