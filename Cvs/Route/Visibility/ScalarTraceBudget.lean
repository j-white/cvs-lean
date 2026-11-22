import Mathlib
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The scalar trace budget

With `μ ≤ 7/10`, `a ≤ 5/3` and `0 ≤ T ≤ 9/50`, `2aT/(1 − μT) ≤ 300/437 < 7/10`; `μ* ≤ 7/10`; and the top weight
`2/((1 − λ)λ(1 + √λ)³)` is at most `5/3` for `1/2 ≤ λ ≤ 3/4`.
-/

noncomputable section
open Real
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar)

namespace Cvs.Route.Visibility.ScalarTraceBudget
open Cvs.ZeroCounting

/-- `1 − mT ≥ 437/500` for `m ≤ 7/10` and `0 ≤ T ≤ 9/50`. -/
theorem denominator_ge {m t : ℝ} (hm : m ≤ 7 / 10)
    (ht0 : 0 ≤ t) (ht : t ≤ 9 / 50) :
    437 / 500 ≤ 1 - m * t := by
  have hmt : m * t ≤ (7 / 10 : ℝ) * (9 / 50) := calc
    m * t ≤ (7 / 10 : ℝ) * t := mul_le_mul_of_nonneg_right hm ht0
    _ ≤ (7 / 10 : ℝ) * (9 / 50) := mul_le_mul_of_nonneg_left ht (by norm_num)
  linarith

/-- `2aT/(1 − mT) ≤ 300/437` for `m ≤ 7/10`, `a ≤ 5/3` and `0 ≤ T ≤ 9/50`. -/
theorem excess_le {m a t : ℝ} (hm : m ≤ 7 / 10)
    (ha : a ≤ 5 / 3) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 50) :
    2 * a * t / (1 - m * t) ≤ 300 / 437 := by
  have hd := denominator_ge hm ht0 ht
  have hdp : 0 < 1 - m * t := by linarith
  have hat : a * t ≤ (5 / 3 : ℝ) * (9 / 50) := calc
    a * t ≤ (5 / 3 : ℝ) * t := mul_le_mul_of_nonneg_right ha ht0
    _ ≤ (5 / 3 : ℝ) * (9 / 50) := mul_le_mul_of_nonneg_left ht (by norm_num)
  apply (div_le_iff₀ hdp).2
  nlinarith

/-- `μ* = 12 − 8√2 ≤ 7/10`. -/
theorem muStar_le_seven_tenths : muStar ≤ (7 / 10 : ℝ) := by
  have hs : (113 / 80 : ℝ) < √2 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  unfold muStar
  linarith

/-- `2aT/(1 − μ*T) < 7/10` for `a ≤ 5/3` and `0 ≤ T ≤ 9/50`. -/
theorem prolate_excess_lt_seven_tenths {a t : ℝ}
    (ha : a ≤ 5 / 3) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 50) :
    2 * a * t / (1 - muStar * t) < 7 / 10 := by
  exact lt_of_le_of_lt (excess_le muStar_le_seven_tenths ha ht0 ht) (by norm_num)

/-- `(1 − l)l(1 + √l)³ ≥ 6/5` for `1/2 ≤ l ≤ 3/4`. -/
theorem six_fifths_le {l : ℝ} (h1 : 1 / 2 ≤ l) (h2 : l ≤ 3 / 4) : 6 / 5 ≤ (1 - l) * l * (1 + √l) ^ 3 := by
  have hs := Real.sq_sqrt (show 0 ≤ l by linarith)
  have hs0 := Real.sqrt_nonneg l
  set s := √l
  have hlo : 7 / 10 ≤ s := by nlinarith
  have hhi : s ≤ 87 / 100 := by nlinarith
  rw [← hs]
  nlinarith [mul_nonneg (sub_nonneg.2 hlo) (sub_nonneg.2 hhi), mul_nonneg (mul_nonneg (sub_nonneg.2 hlo)
    (sub_nonneg.2 hhi)) hs0, mul_nonneg (mul_nonneg (sub_nonneg.2 hlo) (sub_nonneg.2 hhi)) (sq_nonneg s)]

/-- `2/((1 − l)l(1 + √l)³) ≤ 5/3` for `1/2 ≤ l ≤ 3/4`. -/
theorem topWeight_le {l : ℝ} (h1 : 1 / 2 ≤ l) (h2 : l ≤ 3 / 4) : 2 / ((1 - l) * l * (1 + √l) ^ 3) ≤ 5 / 3 := by
  have h := six_fifths_le h1 h2
  rw [div_le_iff₀ (by linarith)]
  linarith

end Cvs.Route.Visibility.ScalarTraceBudget

end
