import Mathlib
import Cvs.Prolate.Envelope.ProlateWeightSizes
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green factors at `ξ₀ = 1 + 1/c²`, for `c ≥ 100`, `0 ≤ χ ≤ c√c`

There `9/5 ≤ pq ≤ 3`, `13/10 ≤ a ≤ 2` and `0 < w ≤ 1`, so `fac ≤ 3e`, the lower factor
`(1 − w/2)/(1 + w/2) e^{−w/(2−w)} ≥ 1/(3e)`, and `EdgeValueSoninBound`'s edge constant `fac/(a(1 − pq/4)) ≤ 12e`.
-/

namespace Cvs.Prolate.LiouvilleGreen.FactorsNearEdge

open Real Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {c χ : ℝ}

theorem pq_bounds (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) :
    9 / 5 ≤ pP (1 + 1 / c ^ 2) * qP c χ (1 + 1 / c ^ 2) ∧ pP (1 + 1 / c ^ 2) * qP c χ (1 + 1 / c ^ 2) ≤ 3 := by
  have hc0 : 0 < c := by linarith
  have hsc : √c ≤ c / 10 := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  have hχc : χ ≤ c ^ 2 / 10 := by nlinarith [mul_le_mul_of_nonneg_left hsc hc0.le]
  set e := 1 / c ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 10000 := by rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hce : c ^ 2 * e = 1 := by rw [he]; field_simp
  have hp : pP (1 + e) = 2 * e + e ^ 2 := by unfold pP; ring
  have hq : qP c χ (1 + e) = c ^ 2 + 2 + e - χ := by
    unfold qP; have : c ^ 2 * (1 + e) ^ 2 = c ^ 2 + 2 * (c ^ 2 * e) + e * (c ^ 2 * e) := by ring
    rw [this, hce]; ring
  rw [hp, hq]
  constructor
  · -- `q ≥ (9/10) c²`, `p ≥ 2e`
    have h1 : (9 / 10) * c ^ 2 ≤ c ^ 2 + 2 + e - χ := by linarith
    have h2 : 2 * e ≤ 2 * e + e ^ 2 := by nlinarith
    have h3 : 2 * e * ((9 / 10) * c ^ 2) = 9 / 5 := by rw [show 2 * e * ((9 / 10) * c ^ 2) = 9 / 5 * (c ^ 2 * e) by ring, hce]; ring
    nlinarith [mul_le_mul h2 h1 (by positivity) (by positivity)]
  · have h1 : c ^ 2 + 2 + e - χ ≤ c ^ 2 + 3 := by linarith
    have h0 : 0 ≤ c ^ 2 + 2 + e - χ := by linarith
    have e2 : (2 * e + e ^ 2) * (c ^ 2 + 3) = 2 + 6 * e + e + 3 * e ^ 2 := by
      have : (2 * e + e ^ 2) * (c ^ 2 + 3) = 2 * (c ^ 2 * e) + e * (c ^ 2 * e) + 6 * e + 3 * e ^ 2 := by ring
      rw [this, hce]; ring
    calc (2 * e + e ^ 2) * (c ^ 2 + 2 + e - χ) ≤ (2 * e + e ^ 2) * (c ^ 2 + 3) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 + 6 * e + e + 3 * e ^ 2 := e2
      _ ≤ 3 := by nlinarith

theorem a_bounds (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) :
    13 / 10 ≤ aP c χ (1 + 1 / c ^ 2) ∧ aP c χ (1 + 1 / c ^ 2) ≤ 2 := by
  obtain ⟨h1, h2⟩ := pq_bounds hc hχ0 hχs
  unfold aP
  constructor
  · exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [sqrt_le_left (by norm_num)]; linarith

theorem w_le (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : wP c χ (1 + 1 / c ^ 2) ≤ 1 := by
  have hc0 : 0 < c := by linarith
  have hsc : √c ≤ c / 10 := by rw [sqrt_le_left (by positivity)]; nlinarith
  have hχc : χ ≤ c ^ 2 / 10 := by nlinarith [mul_le_mul_of_nonneg_left hsc hc0.le]
  obtain ⟨ha1, _⟩ := a_bounds hc hχ0 hχs
  set e := 1 / c ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 10000 := by rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hce : c ^ 2 * e = 1 := by rw [he]; field_simp
  have hq : qP c χ (1 + e) = c ^ 2 + 2 + e - χ := by
    unfold qP; have : c ^ 2 * (1 + e) ^ 2 = c ^ 2 + 2 * (c ^ 2 * e) + e * (c ^ 2 * e) := by ring
    rw [this, hce]; ring
  have hq9 : (9 / 10) * c ^ 2 ≤ qP c χ (1 + e) := by rw [hq]; linarith
  have hd : dP c χ (1 + e) ≤ 21 / 10 * c ^ 2 := by
    unfold dP
    have : c ^ 2 * (1 + e) ^ 2 = c ^ 2 + 2 + e := by
      have : c ^ 2 * (1 + e) ^ 2 = c ^ 2 + 2 * (c ^ 2 * e) + e * (c ^ 2 * e) := by ring
      rw [this, hce]; ring
    have h2 : 2 * c ^ 2 * (1 + e) ^ 2 - c ^ 2 - χ ≤ c ^ 2 + 5 := by nlinarith
    have h3 : 0 ≤ 2 * c ^ 2 * (1 + e) ^ 2 - c ^ 2 - χ := by nlinarith
    calc 2 * (1 + e) * (2 * c ^ 2 * (1 + e) ^ 2 - c ^ 2 - χ) ≤ 2 * (1 + e) * (c ^ 2 + 5) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 21 / 10 * c ^ 2 := by nlinarith
  have hq0 : 0 < qP c χ (1 + e) := by nlinarith
  unfold wP
  rw [div_le_one (mul_pos (mul_pos two_pos hq0) (by linarith))]
  nlinarith [mul_le_mul hq9 ha1 (by norm_num) hq0.le]

theorem w_pos (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : 0 < wP c χ (1 + 1 / c ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hχc : χ < c ^ 2 := by nlinarith [Cvs.Prolate.Envelope.ProlateWeightSizes.half_sq_le (by linarith : (4 : ℝ) ≤ c) hχ0 hχs]
  have he : 0 < 1 / c ^ 2 := by positivity
  exact wP_pos (by linarith) (by positivity) hχc

/-- **The upper energy factor**: `fac ≤ 3e`. -/
theorem fac_le (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) :
    Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ (1 + 1 / c ^ 2) ≤ 3 * exp 1 := by
  have hw1 := w_le hc hχ0 hχs
  have hw0 := w_pos hc hχ0 hχs
  unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
  set w := wP c χ (1 + 1 / c ^ 2)
  have h1 : (1 + w / 2) / (1 - w / 2) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : exp (w / (2 - w)) ≤ exp 1 := exp_le_exp.mpr (by rw [div_le_one (by linarith)]; linarith)
  calc (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w)) ≤ 3 * exp 1 :=
        mul_le_mul h1 h2 (exp_pos _).le (by norm_num)

/-- **The lower energy factor**: `(1 − w/2)/(1 + w/2) e^{−w/(2−w)} ≥ 1/(3e)`. -/
theorem lower_ge (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) :
    1 / (3 * exp 1) ≤ (1 - wP c χ (1 + 1 / c ^ 2) / 2) / (1 + wP c χ (1 + 1 / c ^ 2) / 2)
      * exp (-(wP c χ (1 + 1 / c ^ 2) / (2 - wP c χ (1 + 1 / c ^ 2)))) := by
  have hw1 := w_le hc hχ0 hχs
  have hw0 := w_pos hc hχ0 hχs
  set w := wP c χ (1 + 1 / c ^ 2)
  have h1 : 1 / 3 ≤ (1 - w / 2) / (1 + w / 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : exp (-1) ≤ exp (-(w / (2 - w))) := exp_le_exp.mpr (by
    have : w / (2 - w) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith)
  calc 1 / (3 * exp 1) = 1 / 3 * exp (-1) := by rw [exp_neg]; field_simp
    _ ≤ _ := mul_le_mul h1 h2 (exp_pos _).le (by linarith)

/-- **`EdgeValueSoninBound`'s edge constant**: `fac/(a(1 − pq/4)) ≤ 12e`. -/
theorem edge_const_le (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) :
    Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ (1 + 1 / c ^ 2)
      / (aP c χ (1 + 1 / c ^ 2) * (1 - pP (1 + 1 / c ^ 2) * qP c χ (1 + 1 / c ^ 2) / 4)) ≤ 12 * exp 1 := by
  obtain ⟨hpq1, hpq3⟩ := pq_bounds hc hχ0 hχs
  obtain ⟨ha1, _⟩ := a_bounds hc hχ0 hχs
  have hf := fac_le hc hχ0 hχs
  have hden : 1 / 4 ≤ aP c χ (1 + 1 / c ^ 2) * (1 - pP (1 + 1 / c ^ 2) * qP c χ (1 + 1 / c ^ 2) / 4) := by
    nlinarith
  calc _ ≤ 3 * exp 1 / (1 / 4) := div_le_div₀ (by positivity) hf (by norm_num) hden
    _ = 12 * exp 1 := by ring

end Cvs.Prolate.LiouvilleGreen.FactorsNearEdge
