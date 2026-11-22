import Mathlib
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
# The Liouville–Green factors at `ξ₀ = 1 + 1/(c² − χ)`, for `ℓc² ≤ c² − χ`, `ℓc ≥ 100`

With `D = c² − χ`, `e = 1/D`, `X = c²e ≤ 1/ℓ`: `pq = 2 + e + eX(2 + e)²` and `d = 2(1 + e)(q + 2X + Xe)` exactly, so
`2 ≤ pq ≤ 3`, `7/5 ≤ a ≤ 2` and `0 < w ≤ 1`; hence `fac ≤ 3e`, the lower factor is at least `1/(3e)`, and `EdgeValueSoninBound`'s edge
constant `fac/(a(1 − pq/4)) ≤ 12e`, for every `χ ≤ (1 − ℓ)c²`.
-/

namespace Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge

open Real Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {c χ ℓ : ℝ}

/-- The sizes behind the factors: `e = 1/D ≤ 10⁻⁴`, `eD = 1`, `X = c²e`, `eX ≤ 10⁻⁴`, `X ≤ 10⁻⁴ D`. -/
theorem sizes (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) :
    let D := c ^ 2 - χ
    let e := 1 / D
    0 < D ∧ e * D = 1 ∧ 0 < e ∧ e ≤ 1 / 10000 ∧ e * (c ^ 2 * e) ≤ 1 / 10000 ∧ c ^ 2 * e ≤ D / 10000
      ∧ 10000 ≤ D := by
  intro D e
  have hc0 : 0 < c := by
    by_contra h; push Not at h
    have : ℓ * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hℓ0.le h
    linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hℓ1 : ℓ ≤ 1 := by
    have : ℓ * c ^ 2 ≤ 1 * c ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hc2
  have hc : 100 ≤ c := by nlinarith
  have hD : 100 * c ≤ D := by nlinarith
  have hD4 : 10000 ≤ D := by nlinarith
  have hD0 : 0 < D := by linarith
  have heD : e * D = 1 := by simp only [e]; field_simp
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 10000 := by
    simp only [e]; rw [div_le_div_iff₀ hD0 (by norm_num)]; linarith
  -- `ℓ²c² ≥ 10⁴` and `c²/D ≤ 1/ℓ`
  have hℓ2 : 10000 ≤ (ℓ * c) ^ 2 := by nlinarith
  have hX : c ^ 2 * e ≤ D / 10000 := by
    simp only [e]
    rw [mul_one_div, div_le_div_iff₀ hD0 (by norm_num)]
    nlinarith
  have heX : e * (c ^ 2 * e) ≤ 1 / 10000 := by
    have : e * (c ^ 2 * e) ≤ e * (D / 10000) := mul_le_mul_of_nonneg_left hX he0.le
    have e2 : e * (D / 10000) = 1 / 10000 := by rw [← mul_div_assoc, heD]
    linarith
  exact ⟨hD0, heD, he0, he1, heX, hX, hD4⟩

theorem pq_eq (hD : 0 < c ^ 2 - χ) :
    pP (1 + 1 / (c ^ 2 - χ)) * qP c χ (1 + 1 / (c ^ 2 - χ))
      = 2 + 1 / (c ^ 2 - χ) + 1 / (c ^ 2 - χ) * (c ^ 2 * (1 / (c ^ 2 - χ))) * (2 + 1 / (c ^ 2 - χ)) ^ 2 := by
  unfold pP qP; field_simp; ring

theorem pq_bounds (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) :
    2 ≤ pP (1 + 1 / (c ^ 2 - χ)) * qP c χ (1 + 1 / (c ^ 2 - χ))
      ∧ pP (1 + 1 / (c ^ 2 - χ)) * qP c χ (1 + 1 / (c ^ 2 - χ)) ≤ 3 := by
  obtain ⟨hD0, heD, he0, he1, heX, hX, hD4⟩ := sizes (c := c) (χ := χ) hℓ0 hχ0 hσ hℓc
  rw [pq_eq hD0]
  set e := 1 / (c ^ 2 - χ)
  have hX0 : 0 ≤ e * (c ^ 2 * e) := by positivity
  constructor
  · nlinarith [sq_nonneg (2 + e)]
  · have : (2 + e) ^ 2 ≤ 5 := by nlinarith
    nlinarith

theorem a_bounds (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) :
    7 / 5 ≤ aP c χ (1 + 1 / (c ^ 2 - χ)) ∧ aP c χ (1 + 1 / (c ^ 2 - χ)) ≤ 2 := by
  obtain ⟨h1, h2⟩ := pq_bounds hℓ0 hχ0 hσ hℓc
  unfold aP
  constructor
  · exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [sqrt_le_left (by norm_num)]; linarith

theorem w_le (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) : wP c χ (1 + 1 / (c ^ 2 - χ)) ≤ 1 := by
  obtain ⟨hD0, heD, he0, he1, heX, hX, hD4⟩ := sizes (c := c) (χ := χ) hℓ0 hχ0 hσ hℓc
  obtain ⟨ha1, _⟩ := a_bounds hℓ0 hχ0 hσ hℓc
  set D := c ^ 2 - χ with hDdef
  set e := 1 / D with hedef
  set X := c ^ 2 * e with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hq : qP c χ (1 + e) = D + 2 * X + X * e := by
    simp only [hXdef, hDdef]; unfold qP; ring
  have hd : dP c χ (1 + e) = 2 * (1 + e) * (qP c χ (1 + e) + 2 * X + X * e) := by
    rw [hq]; simp only [hXdef, hDdef]; unfold dP; ring
  have hqD : D ≤ qP c χ (1 + e) := by rw [hq]; nlinarith
  have hq0 : 0 < qP c χ (1 + e) := by linarith
  unfold wP
  rw [div_le_one (mul_pos (mul_pos two_pos hq0) (by linarith)), hd]
  have h3 : 2 * X + X * e ≤ 3 * (D / 10000) := by nlinarith
  have : (1 + e) * (qP c χ (1 + e) + 2 * X + X * e) ≤ 7 / 5 * qP c χ (1 + e) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left ha1 hq0.le]

theorem w_pos (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) : 0 < wP c χ (1 + 1 / (c ^ 2 - χ)) := by
  obtain ⟨hD0, heD, he0, he1, heX, hX, hD4⟩ := sizes (c := c) (χ := χ) hℓ0 hχ0 hσ hℓc
  have hχc : χ < c ^ 2 := by linarith
  have hc2 : 0 < c ^ 2 := by nlinarith
  exact wP_pos (by linarith) hc2 hχc

/-- **The upper energy factor**: `fac ≤ 3e`. -/
theorem fac_le (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) :
    Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ (1 + 1 / (c ^ 2 - χ)) ≤ 3 * exp 1 := by
  have hw1 := w_le hℓ0 hχ0 hσ hℓc
  have hw0 := w_pos hℓ0 hχ0 hσ hℓc
  unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
  set w := wP c χ (1 + 1 / (c ^ 2 - χ))
  have h1 : (1 + w / 2) / (1 - w / 2) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : exp (w / (2 - w)) ≤ exp 1 := exp_le_exp.mpr (by rw [div_le_one (by linarith)]; linarith)
  calc (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w)) ≤ 3 * exp 1 :=
        mul_le_mul h1 h2 (exp_pos _).le (by norm_num)

/-- **The lower energy factor**: `(1 − w/2)/(1 + w/2) e^{−w/(2−w)} ≥ 1/(3e)`. -/
theorem lower_ge (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) :
    1 / (3 * exp 1) ≤ (1 - wP c χ (1 + 1 / (c ^ 2 - χ)) / 2) / (1 + wP c χ (1 + 1 / (c ^ 2 - χ)) / 2)
      * exp (-(wP c χ (1 + 1 / (c ^ 2 - χ)) / (2 - wP c χ (1 + 1 / (c ^ 2 - χ))))) := by
  have hw1 := w_le hℓ0 hχ0 hσ hℓc
  have hw0 := w_pos hℓ0 hχ0 hσ hℓc
  set w := wP c χ (1 + 1 / (c ^ 2 - χ))
  have h1 : 1 / 3 ≤ (1 - w / 2) / (1 + w / 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : exp (-1) ≤ exp (-(w / (2 - w))) := exp_le_exp.mpr (by
    have : w / (2 - w) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith)
  calc 1 / (3 * exp 1) = 1 / 3 * exp (-1) := by rw [exp_neg]; field_simp
    _ ≤ _ := mul_le_mul h1 h2 (exp_pos _).le (by linarith)

/-- **`EdgeValueSoninBound`'s edge constant**: `fac/(a(1 − pq/4)) ≤ 12e`. -/
theorem edge_const_le (hℓ0 : 0 < ℓ) (hχ0 : 0 ≤ χ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hℓc : 100 ≤ ℓ * c) :
    Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ (1 + 1 / (c ^ 2 - χ))
      / (aP c χ (1 + 1 / (c ^ 2 - χ)) * (1 - pP (1 + 1 / (c ^ 2 - χ)) * qP c χ (1 + 1 / (c ^ 2 - χ)) / 4)) ≤ 12 * exp 1 := by
  obtain ⟨hpq1, hpq3⟩ := pq_bounds hℓ0 hχ0 hσ hℓc
  obtain ⟨ha1, _⟩ := a_bounds hℓ0 hχ0 hσ hℓc
  have hf := fac_le hℓ0 hχ0 hσ hℓc
  have hden : 1 / 4 ≤ aP c χ (1 + 1 / (c ^ 2 - χ)) * (1 - pP (1 + 1 / (c ^ 2 - χ)) * qP c χ (1 + 1 / (c ^ 2 - χ)) / 4) := by
    nlinarith
  calc _ ≤ 3 * exp 1 / (1 / 4) := div_le_div₀ (by positivity) hf (by norm_num) hden
    _ = 12 * exp 1 := by ring

end Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge
