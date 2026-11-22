import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit sup bounds of the project constants

The centred coefficient `q̄(θ) = c²m⁴θ² − m²χ̄` is increasing on `θ ≥ 0`, so on `[α, β]` with `q̄(α) > 0`:
the majorant `W₂ = 2(m²θ² − 1)((π/h)²/q̄ + (2c²m⁴θ)²/q̄³)` is at most its value with `θ = β` in the numerators and
`θ = α` in `q̄`, `1/q̄² ≤ 1/q̄(α)²`, and the centred product `(m²θ² − 1)q̄(θ)` is at most `(m²β² − 1)q̄(β)`: the
constants `A`, `B`, `P` of the project bounds (Cvs.L2a.TreeStepModePair, Cvs.L2a.TreeStepFirstPair) as explicit expressions in `c, m, χ̄, h, α, β`.
-/

namespace Cvs.L2a.TreeConstantSupBounds

open Real Set

/-- The centred coefficient. -/
def qb (c m χb θ : ℝ) : ℝ := c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb

theorem qb_mono {c m χb θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) : qb c m χb θ₁ ≤ qb c m χb θ₂ := by
  unfold qb
  have : θ₁ ^ 2 ≤ θ₂ ^ 2 := pow_le_pow_left₀ h1 h12 2
  have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ c ^ 2 * m ^ 4)
  linarith

/-- **The majorant `W₂` uniformly on `[α, ∞)`**: for `θ ≥ α > 0`, `0 ≤ χ̄ < c²m²α²`, `h > 0`, with `q̂ = c²m² − χ̄/α²`,
`2(m²θ² − 1)((π/h)²/q̄(θ) + (2c²m⁴θ)²/q̄(θ)³) ≤ 2((π/h)²/q̂ + 4c⁴m⁴/(q̂³α²))`. -/
theorem W2_le_uniform {c m χb h α θ : ℝ} (hh : 0 < h) (hα : 0 < α) (hm : 0 < m) (hχb : 0 ≤ χb)
    (hq : χb < c ^ 2 * m ^ 2 * α ^ 2) (hθ : α ≤ θ) :
    2 * (m ^ 2 * θ ^ 2 - 1) * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
        + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3)
      ≤ 2 * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 2 - χb / α ^ 2)
        + 4 * c ^ 4 * m ^ 4 / ((c ^ 2 * m ^ 2 - χb / α ^ 2) ^ 3 * α ^ 2)) := by
  have hθ0 : 0 < θ := hα.trans_le hθ
  have hθ2 : α ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hα.le hθ 2
  have hα2 : 0 < α ^ 2 := by positivity
  set D := c ^ 2 * m ^ 2 * θ ^ 2 - χb with hD
  set qh := c ^ 2 * m ^ 2 - χb / α ^ 2 with hqh
  have hqh0 : 0 < qh := by
    rw [hqh, sub_pos, div_lt_iff₀ hα2]; linarith
  have hDq : qh * θ ^ 2 ≤ D := by
    have h1 : 1 ≤ θ ^ 2 / α ^ 2 := by rw [le_div_iff₀ hα2]; linarith
    have h2 : χb ≤ χb * (θ ^ 2 / α ^ 2) := by nlinarith
    have e : (c ^ 2 * m ^ 2 - χb / α ^ 2) * θ ^ 2 = c ^ 2 * m ^ 2 * θ ^ 2 - χb * (θ ^ 2 / α ^ 2) := by ring
    rw [hqh, hD, e]; linarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDq
  have e1 : c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb = m ^ 2 * D := by rw [hD]; ring
  rw [e1]
  have hm2 : 0 < m ^ 2 := by positivity
  have t1 : (Real.pi / h) ^ 2 / (m ^ 2 * D) * (m ^ 2 * θ ^ 2) ≤ (Real.pi / h) ^ 2 / qh := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hqh0]
    have := mul_le_mul_of_nonneg_left hDq (by positivity : 0 ≤ (Real.pi / h) ^ 2 * m ^ 2)
    nlinarith [this]
  have t2 : (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (m ^ 2 * D) ^ 3 * (m ^ 2 * θ ^ 2)
      ≤ 4 * c ^ 4 * m ^ 4 / (qh ^ 3 * α ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (qh * θ ^ 2) ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ (by positivity) hDq 3
    have h4 : qh ^ 3 * α ^ 2 * θ ^ 4 ≤ (qh * θ ^ 2) ^ 3 := by
      have h5 : α ^ 2 * θ ^ 4 ≤ θ ^ 6 := by
        have := mul_le_mul_of_nonneg_right hθ2 (by positivity : (0:ℝ) ≤ θ ^ 4)
        calc α ^ 2 * θ ^ 4 ≤ θ ^ 2 * θ ^ 4 := this
          _ = θ ^ 6 := by ring
      calc qh ^ 3 * α ^ 2 * θ ^ 4 = qh ^ 3 * (α ^ 2 * θ ^ 4) := by ring
        _ ≤ qh ^ 3 * θ ^ 6 := mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = (qh * θ ^ 2) ^ 3 := by ring
    have h6 := mul_le_mul_of_nonneg_left (h4.trans h3) (by positivity : 0 ≤ 4 * c ^ 4 * m ^ 10)
    nlinarith [h6]
  have hs : 0 ≤ (Real.pi / h) ^ 2 / (m ^ 2 * D) + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (m ^ 2 * D) ^ 3 := by positivity
  calc 2 * (m ^ 2 * θ ^ 2 - 1) * ((Real.pi / h) ^ 2 / (m ^ 2 * D) + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (m ^ 2 * D) ^ 3)
      ≤ 2 * (m ^ 2 * θ ^ 2) * ((Real.pi / h) ^ 2 / (m ^ 2 * D) + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (m ^ 2 * D) ^ 3) := by
        apply mul_le_mul_of_nonneg_right _ hs; linarith
    _ = 2 * ((Real.pi / h) ^ 2 / (m ^ 2 * D) * (m ^ 2 * θ ^ 2)
          + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (m ^ 2 * D) ^ 3 * (m ^ 2 * θ ^ 2)) := by ring
    _ ≤ 2 * ((Real.pi / h) ^ 2 / qh + 4 * c ^ 4 * m ^ 4 / (qh ^ 3 * α ^ 2)) := by
        apply mul_le_mul_of_nonneg_left (add_le_add t1 t2) (by norm_num)

/-- **`1/q̄² ≤ 1/q̄(α)²`** on `[α, β]`. -/
theorem qb_inv_sq_le {c m χb α β θ : ℝ} (hα : 0 < α) (hq : 0 < qb c m χb α) (hθ : θ ∈ Icc α β) :
    1 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 2 ≤ 1 / qb c m χb α ^ 2 := by
  have hqθ : qb c m χb α ≤ qb c m χb θ := qb_mono hα.le hθ.1
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  apply pow_le_pow_left₀ hq.le
  unfold qb at hqθ ⊢; linarith

end Cvs.L2a.TreeConstantSupBounds
