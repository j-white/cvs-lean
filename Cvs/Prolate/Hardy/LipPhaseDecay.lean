import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Upstream.NonStationaryPhaseParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The lip phase `φ(x) = x − ½√(x² − ¼)` and the Fourier decay of a lip piece

`φ' = 1 − x/(2√(x² − ¼))` and `φ'' = 1/(8√(x² − ¼)³)` on `x > ½`; if `|cφ' − 2πξ| ≥ κ ≥ cδ` on `[α, β]`, then
`|∫_α^β g e^{±i(cφ − 2πξx)}| ≤ (2G₀ + (β − α)(G₁ + G₀φ''(α)/δ))/κ`; and `∫_{ξ>0} (p + qξ)^{−2} dξ = 1/(pq)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral
open Complex (I)

namespace Cvs.Prolate.Hardy.LipPhaseDecay

/-- The lip phase `φ(x) = x − ½√(x² − ¼)`. -/
def lipPhase (x : ℝ) : ℝ := x - √(x ^ 2 - 1 / 4) / 2

/-- `φ'(x) = 1 − x/(2√(x² − ¼))`. -/
def lipD (x : ℝ) : ℝ := 1 - x / (2 * √(x ^ 2 - 1 / 4))

/-- `φ''(x) = 1/(8√(x² − ¼)³)`. -/
def lipDD (x : ℝ) : ℝ := 1 / (8 * √(x ^ 2 - 1 / 4) ^ 3)

theorem sqrt_pos_of_half_lt {x : ℝ} (hx : 1 / 2 < x) : 0 < √(x ^ 2 - 1 / 4) :=
  Real.sqrt_pos.2 (by nlinarith)

theorem hasDerivAt_sqrt_lip {x : ℝ} (hx : 1 / 2 < x) :
    HasDerivAt (fun x => √(x ^ 2 - 1 / 4)) (x / √(x ^ 2 - 1 / 4)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - 1 / 4) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const (1 / 4)
  have h := h1.sqrt (show x ^ 2 - 1 / 4 ≠ 0 by nlinarith)
  refine h.congr_deriv ?_
  have := (sqrt_pos_of_half_lt hx).ne'
  field_simp

theorem hasDerivAt_lipPhase {x : ℝ} (hx : 1 / 2 < x) : HasDerivAt lipPhase (lipD x) x := by
  have h : HasDerivAt (fun x => x - √(x ^ 2 - 1 / 4) / 2) (1 - x / √(x ^ 2 - 1 / 4) / 2) x :=
    (hasDerivAt_id' x).sub ((hasDerivAt_sqrt_lip hx).div_const 2)
  refine h.congr_deriv ?_
  unfold lipD
  have := (sqrt_pos_of_half_lt hx).ne'
  field_simp

theorem hasDerivAt_lipD {x : ℝ} (hx : 1 / 2 < x) : HasDerivAt lipD (lipDD x) x := by
  have hs := sqrt_pos_of_half_lt hx
  have hd : HasDerivAt (fun x => 2 * √(x ^ 2 - 1 / 4)) (2 * (x / √(x ^ 2 - 1 / 4))) x :=
    (hasDerivAt_sqrt_lip hx).const_mul 2
  have h : HasDerivAt (fun x => 1 - x / (2 * √(x ^ 2 - 1 / 4)))
      (0 - (1 * (2 * √(x ^ 2 - 1 / 4)) - x * (2 * (x / √(x ^ 2 - 1 / 4)))) / (2 * √(x ^ 2 - 1 / 4)) ^ 2) x :=
    (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id' x).div hd (by positivity))
  refine h.congr_deriv ?_
  unfold lipDD
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 1 / 4 by nlinarith)
  generalize √(x ^ 2 - 1 / 4) = S at hsq hs ⊢
  field_simp
  nlinarith [hsq]

theorem continuousOn_lipDD : ContinuousOn lipDD (Ioi (1 / 2)) := by
  intro x hx
  have hs := sqrt_pos_of_half_lt (show 1 / 2 < x from hx)
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun x : ℝ => 8 * √(x ^ 2 - 1 / 4) ^ 3) x :=
    continuousAt_const.mul ((Real.continuous_sqrt.comp (by fun_prop)).continuousAt.pow 3)
  have hne : 8 * √(x ^ 2 - 1 / 4) ^ 3 ≠ 0 := by positivity
  exact continuousAt_const.div hc hne

theorem lipDD_nonneg {x : ℝ} : 0 ≤ lipDD x := by unfold lipDD; positivity

/-- `φ''` decreases: `φ''(x) ≤ φ''(α)` for `½ < α ≤ x`. -/
theorem lipDD_le {α x : ℝ} (hα : 1 / 2 < α) (hx : α ≤ x) : lipDD x ≤ lipDD α := by
  unfold lipDD
  have h1 := sqrt_pos_of_half_lt hα
  have h2 : √(α ^ 2 - 1 / 4) ≤ √(x ^ 2 - 1 / 4) := Real.sqrt_le_sqrt (by nlinarith)
  exact one_div_le_one_div_of_le (by positivity) (by gcongr)

/-- `φ'` increases on `x > ½`: `φ'(x) ≤ φ'(β)` for `½ < x ≤ β`. -/
theorem lipD_le {x β : ℝ} (hx : 1 / 2 < x) (hxβ : x ≤ β) : lipD x ≤ lipD β := by
  unfold lipD
  have h1 := sqrt_pos_of_half_lt hx
  have h2 := sqrt_pos_of_half_lt (lt_of_lt_of_le hx hxβ)
  have key : β / (2 * √(β ^ 2 - 1 / 4)) ≤ x / (2 * √(x ^ 2 - 1 / 4)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hx0 : 0 ≤ x := by linarith
    have hb0 : 0 ≤ β := by linarith
    have e1 : β * √(x ^ 2 - 1 / 4) = √(β ^ 2 * (x ^ 2 - 1 / 4)) := by
      rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hb0]
    have e2 : x * √(β ^ 2 - 1 / 4) = √(x ^ 2 * (β ^ 2 - 1 / 4)) := by
      rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0]
    have : β * √(x ^ 2 - 1 / 4) ≤ x * √(β ^ 2 - 1 / 4) := by
      rw [e1, e2]; exact Real.sqrt_le_sqrt (by nlinarith)
    nlinarith
  linarith

/-- **The Fourier decay of a lip piece**: with `|cφ' − 2πξ| ≥ κ ≥ cδ` on `[α, β]`, `σ = ±1`,
`|∫_α^β g e^{iσ(cφ − 2πξx)}| ≤ (2G₀ + (β − α)(G₁ + G₀φ''(α)/δ))/κ`. -/
theorem norm_lip_le {α β δ c ξ κ G₀ G₁ σ : ℝ} (hσ : |σ| = 1) (hα : 1 / 2 < α) (hαβ : α ≤ β) (hδ : 0 < δ)
    (hc : 0 < c) (hκ : c * δ ≤ κ) (hκx : ∀ x ∈ Icc α β, κ ≤ |c * lipD x - 2 * π * ξ|)
    {g g' : ℝ → ℂ} (hg : ∀ x ∈ Icc α β, HasDerivAt g (g' x) x) (hg' : ContinuousOn g' (Icc α β))
    (hG₀ : ∀ x ∈ Icc α β, ‖g x‖ ≤ G₀) (hG₁ : ∀ x ∈ Icc α β, ‖g' x‖ ≤ G₁) :
    ‖∫ x in α..β, g x * Complex.exp (I * ((σ * (c * lipPhase x - 2 * π * ξ * x) : ℝ) : ℂ))‖ ≤
      (2 * G₀ + (β - α) * (G₁ + G₀ * lipDD α / δ)) / κ := by
  have hκ0 : 0 < κ := lt_of_lt_of_le (mul_pos hc hδ) hκ
  have hmem : ∀ x ∈ Icc α β, 1 / 2 < x := fun x hx => lt_of_lt_of_le hα hx.1
  have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans (hG₀ α ⟨le_rfl, hαβ⟩)
  have h := Cvs.Upstream.NonStationaryPhaseParts.norm_integral_mul_exp_le (D := c * lipDD α) hαβ hκ0 hg hg'
    (Φ := fun x => σ * (c * lipPhase x - 2 * π * ξ * x)) (Φ₁ := fun x => σ * (c * lipD x - 2 * π * ξ))
    (Φ₂ := fun x => σ * (c * lipDD x))
    (fun x hx => by
      have := (((hasDerivAt_lipPhase (hmem x hx)).const_mul c).sub
        ((hasDerivAt_id x).const_mul (2 * π * ξ))).const_mul σ
      simpa using this)
    (fun x hx => by
      have := (((hasDerivAt_lipD (hmem x hx)).const_mul c).sub_const (2 * π * ξ)).const_mul σ
      simpa using this)
    (continuousOn_const.mul (continuousOn_const.mul (continuousOn_lipDD.mono fun x hx => hmem x hx)))
    hG₀ hG₁
    (fun x hx => by rw [abs_mul, hσ, one_mul]; exact hκx x hx)
    (fun x hx => by
      rw [abs_mul, hσ, one_mul, abs_mul, abs_of_pos hc, abs_of_nonneg lipDD_nonneg]
      exact mul_le_mul_of_nonneg_left (lipDD_le hα hx.1) hc.le)
  refine h.trans (le_of_eq_of_le rfl ?_)
  have hD : G₀ * (c * lipDD α) / κ ^ 2 ≤ G₀ * lipDD α / δ / κ := by
    rw [div_div, show G₀ * (c * lipDD α) = c * (G₀ * lipDD α) by ring, sq]
    have hl : 0 ≤ G₀ * lipDD α := mul_nonneg hG0 lipDD_nonneg
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hκ (mul_nonneg hl hκ0.le)
    nlinarith
  have hβα : 0 ≤ β - α := by linarith
  calc 2 * G₀ / κ + (β - α) * (G₁ / κ + G₀ * (c * lipDD α) / κ ^ 2)
      ≤ 2 * G₀ / κ + (β - α) * (G₁ / κ + G₀ * lipDD α / δ / κ) := by gcongr
    _ = (2 * G₀ + (β - α) * (G₁ + G₀ * lipDD α / δ)) / κ := by field_simp

theorem hasDerivAt_inv_lin {p q : ℝ} (hq : 0 < q) {ξ : ℝ} (hξ : 0 < p + q * ξ) :
    HasDerivAt (fun ξ => -1 / (q * (p + q * ξ))) (1 / (p + q * ξ) ^ 2) ξ := by
  have h1 : HasDerivAt (fun ξ => q * (p + q * ξ)) (q * q) ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul q |>.const_add p).const_mul q
  have h2 : HasDerivAt (fun ξ => -1 / (q * (p + q * ξ)))
      ((0 * (q * (p + q * ξ)) - (-1) * (q * q)) / (q * (p + q * ξ)) ^ 2) ξ :=
    (hasDerivAt_const ξ (-1 : ℝ)).div h1 (by positivity)
  refine h2.congr_deriv ?_
  have := hξ.ne'
  field_simp
  ring

theorem tendsto_inv_lin {p q : ℝ} (hq : 0 < q) : Tendsto (fun ξ => -1 / (q * (p + q * ξ))) atTop (𝓝 0) := by
  have : Tendsto (fun ξ => q * (p + q * ξ)) atTop atTop :=
    Tendsto.const_mul_atTop hq (tendsto_atTop_add_const_left _ p (Tendsto.const_mul_atTop hq tendsto_id))
  have h3 := (this.inv_tendsto_atTop).const_mul (-1)
  rw [mul_zero] at h3
  exact h3.congr fun ξ => by simp [div_eq_mul_inv]

theorem integrableOn_inv_sq_Ioi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun ξ => 1 / (p + q * ξ) ^ 2) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun ξ hξ => hasDerivAt_inv_lin hq (by nlinarith [hξ.out]))
    (fun ξ _ => by positivity) (tendsto_inv_lin hq)

/-- `∫_{ξ>0} (p + qξ)^{−2} dξ = 1/(pq)` for `p, q > 0`. -/
theorem integral_inv_sq_Ioi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ ξ in Ioi (0 : ℝ), 1 / (p + q * ξ) ^ 2 = 1 / (p * q) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun ξ hξ => hasDerivAt_inv_lin hq (by nlinarith [hξ.out]))
    (integrableOn_inv_sq_Ioi hp hq) (tendsto_inv_lin hq)]
  simp only [mul_zero, add_zero]
  ring

end Cvs.Prolate.Hardy.LipPhaseDecay

end
