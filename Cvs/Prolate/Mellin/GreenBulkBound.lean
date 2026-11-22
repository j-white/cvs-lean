import Mathlib
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.Prolate.RungConnectionIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bulk bound of Lemma G (Lemma R)

On `ξ ≥ 2` with `w ≤ r c²ξ²`, `r < 1`: `|α| ≤ 2/(c²ξ³(1 − r)²)`, `|β| ≤ (32/9)/(c²ξ³(1 − r)²)`, so
`‖ρ‖² ≤ (1024/81 + 16r/3 + 16/(9c))(1 − r)⁻⁴·E/(c³ξ⁵)`, and `‖∫_s^X ρ‖ ≤ (2/3)√(ρ²Ē/c³)/(s√s)` when `E ≤ Ē`.
-/

namespace Cvs.Prolate.Mellin.GreenBulkBound

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.GreenBoundaryBound

/-- The bulk constant `ρ² = (1024/81 + 16r/3 + 16/(9c))/(1 − r)⁴`. -/
noncomputable def rhoSq (c r : ℝ) : ℝ := (1024 / 81 + 16 / 3 * r + 16 / (9 * c)) / (1 - r) ^ 4

/-- `|α| ≤ 2/(c²ξ³(1 − r)²)` on `ξ ≥ 2` when `w ≤ r c²ξ²`, `r < 1` and `0 ≤ χ ≤ c²`. -/
theorem abs_alphaM_le {c χ r w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hξ : 2 ≤ ξ) (hr : r < 1)
    (hw : w ≤ r * (c ^ 2 * ξ ^ 2)) : |alphaM c χ w ξ| ≤ 2 / (c ^ 2 * ξ ^ 3 * (1 - r) ^ 2) := by
  have hξ0 : 0 < ξ := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hp : 3 / 4 * ξ ^ 2 ≤ pP ξ := by unfold pP; nlinarith
  have hp0 : 0 < pP ξ := lt_of_lt_of_le (by positivity) hp
  have hD : pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ DM c χ w ξ := by
    have h := DM_ge (w := w) hχ (by linarith : (1 : ℝ) ≤ ξ)
    have : pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ pP ξ * (c ^ 2 * ξ ^ 2 - w) := by
      have : c ^ 2 * ξ ^ 2 * (1 - r) ≤ c ^ 2 * ξ ^ 2 - w := by nlinarith
      nlinarith
    linarith
  have hL0 : 0 < pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) := by positivity
  have hD0 : 0 < DM c χ w ξ := lt_of_lt_of_le hL0 hD
  have hnum : |c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)| ≤ c ^ 2 * pP ξ ^ 2 := by
    rw [abs_le]
    have hp1 : 1 ≤ pP ξ := by unfold pP; nlinarith
    have hp2 : 1 ≤ pP ξ ^ 2 := one_le_pow₀ hp1
    have : c ^ 2 ≤ c ^ 2 * pP ξ ^ 2 := le_mul_of_one_le_right (sq_nonneg c) hp2
    constructor <;> nlinarith
  unfold alphaM
  rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hξ0,
    abs_of_pos (pow_pos hD0 2)]
  rw [div_le_div_iff₀ (pow_pos hD0 2) (mul_pos (mul_pos (pow_pos hc 2) (pow_pos hξ0 3)) (pow_pos h1r 2))]
  have hDsq : (pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r)) ^ 2 ≤ DM c χ w ξ ^ 2 := pow_le_pow_left₀ hL0.le hD 2
  calc 2 * ξ * |c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)| * (c ^ 2 * ξ ^ 3 * (1 - r) ^ 2)
      ≤ 2 * ξ * (c ^ 2 * pP ξ ^ 2) * (c ^ 2 * ξ ^ 3 * (1 - r) ^ 2) := by gcongr
    _ = 2 * (pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r)) ^ 2 := by ring
    _ ≤ 2 * DM c χ w ξ ^ 2 := by linarith

/-- `|β| ≤ (32/9)/(c²ξ³(1 − r)²)` on `ξ ≥ 2` when `0 ≤ w ≤ r c²ξ²`, `r < 1`. -/
theorem abs_betaM_le {c χ r w ξ : ℝ} (hc : 0 < c) (hχ : χ ≤ c ^ 2) (hξ : 2 ≤ ξ) (hr : r < 1) (hw0 : 0 ≤ w)
    (hw : w ≤ r * (c ^ 2 * ξ ^ 2)) : |betaM c χ w ξ| ≤ 32 / 9 / (c ^ 2 * ξ ^ 3 * (1 - r) ^ 2) := by
  have hξ0 : 0 < ξ := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hp : 3 / 4 * ξ ^ 2 ≤ pP ξ := by unfold pP; nlinarith
  have hp0 : 0 < pP ξ := lt_of_lt_of_le (by positivity) hp
  have hD : pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ DM c χ w ξ := by
    have h := DM_ge (w := w) hχ (by linarith : (1 : ℝ) ≤ ξ)
    have : pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ pP ξ * (c ^ 2 * ξ ^ 2 - w) := by
      have : c ^ 2 * ξ ^ 2 * (1 - r) ≤ c ^ 2 * ξ ^ 2 - w := by nlinarith
      nlinarith
    linarith
  have hL0 : 0 < pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) := by positivity
  have hD0 : 0 < DM c χ w ξ := lt_of_lt_of_le hL0 hD
  have hr0 : 0 ≤ r := by
    by_contra h; push Not at h
    have : r * (c ^ 2 * ξ ^ 2) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  have hnum : |c ^ 2 * ξ ^ 4 - w| ≤ c ^ 2 * ξ ^ 4 := by
    rw [abs_le]
    have : r * (c ^ 2 * ξ ^ 2) ≤ c ^ 2 * ξ ^ 4 := by
      have h1 : r * (c ^ 2 * ξ ^ 2) ≤ c ^ 2 * ξ ^ 2 := by nlinarith [mul_pos hc hξ0]
      have h2 : c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 4 := by
        have h1 : 1 ≤ ξ ^ 2 := by nlinarith
        have : ξ ^ 2 ≤ ξ ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ξ)]
        exact mul_le_mul_of_nonneg_left this (sq_nonneg c)
      linarith
    constructor <;> nlinarith
  unfold betaM
  rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hξ0,
    abs_of_pos (pow_pos hD0 2)]
  rw [div_le_div_iff₀ (pow_pos hD0 2) (mul_pos (mul_pos (pow_pos hc 2) (pow_pos hξ0 3)) (pow_pos h1r 2))]
  have hDsq : (pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r)) ^ 2 ≤ DM c χ w ξ ^ 2 := pow_le_pow_left₀ hL0.le hD 2
  have hp2 : 9 / 16 * ξ ^ 4 ≤ pP ξ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hp 2; nlinarith
  calc 2 * ξ * |c ^ 2 * ξ ^ 4 - w| * (c ^ 2 * ξ ^ 3 * (1 - r) ^ 2)
      ≤ 2 * ξ * (c ^ 2 * ξ ^ 4) * (c ^ 2 * ξ ^ 3 * (1 - r) ^ 2) := by gcongr
    _ = 32 / 9 * ((9 / 16 * ξ ^ 4) * (c ^ 2 * ξ ^ 2) ^ 2 * (1 - r) ^ 2) := by ring
    _ ≤ 32 / 9 * (pP ξ ^ 2 * (c ^ 2 * ξ ^ 2) ^ 2 * (1 - r) ^ 2) := by gcongr
    _ = 32 / 9 * (pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r)) ^ 2 := by ring
    _ ≤ 32 / 9 * DM c χ w ξ ^ 2 := by gcongr

/-- **Lemma R, pointwise**: for `ξ ≥ 2`, `0 ≤ χ ≤ c²`, `t² + ¼ ≤ r c²ξ²`, `r < 1`: `‖ρ(ξ)‖² ≤ ρ²·E(ξ)/(c³ξ⁵)`. -/
theorem norm_remDens_sq_le {c χ r t ξ : ℝ} (ψ u : ℝ → ℝ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hξ : 2 ≤ ξ) (hr : r < 1) (hw : t ^ 2 + 1 / 4 ≤ r * (c ^ 2 * ξ ^ 2)) :
    ‖remDens c χ t ψ u ξ‖ ^ 2 ≤ rhoSq c r * energy (aP c χ) ψ u ξ / (c ^ 3 * ξ ^ 5) := by
  have hξ0 : 0 < ξ := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hp : 3 / 4 * ξ ^ 2 ≤ pP ξ := by unfold pP; nlinarith
  have haL : c * pP ξ ≤ aP c χ ξ := Cvs.Prolate.RungConnectionIdentity.le_aP_far hχ (by linarith)
  have haU : aP c χ ξ ≤ c * ξ ^ 2 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.aP_le hc hχ0 (by linarith)
  have ha0 : 0 < aP c χ ξ := lt_of_lt_of_le (mul_pos hc (lt_of_lt_of_le (by positivity) hp)) haL
  have hr0 : 0 ≤ r := by
    by_contra h; push Not at h
    have : r * (c ^ 2 * ξ ^ 2) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    nlinarith
  have hA := abs_alphaM_le hc hχ0 hχ hξ hr hw
  have hB := abs_betaM_le hc hχ hξ hr (by positivity) hw
  have h := norm_pair_sq_le t (alphaM c χ (t ^ 2 + 1 / 4) ξ) (betaM c χ (t ^ 2 + 1 / 4) ξ) (ψ := ψ) (u := u) hξ0 ha0
  set A := alphaM c χ (t ^ 2 + 1 / 4) ξ
  set B := betaM c χ (t ^ 2 + 1 / 4) ξ
  set a := aP c χ ξ
  set w := t ^ 2 + 1 / 4
  set K := c ^ 2 * ξ ^ 3 * (1 - r) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  have hwa : ξ * w / a ≤ 4 / 3 * r * c * ξ := by
    rw [div_le_iff₀ ha0]
    have h1 : ξ * w ≤ ξ * (r * (c ^ 2 * ξ ^ 2)) := mul_le_mul_of_nonneg_left hw hξ0.le
    have h2 : 4 / 3 * r * c * ξ * (c * (3 / 4 * ξ ^ 2)) ≤ 4 / 3 * r * c * ξ * a := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith
  have haξ : a / ξ ≤ c * ξ := by rw [div_le_iff₀ hξ0]; nlinarith
  have hA2 : A ^ 2 ≤ (2 / K) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hB2 : B ^ 2 ≤ (32 / 9 / K) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  have t1 : A ^ 2 * (ξ * w) / a ≤ (2 / K) ^ 2 * (4 / 3 * r * c * ξ) := by
    rw [mul_div_assoc]
    exact mul_le_mul hA2 hwa (by positivity) (by positivity)
  have t2 : |A * B| / 2 ≤ (2 / K) * (32 / 9 / K) / 2 := by
    rw [abs_mul]
    have := mul_le_mul hA hB (abs_nonneg _) (by positivity)
    linarith
  have t3 : B ^ 2 * a / ξ ≤ (32 / 9 / K) ^ 2 * (c * ξ) := by
    rw [mul_div_assoc]
    exact mul_le_mul hB2 haξ (by positivity) (by positivity)
  have hsum : (2 / K) ^ 2 * (4 / 3 * r * c * ξ) + (2 / K) * (32 / 9 / K) / 2 + (32 / 9 / K) ^ 2 * (c * ξ)
      ≤ rhoSq c r / (c ^ 3 * ξ ^ 5) := by
    have hc0 : c ≠ 0 := hc.ne'
    have hξ0' : ξ ≠ 0 := hξ0.ne'
    have h1r' : 1 - r ≠ 0 := h1r.ne'
    have e : (2 / K) ^ 2 * (4 / 3 * r * c * ξ) + (2 / K) * (32 / 9 / K) / 2 + (32 / 9 / K) ^ 2 * (c * ξ)
        = (1024 / 81 + 16 / 3 * r + 32 / 9 / (c * ξ)) / (1 - r) ^ 4 / (c ^ 3 * ξ ^ 5) := by
      rw [hK]; field_simp; ring
    rw [e, rhoSq]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 32 / 9 / (c * ξ) ≤ 16 / (9 * c) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy; positivity
  unfold remDens
  calc _ ≤ _ := h
    _ ≤ energy (aP c χ) ψ u ξ * (rhoSq c r / (c ^ 3 * ξ ^ 5)) :=
        mul_le_mul_of_nonneg_left (by linarith) hE0
    _ = _ := by ring

/-- `(−(2/3)(ξ√ξ)⁻¹)′ = 1/(ξ²√ξ)` for `ξ > 0`. -/
theorem hasDerivAt_neg_inv_mul_sqrt {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun x => -(2 / 3) * (x * √x)⁻¹) (1 / (ξ ^ 2 * √ξ)) ξ := by
  have hs : 0 < √ξ := Real.sqrt_pos.mpr hξ
  have h1 : HasDerivAt (fun x => x * √x) (1 * √ξ + ξ * (1 / (2 * √ξ))) ξ :=
    (hasDerivAt_id ξ).mul (Real.hasDerivAt_sqrt hξ.ne')
  have h2 := (h1.inv (by positivity)).const_mul (-(2 / 3 : ℝ))
  refine h2.congr_deriv ?_
  have hss : √ξ * √ξ = ξ := Real.mul_self_sqrt hξ.le
  field_simp
  nlinarith [hss]

/-- `∫_s^X dξ/(ξ²√ξ) ≤ (2/3)/(s√s)` for `0 < s ≤ X`. -/
theorem integral_inv_sq_sqrt_le {s X : ℝ} (hs : 0 < s) (hsX : s ≤ X) :
    ∫ ξ in s..X, 1 / (ξ ^ 2 * √ξ) ≤ 2 / 3 / (s * √s) := by
  have hpos : ∀ x ∈ uIcc s X, 0 < x := fun x hx => by rw [uIcc_of_le hsX] at hx; linarith [hx.1]
  have hc : ContinuousOn (fun ξ : ℝ => 1 / (ξ ^ 2 * √ξ)) (uIcc s X) := by
    refine ContinuousOn.div continuousOn_const ((continuousOn_pow 2).mul continuous_sqrt.continuousOn) ?_
    intro x hx; have := hpos x hx
    exact mul_ne_zero (pow_ne_zero 2 this.ne') (Real.sqrt_pos.mpr this).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_neg_inv_mul_sqrt (hpos x hx))
    (hc.intervalIntegrable)]
  have hX0 : 0 < X := lt_of_lt_of_le hs hsX
  have : 0 ≤ (X * √X)⁻¹ := by positivity
  have e : -(2 / 3) * (X * √X)⁻¹ - -(2 / 3) * (s * √s)⁻¹ = 2 / 3 / (s * √s) - 2 / 3 * (X * √X)⁻¹ := by ring
  rw [e]; linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2 / 3) this]

/-- `ρ² ≥ 0` for `c > 0`, `r ≥ 0`. -/
theorem rhoSq_nonneg {c r : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) : 0 ≤ rhoSq c r := by
  unfold rhoSq; positivity

/-- **Lemma R**: for `2 ≤ s ≤ X`, `t² + ¼ ≤ r c²s²`, `r < 1` and `E ≤ Ē` on `[s, X]`,
`‖∫_s^X ρ‖ ≤ (2/3)√(ρ²Ē/c³)/(s√s)`. -/
theorem green_rem_le {c χ r t s X Ebar : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hs : 2 ≤ s) (hsX : s ≤ X) (hr : r < 1) (hw : t ^ 2 + 1 / 4 ≤ r * (c ^ 2 * s ^ 2))
    (hE : ∀ ξ ∈ Icc s X, energy (aP c χ) ψ u ξ ≤ Ebar) :
    ‖∫ ξ in s..X, remDens c χ t ψ u ξ‖ ≤ 2 / 3 * √(rhoSq c r * Ebar / c ^ 3) / (s * √s) := by
  have hs0 : 0 < s := by linarith
  have hr0 : 0 ≤ r := by
    by_contra h; push Not at h
    have : r * (c ^ 2 * s ^ 2) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    nlinarith
  have hwξ : ∀ ξ ∈ Icc s X, t ^ 2 + 1 / 4 ≤ r * (c ^ 2 * ξ ^ 2) := fun ξ hξ => by
    have : s ^ 2 ≤ ξ ^ 2 := pow_le_pow_left₀ hs0.le hξ.1 2
    nlinarith [mul_nonneg hr0 (sq_nonneg c)]
  set K := √(rhoSq c r * Ebar / c ^ 3) with hKdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hpt : ∀ ξ ∈ Icc s X, ‖remDens c χ t ψ u ξ‖ ≤ K * (1 / (ξ ^ 2 * √ξ)) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have h := norm_remDens_sq_le ψ u hc hχ0 hχ (le_trans hs hξ.1) hr (hwξ ξ hξ)
    have hE' : rhoSq c r * energy (aP c χ) ψ u ξ / (c ^ 3 * ξ ^ 5) ≤ rhoSq c r * Ebar / (c ^ 3 * ξ ^ 5) := by
      gcongr
      · exact rhoSq_nonneg hc hr0
      · exact hE ξ hξ
    have hrhs : rhoSq c r * Ebar / (c ^ 3 * ξ ^ 5) = (K * (1 / (ξ ^ 2 * √ξ))) ^ 2 := by
      have hEξ : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy aP; positivity
      have hEb : 0 ≤ Ebar := le_trans hEξ (hE ξ hξ)
      rw [mul_pow, hKdef, Real.sq_sqrt (by have := rhoSq_nonneg hc hr0; positivity), div_pow, mul_pow,
        Real.sq_sqrt hξ0.le]
      field_simp
    have hsq : ‖remDens c χ t ψ u ξ‖ ^ 2 ≤ (K * (1 / (ξ ^ 2 * √ξ))) ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hgi : IntervalIntegrable (fun ξ => K * (1 / (ξ ^ 2 * √ξ))) MeasureTheory.volume s X := by
    refine ContinuousOn.intervalIntegrable_of_Icc hsX (continuousOn_const.mul ?_)
    refine ContinuousOn.div continuousOn_const ((continuousOn_pow 2).mul continuous_sqrt.continuousOn) ?_
    intro x hx; have : 0 < x := by linarith [hx.1]
    exact mul_ne_zero (pow_ne_zero 2 this.ne') (Real.sqrt_pos.mpr this).ne'
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hsX
    (Filter.Eventually.of_forall fun ξ hξ => hpt ξ ⟨hξ.1.le, hξ.2⟩) hgi
  rw [intervalIntegral.integral_const_mul] at h1
  have h2 := integral_inv_sq_sqrt_le hs0 hsX
  calc _ ≤ _ := h1
    _ ≤ K * (2 / 3 / (s * √s)) := mul_le_mul_of_nonneg_left h2 hK0
    _ = _ := by ring

end Cvs.Prolate.Mellin.GreenBulkBound
