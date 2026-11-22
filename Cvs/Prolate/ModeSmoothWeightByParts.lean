import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A mode against a smooth weight, by one integration by parts

If `u' = −q f` and `V = g/q` has derivative `h`, then `∫_s^t f g = −[u V]_s^t + ∫_s^t u h`. For the scaled mode
`ψ(m·)` with `|u(ξ)| ≤ ξ U` and `q_m ≥ σ²m²τ²`: `|∫_s^t ψ(mτ) dτ| ≤ 2U/(σ²m² s) + 2c²U/(σ⁴m² s)` and
`|∫_s^t ψ(mτ)/τ dτ| ≤ 2U/(σ²m² s²) + 3c²U/(2σ⁴m² s²)`.
-/

namespace Cvs.Prolate.ModeSmoothWeightByParts

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral

/-- **One integration by parts**: `∫ f g = −(u(t)V(t) − u(s)V(s)) + ∫ u V'` with `V = g/q`, `u' = −q f`. -/
theorem integral_eq {f u q g V h : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hu : ∀ τ ∈ Icc s t, HasDerivAt u (-(q τ * f τ)) τ) (hq : ∀ τ ∈ Icc s t, q τ ≠ 0)
    (hV : ∀ τ ∈ Icc s t, V τ = g τ / q τ) (hVd : ∀ τ ∈ Icc s t, HasDerivAt V (h τ) τ)
    (hfc : ContinuousOn (fun τ => q τ * f τ) (Icc s t)) (hhc : ContinuousOn h (Icc s t)) :
    ∫ τ in s..t, f τ * g τ = -(u t * V t - u s * V s) + ∫ τ in s..t, u τ * h τ := by
  have hI : uIcc s t = Icc s t := uIcc_of_le hst
  have ibp := integral_mul_deriv_eq_deriv_mul (a := s) (b := t) (u := u) (v := V) (u' := fun τ => -(q τ * f τ))
    (v' := h) (fun τ hτ => hu τ (hI ▸ hτ)) (fun τ hτ => hVd τ (hI ▸ hτ))
    ((hfc.neg).intervalIntegrable_of_Icc hst) (hhc.intervalIntegrable_of_Icc hst)
  have e : ∫ τ in s..t, f τ * g τ = ∫ τ in s..t, -(-(q τ * f τ) * V τ) := by
    apply integral_congr
    intro τ hτ
    rw [hI] at hτ
    simp only
    rw [hV τ hτ]; field_simp [hq τ hτ]
  rw [e, intervalIntegral.integral_neg, ibp]; ring

/-- `q_m ≥ σ² m² τ²` where `mτ ≥ 1`. -/
theorem qm_ge {c χ m τ : ℝ} (hχ0 : 0 ≤ χ) (h : 1 ≤ m * τ) :
    (c ^ 2 - χ) * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ := by
  unfold qm
  have : 1 ≤ m ^ 2 * τ ^ 2 := by nlinarith
  nlinarith [mul_nonneg hχ0 (by linarith : (0 : ℝ) ≤ m ^ 2 * τ ^ 2 - 1)]

theorem integral_inv_sq {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : ∫ τ in s..t, 1 / τ ^ 2 = 1 / s - 1 / t := by
  have := integral_eq_sub_of_hasDerivAt (f := fun τ => -(1 / τ)) (f' := fun τ => 1 / τ ^ 2) (a := s) (b := t)
    (fun τ hτ => by
      rw [uIcc_of_le hst] at hτ
      have hτ0 : τ ≠ 0 := (lt_of_lt_of_le hs hτ.1).ne'
      have h := (hasDerivAt_inv hτ0).neg
      convert h using 1
      · funext r; simp [one_div]
      · simp [one_div])
    (by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hst]
      exact continuousOn_const.div (continuousOn_id.pow 2) (fun τ hτ =>
        pow_ne_zero 2 (lt_of_lt_of_le hs hτ.1).ne'))
  rw [this]; ring

/-- **A mode against the weight `1`** (the pole's `∫ F`). -/
theorem mode_one_le {c χ m s t U : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hm : 1 ≤ m)
    (hs : 1 ≤ s) (hst : s ≤ t) (hU : 0 ≤ U)
    (hu : ∀ ξ ∈ Icc (m * s) (m * t), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc (m * s) (m * t), |u ξ| ≤ ξ * U) (hψc : ContinuousOn ψ (Icc (m * s) (m * t))) :
    |∫ τ in s..t, ψ (m * τ)| ≤ 2 * U / ((c ^ 2 - χ) * m ^ 2 * s) + 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2 * s) := by
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hmem : ∀ τ ∈ Icc s t, m * τ ∈ Icc (m * s) (m * t) := fun τ hτ =>
    ⟨mul_le_mul_of_nonneg_left hτ.1 hm0.le, mul_le_mul_of_nonneg_left hτ.2 hm0.le⟩
  have hτ1 : ∀ τ ∈ Icc s t, 1 ≤ m * τ := fun τ hτ => by nlinarith [hτ.1]
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hq : ∀ τ ∈ Icc s t, (c ^ 2 - χ) * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ := fun τ hτ => qm_ge hχ0 (hτ1 τ hτ)
  have hqp : ∀ τ ∈ Icc s t, 0 < qm c χ m τ := fun τ hτ =>
    lt_of_lt_of_le (by have := hτ0 τ hτ; positivity) (hq τ hτ)
  have hmt : ∀ τ, HasDerivAt (fun r => m * r) m τ := fun τ => by simpa using (hasDerivAt_id τ).const_mul m
  have huu : ∀ τ ∈ Icc s t, HasDerivAt (fun r => u (m * r) / m) (-(qm c χ m τ * ψ (m * τ))) τ := fun τ hτ => by
    have := ((hu _ (hmem τ hτ)).comp τ (hmt τ)).div_const m
    refine this.congr_deriv ?_
    unfold qm qP; field_simp
  have hqd : ∀ τ, HasDerivAt (qm c χ m) (2 * c ^ 2 * m ^ 2 * τ) τ := fun τ => by
    have h := ((hasDerivAt_pow 2 τ).const_mul (c ^ 2 * m ^ 2)).sub_const χ
    have e : qm c χ m = fun r => c ^ 2 * m ^ 2 * r ^ 2 - χ := by funext r; unfold qm; ring
    rw [e]; exact h.congr_deriv (by simp; ring)
  have hVd : ∀ τ ∈ Icc s t, HasDerivAt (fun r => 1 / qm c χ m r)
      (-(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2) τ := fun τ hτ => by
    have h := (hqd τ).inv (hqp τ hτ).ne'
    have e : (fun r => 1 / qm c χ m r) = fun r => (qm c χ m r)⁻¹ := by funext r; simp [one_div]
    rw [e]; exact h.congr_deriv (by ring)
  have hqc : ContinuousOn (qm c χ m) (Icc s t) := by unfold qm; fun_prop
  have hfc : ContinuousOn (fun τ => qm c χ m τ * ψ (m * τ)) (Icc s t) :=
    hqc.mul (hψc.comp (continuousOn_const.mul continuousOn_id) (fun τ hτ => hmem τ hτ))
  have hhc : ContinuousOn (fun τ => -(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2) (Icc s t) :=
    (continuousOn_const.mul continuousOn_id).neg.div (hqc.pow 2) (fun τ hτ => pow_ne_zero 2 (hqp τ hτ).ne')
  have hid := integral_eq (f := fun τ => ψ (m * τ)) (u := fun r => u (m * r) / m) (q := qm c χ m)
    (g := fun _ => 1) (V := fun r => 1 / qm c χ m r) (h := fun τ => -(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2)
    hst huu (fun τ hτ => (hqp τ hτ).ne') (fun τ _ => rfl) hVd hfc hhc
  simp only [mul_one] at hid
  rw [hid]
  -- pointwise sizes
  have hum : ∀ τ ∈ Icc s t, |u (m * τ) / m| ≤ τ * U := fun τ hτ => by
    rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    have := hub _ (hmem τ hτ); linarith
  have hbd : ∀ τ ∈ Icc s t, |u (m * τ) / m * (1 / qm c χ m τ)| ≤ U / ((c ^ 2 - χ) * m ^ 2 * s) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    rw [abs_mul, abs_of_pos (by have := hqp τ hτ; positivity : 0 < 1 / qm c χ m τ)]
    calc |u (m * τ) / m| * (1 / qm c χ m τ) ≤ τ * U * (1 / ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2))) :=
          mul_le_mul (hum τ hτ) (one_div_le_one_div_of_le (mul_pos hd (by positivity)) (hq τ hτ))
            (one_div_pos.mpr (hqp τ hτ)).le (mul_nonneg hτp.le hU)
      _ = U / ((c ^ 2 - χ) * m ^ 2 * τ) := by field_simp
      _ ≤ U / ((c ^ 2 - χ) * m ^ 2 * s) :=
          div_le_div_of_nonneg_left hU (mul_pos (mul_pos hd (by positivity)) hs0)
            (mul_le_mul_of_nonneg_left hτ.1 (mul_pos hd (by positivity)).le)
  have hK : ∀ τ ∈ Icc s t, |u (m * τ) / m * (-(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2)|
      ≤ 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / τ ^ 2) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hq2 : ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2)) ^ 2 ≤ qm c χ m τ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hq τ hτ) 2
    have hpos : 0 < 2 * c ^ 2 * m ^ 2 * τ / qm c χ m τ ^ 2 := by have := hqp τ hτ; positivity
    rw [abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    calc |u (m * τ) / m| * (2 * c ^ 2 * m ^ 2 * τ / qm c χ m τ ^ 2)
        ≤ τ * U * (2 * c ^ 2 * m ^ 2 * τ / ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2)) ^ 2) :=
          mul_le_mul (hum τ hτ) (div_le_div_of_nonneg_left (by positivity) (pow_pos (mul_pos hd (by positivity)) 2) hq2)
            hpos.le (mul_nonneg hτp.le hU)
      _ = 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / τ ^ 2) := by field_simp
  have hKint : ∫ τ in s..t, 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / τ ^ 2)
      ≤ 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2 * s) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_sq hs0 hst]
    have : 1 / s - 1 / t ≤ 1 / s := by
      have : 0 ≤ 1 / t := by have := lt_of_lt_of_le hs0 hst; positivity
      linarith
    calc 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / s - 1 / t)
        ≤ 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / s) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hint : |∫ τ in s..t, u (m * τ) / m * (-(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2)|
      ≤ 2 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2 * s) := by
    refine (abs_integral_le_integral_abs hst).trans ((integral_mono_on hst ?_ ?_ hK).trans hKint)
    · have huc : ContinuousOn (fun τ => u (m * τ) / m) (Icc s t) := fun τ hτ =>
        (huu τ hτ).continuousAt.continuousWithinAt
      exact ((huc.mul hhc).abs).intervalIntegrable_of_Icc hst
    · exact (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2)
        (fun τ hτ => pow_ne_zero 2 (hτ0 τ hτ).ne'))).intervalIntegrable_of_Icc hst
  have hbs := hbd s (left_mem_Icc.mpr hst)
  have hbt := hbd t (right_mem_Icc.mpr hst)
  have A := abs_le.mp hbs
  have B := abs_le.mp hbt
  have C := abs_le.mp hint
  have e2 : 2 * U / ((c ^ 2 - χ) * m ^ 2 * s) = U / ((c ^ 2 - χ) * m ^ 2 * s) + U / ((c ^ 2 - χ) * m ^ 2 * s) := by
    ring
  rw [abs_le]
  constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]

theorem integral_inv_cube {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ∫ τ in s..t, 1 / τ ^ 3 = (1 / s ^ 2 - 1 / t ^ 2) / 2 := by
  have := integral_eq_sub_of_hasDerivAt (f := fun τ => -(1 / (2 * τ ^ 2))) (f' := fun τ => 1 / τ ^ 3)
    (a := s) (b := t)
    (fun τ hτ => by
      rw [uIcc_of_le hst] at hτ
      have hτ0 : τ ≠ 0 := (lt_of_lt_of_le hs hτ.1).ne'
      have h := (((hasDerivAt_pow 2 τ).const_mul 2).inv (by positivity)).neg
      have e : (fun τ : ℝ => -(1 / (2 * τ ^ 2))) = fun τ : ℝ => -((2 * τ ^ 2)⁻¹) := by funext r; simp [one_div]
      rw [e]; exact h.congr_deriv (by field_simp; ring))
    (by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hst]
      exact continuousOn_const.div (continuousOn_id.pow 3) (fun τ hτ =>
        pow_ne_zero 3 (lt_of_lt_of_le hs hτ.1).ne'))
  rw [this]; ring

/-- **A mode against the weight `1/τ`** (the pole's `∫ F/θ`). -/
theorem mode_inv_le {c χ m s t U : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hm : 1 ≤ m)
    (hs : 1 ≤ s) (hst : s ≤ t) (hU : 0 ≤ U)
    (hu : ∀ ξ ∈ Icc (m * s) (m * t), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc (m * s) (m * t), |u ξ| ≤ ξ * U) (hψc : ContinuousOn ψ (Icc (m * s) (m * t))) :
    |∫ τ in s..t, ψ (m * τ) / τ|
      ≤ 2 * U / ((c ^ 2 - χ) * m ^ 2 * s ^ 2) + 3 * c ^ 2 * U / (2 * ((c ^ 2 - χ) ^ 2 * m ^ 2 * s ^ 2)) := by
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hmem : ∀ τ ∈ Icc s t, m * τ ∈ Icc (m * s) (m * t) := fun τ hτ =>
    ⟨mul_le_mul_of_nonneg_left hτ.1 hm0.le, mul_le_mul_of_nonneg_left hτ.2 hm0.le⟩
  have hτ1 : ∀ τ ∈ Icc s t, 1 ≤ m * τ := fun τ hτ => by nlinarith [hτ.1]
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hq : ∀ τ ∈ Icc s t, (c ^ 2 - χ) * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ := fun τ hτ => qm_ge hχ0 (hτ1 τ hτ)
  have hqp : ∀ τ ∈ Icc s t, 0 < qm c χ m τ := fun τ hτ =>
    lt_of_lt_of_le (mul_pos hd (by have := hτ0 τ hτ; positivity)) (hq τ hτ)
  have hqu : ∀ τ, qm c χ m τ ≤ c ^ 2 * m ^ 2 * τ ^ 2 := fun τ => by unfold qm; linarith
  have hmt : ∀ τ, HasDerivAt (fun r => m * r) m τ := fun τ => by simpa using (hasDerivAt_id τ).const_mul m
  have huu : ∀ τ ∈ Icc s t, HasDerivAt (fun r => u (m * r) / m) (-(qm c χ m τ * ψ (m * τ))) τ := fun τ hτ => by
    have := ((hu _ (hmem τ hτ)).comp τ (hmt τ)).div_const m
    refine this.congr_deriv ?_
    unfold qm qP; field_simp
  have hqd : ∀ τ, HasDerivAt (qm c χ m) (2 * c ^ 2 * m ^ 2 * τ) τ := fun τ => by
    have h := ((hasDerivAt_pow 2 τ).const_mul (c ^ 2 * m ^ 2)).sub_const χ
    have e : qm c χ m = fun r => c ^ 2 * m ^ 2 * r ^ 2 - χ := by funext r; unfold qm; ring
    rw [e]; exact h.congr_deriv (by simp; ring)
  have hτq : ∀ τ ∈ Icc s t, 0 < τ * qm c χ m τ := fun τ hτ => mul_pos (hτ0 τ hτ) (hqp τ hτ)
  have hVd : ∀ τ ∈ Icc s t, HasDerivAt (fun r => 1 / (r * qm c χ m r))
      (-(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2) τ := fun τ hτ => by
    have h := ((hasDerivAt_id τ).mul (hqd τ)).inv (hτq τ hτ).ne'
    have e : (fun r => 1 / (r * qm c χ m r)) = fun r => (id r * qm c χ m r)⁻¹ := by funext r; simp [one_div]
    rw [e]; exact h.congr_deriv (by simp)
  have hqc : ContinuousOn (qm c χ m) (Icc s t) := by unfold qm; fun_prop
  have hfc : ContinuousOn (fun τ => qm c χ m τ * ψ (m * τ)) (Icc s t) :=
    hqc.mul (hψc.comp (continuousOn_const.mul continuousOn_id) (fun τ hτ => hmem τ hτ))
  have hhc : ContinuousOn (fun τ => -(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2) (Icc s t) :=
    (hqc.add (continuousOn_id.mul (continuousOn_const.mul continuousOn_id))).neg.div
      ((continuousOn_id.mul hqc).pow 2) (fun τ hτ => pow_ne_zero 2 (hτq τ hτ).ne')
  have hid := integral_eq (f := fun τ => ψ (m * τ)) (u := fun r => u (m * r) / m) (q := qm c χ m)
    (g := fun τ => 1 / τ) (V := fun r => 1 / (r * qm c χ m r))
    (h := fun τ => -(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)
    hst huu (fun τ hτ => (hqp τ hτ).ne')
    (fun τ hτ => by have := (hτ0 τ hτ).ne'; have := (hqp τ hτ).ne'; field_simp) hVd hfc hhc
  have e0 : ∫ τ in s..t, ψ (m * τ) / τ = ∫ τ in s..t, ψ (m * τ) * (1 / τ) := by
    congr 1; funext τ; ring
  rw [e0, hid]
  have hum : ∀ τ ∈ Icc s t, |u (m * τ) / m| ≤ τ * U := fun τ hτ => by
    rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    have := hub _ (hmem τ hτ); linarith
  have hbd : ∀ τ ∈ Icc s t, |u (m * τ) / m * (1 / (τ * qm c χ m τ))| ≤ U / ((c ^ 2 - χ) * m ^ 2 * s ^ 2) :=
      fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hlow : τ * ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2)) ≤ τ * qm c χ m τ := mul_le_mul_of_nonneg_left (hq τ hτ) hτp.le
    rw [abs_mul, abs_of_pos (one_div_pos.mpr (hτq τ hτ))]
    calc |u (m * τ) / m| * (1 / (τ * qm c χ m τ)) ≤ τ * U * (1 / (τ * ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2)))) :=
          mul_le_mul (hum τ hτ) (one_div_le_one_div_of_le (mul_pos hτp (mul_pos hd (by positivity))) hlow)
            (one_div_pos.mpr (hτq τ hτ)).le (mul_nonneg hτp.le hU)
      _ = U / ((c ^ 2 - χ) * m ^ 2 * τ ^ 2) := by field_simp
      _ ≤ U / ((c ^ 2 - χ) * m ^ 2 * s ^ 2) :=
          div_le_div_of_nonneg_left hU (mul_pos (mul_pos hd (by positivity)) (pow_pos hs0 2))
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le hτ.1 2) (mul_pos hd (by positivity)).le)
  have hK : ∀ τ ∈ Icc s t,
      |u (m * τ) / m * (-(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)|
        ≤ 3 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / τ ^ 3) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hnum : qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ) ≤ 3 * c ^ 2 * m ^ 2 * τ ^ 2 := by
      have := hqu τ; nlinarith
    have hnum0 : 0 < qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ) := by
      have := hqp τ hτ; positivity
    have hden : (τ * ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2))) ^ 2 ≤ (τ * qm c χ m τ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hq τ hτ) hτp.le) 2
    have hpos : 0 < (qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2 := by
      have := hτq τ hτ; positivity
    rw [abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    calc |u (m * τ) / m| * ((qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)
        ≤ τ * U * (3 * c ^ 2 * m ^ 2 * τ ^ 2 / (τ * ((c ^ 2 - χ) * (m ^ 2 * τ ^ 2))) ^ 2) := by
          apply mul_le_mul (hum τ hτ) _ hpos.le (mul_nonneg hτp.le hU)
          exact div_le_div₀ (by positivity) hnum (pow_pos (mul_pos hτp (mul_pos hd (by positivity))) 2) hden
      _ = 3 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / τ ^ 3) := by field_simp
  have hKint : ∫ τ in s..t, 3 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / τ ^ 3)
      ≤ 3 * c ^ 2 * U / (2 * ((c ^ 2 - χ) ^ 2 * m ^ 2 * s ^ 2)) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_cube hs0 hst]
    have : (1 / s ^ 2 - 1 / t ^ 2) / 2 ≤ 1 / (2 * s ^ 2) := by
      have : 0 ≤ 1 / t ^ 2 := by have := lt_of_lt_of_le hs0 hst; positivity
      have e : 1 / (2 * s ^ 2) = (1 / s ^ 2) / 2 := by field_simp
      rw [e]; linarith
    calc 3 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * ((1 / s ^ 2 - 1 / t ^ 2) / 2)
        ≤ 3 * c ^ 2 * U / ((c ^ 2 - χ) ^ 2 * m ^ 2) * (1 / (2 * s ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hint : |∫ τ in s..t, u (m * τ) / m * (-(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)|
      ≤ 3 * c ^ 2 * U / (2 * ((c ^ 2 - χ) ^ 2 * m ^ 2 * s ^ 2)) := by
    refine (abs_integral_le_integral_abs hst).trans ((integral_mono_on hst ?_ ?_ hK).trans hKint)
    · have huc : ContinuousOn (fun τ => u (m * τ) / m) (Icc s t) := fun τ hτ =>
        (huu τ hτ).continuousAt.continuousWithinAt
      exact ((huc.mul hhc).abs).intervalIntegrable_of_Icc hst
    · exact (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 3)
        (fun τ hτ => pow_ne_zero 3 (hτ0 τ hτ).ne'))).intervalIntegrable_of_Icc hst
  have A := abs_le.mp (hbd s (left_mem_Icc.mpr hst))
  have B := abs_le.mp (hbd t (right_mem_Icc.mpr hst))
  have C := abs_le.mp hint
  have e2 : 2 * U / ((c ^ 2 - χ) * m ^ 2 * s ^ 2)
      = U / ((c ^ 2 - χ) * m ^ 2 * s ^ 2) + U / ((c ^ 2 - χ) * m ^ 2 * s ^ 2) := by ring
  rw [abs_le]
  constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]

end Cvs.Prolate.ModeSmoothWeightByParts
