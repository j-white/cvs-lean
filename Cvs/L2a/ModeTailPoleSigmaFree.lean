import Mathlib
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.TailOfModes
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ModeSmoothWeightByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole values of the tail without `σ`

`ModeSmoothWeightByParts`'s one integration by parts holds with any lower bound `βm²τ² ≤ q_m`; for `mτ ≥ 2` and `χ ≤ c²`,
`β = (3/4)c²`. The first mode on `[1 + η, b]` integrates by parts against `q ≥ c²(τ² − 1)`, with
`∫ τ²/(τ² − 1)² ≤ s/(s² − 1)`, and Sonin bounds `[1, 1 + η]`: `|∫F| ≤ η|ψ(1)| + 4Us/(c²(s² − 1)) + (56/9)(π²/6)U/c²`,
`|∫F/θ| ≤ η|ψ(1)| + 5Us/(c²(s² − 1)) + (16/3)(π²/6)U/c²`, `s = 1 + η`, `|u(ξ)| ≤ ξU`, for every `χ < c²`.
-/

namespace Cvs.L2a.ModeTailPoleSigmaFree

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.ModeSmoothWeightByParts Cvs.L2a.TailOfModes

/-- `ModeSmoothWeightByParts`'s first mode bound with a general lower bound `β m²τ² ≤ q_m`. -/
theorem mode_one_le_beta {c χ m s t U β : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hm : 1 ≤ m) (hβ : 0 < β)
    (hs : 1 ≤ s) (hst : s ≤ t) (hU : 0 ≤ U)
    (hu : ∀ ξ ∈ Icc (m * s) (m * t), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc (m * s) (m * t), |u ξ| ≤ ξ * U) (hψc : ContinuousOn ψ (Icc (m * s) (m * t)))
    (hqβ : ∀ τ ∈ Icc s t, β * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ) :
    |∫ τ in s..t, ψ (m * τ)| ≤ 2 * U / (β * m ^ 2 * s) + 2 * c ^ 2 * U / (β ^ 2 * m ^ 2 * s) := by
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < β := hβ
  have hmem : ∀ τ ∈ Icc s t, m * τ ∈ Icc (m * s) (m * t) := fun τ hτ =>
    ⟨mul_le_mul_of_nonneg_left hτ.1 hm0.le, mul_le_mul_of_nonneg_left hτ.2 hm0.le⟩
  have hτ1 : ∀ τ ∈ Icc s t, 1 ≤ m * τ := fun τ hτ => by nlinarith [hτ.1]
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hq : ∀ τ ∈ Icc s t, β * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ := hqβ
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
  have hbd : ∀ τ ∈ Icc s t, |u (m * τ) / m * (1 / qm c χ m τ)| ≤ U / (β * m ^ 2 * s) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    rw [abs_mul, abs_of_pos (by have := hqp τ hτ; positivity : 0 < 1 / qm c χ m τ)]
    calc |u (m * τ) / m| * (1 / qm c χ m τ) ≤ τ * U * (1 / (β * (m ^ 2 * τ ^ 2))) :=
          mul_le_mul (hum τ hτ) (one_div_le_one_div_of_le (mul_pos hd (by positivity)) (hq τ hτ))
            (one_div_pos.mpr (hqp τ hτ)).le (mul_nonneg hτp.le hU)
      _ = U / (β * m ^ 2 * τ) := by field_simp
      _ ≤ U / (β * m ^ 2 * s) :=
          div_le_div_of_nonneg_left hU (mul_pos (mul_pos hd (by positivity)) hs0)
            (mul_le_mul_of_nonneg_left hτ.1 (mul_pos hd (by positivity)).le)
  have hK : ∀ τ ∈ Icc s t, |u (m * τ) / m * (-(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2)|
      ≤ 2 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / τ ^ 2) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hq2 : (β * (m ^ 2 * τ ^ 2)) ^ 2 ≤ qm c χ m τ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hq τ hτ) 2
    have hpos : 0 < 2 * c ^ 2 * m ^ 2 * τ / qm c χ m τ ^ 2 := by have := hqp τ hτ; positivity
    rw [abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    calc |u (m * τ) / m| * (2 * c ^ 2 * m ^ 2 * τ / qm c χ m τ ^ 2)
        ≤ τ * U * (2 * c ^ 2 * m ^ 2 * τ / (β * (m ^ 2 * τ ^ 2)) ^ 2) :=
          mul_le_mul (hum τ hτ) (div_le_div_of_nonneg_left (by positivity) (pow_pos (mul_pos hd (by positivity)) 2) hq2)
            hpos.le (mul_nonneg hτp.le hU)
      _ = 2 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / τ ^ 2) := by field_simp
  have hKint : ∫ τ in s..t, 2 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / τ ^ 2)
      ≤ 2 * c ^ 2 * U / (β ^ 2 * m ^ 2 * s) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_sq hs0 hst]
    have : 1 / s - 1 / t ≤ 1 / s := by
      have : 0 ≤ 1 / t := by have := lt_of_lt_of_le hs0 hst; positivity
      linarith
    calc 2 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / s - 1 / t)
        ≤ 2 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / s) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hint : |∫ τ in s..t, u (m * τ) / m * (-(2 * c ^ 2 * m ^ 2 * τ) / qm c χ m τ ^ 2)|
      ≤ 2 * c ^ 2 * U / (β ^ 2 * m ^ 2 * s) := by
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
  have e2 : 2 * U / (β * m ^ 2 * s) = U / (β * m ^ 2 * s) + U / (β * m ^ 2 * s) := by
    ring
  rw [abs_le]
  constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]

/-- `ModeSmoothWeightByParts`'s `1/τ`-weighted mode bound with a general lower bound `β m²τ² ≤ q_m`. -/
theorem mode_inv_le_beta {c χ m s t U β : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hm : 1 ≤ m) (hβ : 0 < β)
    (hs : 1 ≤ s) (hst : s ≤ t) (hU : 0 ≤ U)
    (hu : ∀ ξ ∈ Icc (m * s) (m * t), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc (m * s) (m * t), |u ξ| ≤ ξ * U) (hψc : ContinuousOn ψ (Icc (m * s) (m * t)))
    (hqβ : ∀ τ ∈ Icc s t, β * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ) :
    |∫ τ in s..t, ψ (m * τ) / τ|
      ≤ 2 * U / (β * m ^ 2 * s ^ 2) + 3 * c ^ 2 * U / (2 * (β ^ 2 * m ^ 2 * s ^ 2)) := by
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < β := hβ
  have hmem : ∀ τ ∈ Icc s t, m * τ ∈ Icc (m * s) (m * t) := fun τ hτ =>
    ⟨mul_le_mul_of_nonneg_left hτ.1 hm0.le, mul_le_mul_of_nonneg_left hτ.2 hm0.le⟩
  have hτ1 : ∀ τ ∈ Icc s t, 1 ≤ m * τ := fun τ hτ => by nlinarith [hτ.1]
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hq : ∀ τ ∈ Icc s t, β * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ := hqβ
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
  have hbd : ∀ τ ∈ Icc s t, |u (m * τ) / m * (1 / (τ * qm c χ m τ))| ≤ U / (β * m ^ 2 * s ^ 2) :=
      fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hlow : τ * (β * (m ^ 2 * τ ^ 2)) ≤ τ * qm c χ m τ := mul_le_mul_of_nonneg_left (hq τ hτ) hτp.le
    rw [abs_mul, abs_of_pos (one_div_pos.mpr (hτq τ hτ))]
    calc |u (m * τ) / m| * (1 / (τ * qm c χ m τ)) ≤ τ * U * (1 / (τ * (β * (m ^ 2 * τ ^ 2)))) :=
          mul_le_mul (hum τ hτ) (one_div_le_one_div_of_le (mul_pos hτp (mul_pos hd (by positivity))) hlow)
            (one_div_pos.mpr (hτq τ hτ)).le (mul_nonneg hτp.le hU)
      _ = U / (β * m ^ 2 * τ ^ 2) := by field_simp
      _ ≤ U / (β * m ^ 2 * s ^ 2) :=
          div_le_div_of_nonneg_left hU (mul_pos (mul_pos hd (by positivity)) (pow_pos hs0 2))
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le hτ.1 2) (mul_pos hd (by positivity)).le)
  have hK : ∀ τ ∈ Icc s t,
      |u (m * τ) / m * (-(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)|
        ≤ 3 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / τ ^ 3) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hnum : qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ) ≤ 3 * c ^ 2 * m ^ 2 * τ ^ 2 := by
      have := hqu τ; nlinarith
    have hnum0 : 0 < qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ) := by
      have := hqp τ hτ; positivity
    have hden : (τ * (β * (m ^ 2 * τ ^ 2))) ^ 2 ≤ (τ * qm c χ m τ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hq τ hτ) hτp.le) 2
    have hpos : 0 < (qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2 := by
      have := hτq τ hτ; positivity
    rw [abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    calc |u (m * τ) / m| * ((qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)
        ≤ τ * U * (3 * c ^ 2 * m ^ 2 * τ ^ 2 / (τ * (β * (m ^ 2 * τ ^ 2))) ^ 2) := by
          apply mul_le_mul (hum τ hτ) _ hpos.le (mul_nonneg hτp.le hU)
          exact div_le_div₀ (by positivity) hnum (pow_pos (mul_pos hτp (mul_pos hd (by positivity))) 2) hden
      _ = 3 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / τ ^ 3) := by field_simp
  have hKint : ∫ τ in s..t, 3 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / τ ^ 3)
      ≤ 3 * c ^ 2 * U / (2 * (β ^ 2 * m ^ 2 * s ^ 2)) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_cube hs0 hst]
    have : (1 / s ^ 2 - 1 / t ^ 2) / 2 ≤ 1 / (2 * s ^ 2) := by
      have : 0 ≤ 1 / t ^ 2 := by have := lt_of_lt_of_le hs0 hst; positivity
      have e : 1 / (2 * s ^ 2) = (1 / s ^ 2) / 2 := by field_simp
      rw [e]; linarith
    calc 3 * c ^ 2 * U / (β ^ 2 * m ^ 2) * ((1 / s ^ 2 - 1 / t ^ 2) / 2)
        ≤ 3 * c ^ 2 * U / (β ^ 2 * m ^ 2) * (1 / (2 * s ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hint : |∫ τ in s..t, u (m * τ) / m * (-(qm c χ m τ + τ * (2 * c ^ 2 * m ^ 2 * τ)) / (τ * qm c χ m τ) ^ 2)|
      ≤ 3 * c ^ 2 * U / (2 * (β ^ 2 * m ^ 2 * s ^ 2)) := by
    refine (abs_integral_le_integral_abs hst).trans ((integral_mono_on hst ?_ ?_ hK).trans hKint)
    · have huc : ContinuousOn (fun τ => u (m * τ) / m) (Icc s t) := fun τ hτ =>
        (huu τ hτ).continuousAt.continuousWithinAt
      exact ((huc.mul hhc).abs).intervalIntegrable_of_Icc hst
    · exact (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 3)
        (fun τ hτ => pow_ne_zero 3 (hτ0 τ hτ).ne'))).intervalIntegrable_of_Icc hst
  have A := abs_le.mp (hbd s (left_mem_Icc.mpr hst))
  have B := abs_le.mp (hbd t (right_mem_Icc.mpr hst))
  have C := abs_le.mp hint
  have e2 : 2 * U / (β * m ^ 2 * s ^ 2)
      = U / (β * m ^ 2 * s ^ 2) + U / (β * m ^ 2 * s ^ 2) := by ring
  rw [abs_le]
  constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]

/-- `q ≥ c²(τ² − 1)` for `χ ≤ c²`. -/
theorem qP_ge {c χ τ : ℝ} (hχc : χ ≤ c ^ 2) : c ^ 2 * (τ ^ 2 - 1) ≤ qP c χ τ := by
  unfold qP; nlinarith

/-- `∫_s^t (τ² + 1)/(τ² − 1)² = s/(s² − 1) − t/(t² − 1)` for `1 < s ≤ t`. -/
theorem integral_ratio {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    ∫ τ in s..t, (τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2 = s / (s ^ 2 - 1) - t / (t ^ 2 - 1) := by
  have hpos : ∀ τ ∈ uIcc s t, 0 < τ ^ 2 - 1 := fun τ hτ => by
    rw [uIcc_of_le hst] at hτ; nlinarith [hτ.1]
  have := integral_eq_sub_of_hasDerivAt (f := fun τ => -(τ / (τ ^ 2 - 1)))
    (f' := fun τ => (τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) (a := s) (b := t)
    (fun τ hτ => by
      have h0 := (hpos τ hτ).ne'
      have hd : HasDerivAt (fun r => r ^ 2 - 1) (2 * τ) τ := by
        simpa using (hasDerivAt_pow 2 τ).sub_const 1
      have h := ((hasDerivAt_id τ).div hd h0).neg
      refine h.congr_deriv ?_
      simp only [id]; field_simp; ring)
    (by
      have hc : ContinuousOn (fun τ : ℝ => (τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) (uIcc s t) :=
        ContinuousOn.div (continuousOn_id.pow 2 |>.add continuousOn_const)
          ((continuousOn_id.pow 2 |>.sub continuousOn_const).pow 2)
          (fun τ hτ => pow_ne_zero 2 (hpos τ hτ).ne')
      exact hc.intervalIntegrable)
  rw [this]; ring

set_option maxHeartbeats 1000000 in
/-- **The first mode past the edge**: `|∫_s^t ψ| ≤ 4Us/(c²(s² − 1))` for `1 < s ≤ t`, `|u(ξ)| ≤ ξU`. -/
theorem first_one_le {c χ s t U : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχc : χ ≤ c ^ 2) (hs : 1 < s) (hst : s ≤ t)
    (hU : 0 ≤ U) (hu : ∀ ξ ∈ Icc s t, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc s t, |u ξ| ≤ ξ * U) (hψc : ContinuousOn ψ (Icc s t)) :
    |∫ τ in s..t, ψ τ| ≤ 4 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by
  have hs0 : 0 < s := by linarith
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hp : ∀ τ ∈ Icc s t, 0 < τ ^ 2 - 1 := fun τ hτ => by nlinarith [hτ.1]
  have hq : ∀ τ ∈ Icc s t, c ^ 2 * (τ ^ 2 - 1) ≤ qP c χ τ := fun τ _ => qP_ge hχc
  have hqp : ∀ τ ∈ Icc s t, 0 < qP c χ τ := fun τ hτ =>
    lt_of_lt_of_le (mul_pos (by positivity) (hp τ hτ)) (hq τ hτ)
  have hqd : ∀ τ, HasDerivAt (qP c χ) (2 * c ^ 2 * τ) τ := fun τ => by
    have h := ((hasDerivAt_pow 2 τ).const_mul (c ^ 2)).sub_const χ
    have e : qP c χ = fun r => c ^ 2 * r ^ 2 - χ := by funext r; unfold qP; ring
    rw [e]; exact h.congr_deriv (by simp; ring)
  have hVd : ∀ τ ∈ Icc s t, HasDerivAt (fun r => 1 / qP c χ r) (-(2 * c ^ 2 * τ) / qP c χ τ ^ 2) τ :=
    fun τ hτ => by
    have h := (hqd τ).inv (hqp τ hτ).ne'
    have e : (fun r => 1 / qP c χ r) = fun r => (qP c χ r)⁻¹ := by funext r; simp [one_div]
    rw [e]; exact h.congr_deriv (by ring)
  have hqc : ContinuousOn (qP c χ) (Icc s t) := by unfold qP; fun_prop
  have hfc : ContinuousOn (fun τ => qP c χ τ * ψ τ) (Icc s t) := hqc.mul hψc
  have hhc : ContinuousOn (fun τ => -(2 * c ^ 2 * τ) / qP c χ τ ^ 2) (Icc s t) :=
    (continuousOn_const.mul continuousOn_id).neg.div (hqc.pow 2) (fun τ hτ => pow_ne_zero 2 (hqp τ hτ).ne')
  have hid := integral_eq (f := ψ) (u := u) (q := qP c χ) (g := fun _ => 1) (V := fun r => 1 / qP c χ r)
    (h := fun τ => -(2 * c ^ 2 * τ) / qP c χ τ ^ 2) hst hu (fun τ hτ => (hqp τ hτ).ne') (fun τ _ => rfl) hVd hfc hhc
  simp only [mul_one] at hid
  rw [hid]
  -- the boundary terms
  have hbd : ∀ τ ∈ Icc s t, |u τ * (1 / qP c χ τ)| ≤ U * s / (c ^ 2 * (s ^ 2 - 1)) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hpτ := hp τ hτ
    rw [abs_mul, abs_of_pos (one_div_pos.mpr (hqp τ hτ))]
    calc |u τ| * (1 / qP c χ τ) ≤ τ * U * (1 / (c ^ 2 * (τ ^ 2 - 1))) :=
          mul_le_mul (hub τ hτ) (one_div_le_one_div_of_le (by positivity) (hq τ hτ))
            (one_div_pos.mpr (hqp τ hτ)).le (mul_nonneg hτp.le hU)
      _ = U / c ^ 2 * (τ / (τ ^ 2 - 1)) := by field_simp
      _ ≤ U / c ^ 2 * (s / (s ^ 2 - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hs2 : 0 < s ^ 2 - 1 := by nlinarith
          rw [div_le_div_iff₀ hpτ hs2]
          nlinarith [mul_nonneg (sub_nonneg.mpr hτ.1) (by positivity : (0 : ℝ) ≤ s * τ + 1)]
      _ = U * s / (c ^ 2 * (s ^ 2 - 1)) := by field_simp
  -- the remainder
  have hK : ∀ τ ∈ Icc s t, |u τ * (-(2 * c ^ 2 * τ) / qP c χ τ ^ 2)|
      ≤ 2 * U / c ^ 2 * ((τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hpτ := hp τ hτ
    have hq2 : (c ^ 2 * (τ ^ 2 - 1)) ^ 2 ≤ qP c χ τ ^ 2 := pow_le_pow_left₀ (by positivity) (hq τ hτ) 2
    have hpos : 0 < 2 * c ^ 2 * τ / qP c χ τ ^ 2 := by have := hqp τ hτ; positivity
    rw [abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    calc |u τ| * (2 * c ^ 2 * τ / qP c χ τ ^ 2) ≤ τ * U * (2 * c ^ 2 * τ / (c ^ 2 * (τ ^ 2 - 1)) ^ 2) :=
          mul_le_mul (hub τ hτ) (div_le_div_of_nonneg_left (by positivity) (by positivity) hq2)
            hpos.le (mul_nonneg hτp.le hU)
      _ = 2 * U / c ^ 2 * (τ ^ 2 / (τ ^ 2 - 1) ^ 2) := by field_simp
      _ ≤ 2 * U / c ^ 2 * ((τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hKint : ∫ τ in s..t, 2 * U / c ^ 2 * ((τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) ≤ 2 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_ratio hs hst]
    have ht1 : 0 ≤ t / (t ^ 2 - 1) := div_nonneg (by linarith) (by nlinarith)
    calc 2 * U / c ^ 2 * (s / (s ^ 2 - 1) - t / (t ^ 2 - 1)) ≤ 2 * U / c ^ 2 * (s / (s ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by field_simp
  have hint : |∫ τ in s..t, u τ * (-(2 * c ^ 2 * τ) / qP c χ τ ^ 2)| ≤ 2 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by
    refine (abs_integral_le_integral_abs hst).trans ((integral_mono_on hst ?_ ?_ hK).trans hKint)
    · have huc : ContinuousOn u (Icc s t) := fun τ hτ => (hu τ hτ).continuousAt.continuousWithinAt
      exact ((huc.mul hhc).abs).intervalIntegrable_of_Icc hst
    · exact (continuousOn_const.mul ((continuousOn_id.pow 2).add continuousOn_const |>.div
        ((continuousOn_id.pow 2).sub continuousOn_const |>.pow 2)
        (fun τ hτ => pow_ne_zero 2 (hp τ hτ).ne'))).intervalIntegrable_of_Icc hst
  have A := abs_le.mp (hbd s (left_mem_Icc.mpr hst))
  have B := abs_le.mp (hbd t (right_mem_Icc.mpr hst))
  have C := abs_le.mp hint
  have e2 : 4 * U * s / (c ^ 2 * (s ^ 2 - 1)) = U * s / (c ^ 2 * (s ^ 2 - 1)) + U * s / (c ^ 2 * (s ^ 2 - 1))
      + 2 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by ring
  rw [abs_le]
  constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]

set_option maxHeartbeats 1000000 in
/-- **The first mode past the edge, over `τ`**: `|∫_s^t ψ/τ| ≤ 5Us/(c²(s² − 1))` for `1 < s ≤ t`. -/
theorem first_inv_le {c χ s t U : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hs : 1 < s)
    (hst : s ≤ t) (hU : 0 ≤ U) (hu : ∀ ξ ∈ Icc s t, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc s t, |u ξ| ≤ ξ * U) (hψc : ContinuousOn ψ (Icc s t)) :
    |∫ τ in s..t, ψ τ / τ| ≤ 5 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by
  have hs0 : 0 < s := by linarith
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hp : ∀ τ ∈ Icc s t, 0 < τ ^ 2 - 1 := fun τ hτ => by nlinarith [hτ.1]
  have hq : ∀ τ ∈ Icc s t, c ^ 2 * (τ ^ 2 - 1) ≤ qP c χ τ := fun τ _ => qP_ge hχc
  have hqp : ∀ τ ∈ Icc s t, 0 < qP c χ τ := fun τ hτ =>
    lt_of_lt_of_le (mul_pos (by positivity) (hp τ hτ)) (hq τ hτ)
  have hqu : ∀ τ, qP c χ τ ≤ c ^ 2 * τ ^ 2 := fun τ => by unfold qP; linarith
  have hqd : ∀ τ, HasDerivAt (qP c χ) (2 * c ^ 2 * τ) τ := fun τ => by
    have h := ((hasDerivAt_pow 2 τ).const_mul (c ^ 2)).sub_const χ
    have e : qP c χ = fun r => c ^ 2 * r ^ 2 - χ := by funext r; unfold qP; ring
    rw [e]; exact h.congr_deriv (by simp; ring)
  have hτq : ∀ τ ∈ Icc s t, 0 < τ * qP c χ τ := fun τ hτ => mul_pos (hτ0 τ hτ) (hqp τ hτ)
  have hVd : ∀ τ ∈ Icc s t, HasDerivAt (fun r => 1 / (r * qP c χ r))
      (-(qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2) τ := fun τ hτ => by
    have h := ((hasDerivAt_id τ).mul (hqd τ)).inv (hτq τ hτ).ne'
    have e : (fun r => 1 / (r * qP c χ r)) = fun r => (id r * qP c χ r)⁻¹ := by funext r; simp [one_div]
    rw [e]; exact h.congr_deriv (by simp)
  have hqc : ContinuousOn (qP c χ) (Icc s t) := by unfold qP; fun_prop
  have hfc : ContinuousOn (fun τ => qP c χ τ * ψ τ) (Icc s t) := hqc.mul hψc
  have hhc : ContinuousOn (fun τ => -(qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2) (Icc s t) :=
    (hqc.add (continuousOn_id.mul (continuousOn_const.mul continuousOn_id))).neg.div
      ((continuousOn_id.mul hqc).pow 2) (fun τ hτ => pow_ne_zero 2 (hτq τ hτ).ne')
  have hid := integral_eq (f := ψ) (u := u) (q := qP c χ) (g := fun τ => 1 / τ) (V := fun r => 1 / (r * qP c χ r))
    (h := fun τ => -(qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2)
    hst hu (fun τ hτ => (hqp τ hτ).ne')
    (fun τ hτ => by have := (hτ0 τ hτ).ne'; have := (hqp τ hτ).ne'; field_simp) hVd hfc hhc
  have e0 : ∫ τ in s..t, ψ τ / τ = ∫ τ in s..t, ψ τ * (1 / τ) := by congr 1; funext τ; ring
  rw [e0, hid]
  have hbd : ∀ τ ∈ Icc s t, |u τ * (1 / (τ * qP c χ τ))| ≤ U * s / (c ^ 2 * (s ^ 2 - 1)) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hpτ := hp τ hτ
    have hlow : τ * (c ^ 2 * (τ ^ 2 - 1)) ≤ τ * qP c χ τ := mul_le_mul_of_nonneg_left (hq τ hτ) hτp.le
    rw [abs_mul, abs_of_pos (one_div_pos.mpr (hτq τ hτ))]
    have hs2 : 0 < s ^ 2 - 1 := by nlinarith
    calc |u τ| * (1 / (τ * qP c χ τ)) ≤ τ * U * (1 / (τ * (c ^ 2 * (τ ^ 2 - 1)))) :=
          mul_le_mul (hub τ hτ) (one_div_le_one_div_of_le (by positivity) hlow)
            (one_div_pos.mpr (hτq τ hτ)).le (mul_nonneg hτp.le hU)
      _ = U / c ^ 2 * (1 / (τ ^ 2 - 1)) := by field_simp
      _ ≤ U / c ^ 2 * (s / (s ^ 2 - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ hpτ hs2]; nlinarith [hτ.1]
      _ = U * s / (c ^ 2 * (s ^ 2 - 1)) := by field_simp
  have hK : ∀ τ ∈ Icc s t, |u τ * (-(qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2)|
      ≤ 3 * U / c ^ 2 * ((τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hpτ := hp τ hτ
    have hτ1 : 1 ≤ τ := by linarith [hτ.1]
    have hnum : qP c χ τ + τ * (2 * c ^ 2 * τ) ≤ 3 * c ^ 2 * τ ^ 2 := by have := hqu τ; nlinarith
    have hnum0 : 0 < qP c χ τ + τ * (2 * c ^ 2 * τ) := by have := hqp τ hτ; positivity
    have hden : (τ * (c ^ 2 * (τ ^ 2 - 1))) ^ 2 ≤ (τ * qP c χ τ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hq τ hτ) hτp.le) 2
    have hpos : 0 < (qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2 := by have := hτq τ hτ; positivity
    rw [abs_mul, neg_div, abs_neg, abs_of_pos hpos]
    calc |u τ| * ((qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2)
        ≤ τ * U * (3 * c ^ 2 * τ ^ 2 / (τ * (c ^ 2 * (τ ^ 2 - 1))) ^ 2) := by
          apply mul_le_mul (hub τ hτ) _ hpos.le (mul_nonneg hτp.le hU)
          exact div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 3 * U / c ^ 2 * (τ / (τ ^ 2 - 1) ^ 2) := by field_simp
      _ ≤ 3 * U / c ^ 2 * ((τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hKint : ∫ τ in s..t, 3 * U / c ^ 2 * ((τ ^ 2 + 1) / (τ ^ 2 - 1) ^ 2) ≤ 3 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_ratio hs hst]
    have ht1 : 0 ≤ t / (t ^ 2 - 1) := div_nonneg (by linarith) (by nlinarith)
    calc 3 * U / c ^ 2 * (s / (s ^ 2 - 1) - t / (t ^ 2 - 1)) ≤ 3 * U / c ^ 2 * (s / (s ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by field_simp
  have hint : |∫ τ in s..t, u τ * (-(qP c χ τ + τ * (2 * c ^ 2 * τ)) / (τ * qP c χ τ) ^ 2)|
      ≤ 3 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by
    refine (abs_integral_le_integral_abs hst).trans ((integral_mono_on hst ?_ ?_ hK).trans hKint)
    · have huc : ContinuousOn u (Icc s t) := fun τ hτ => (hu τ hτ).continuousAt.continuousWithinAt
      exact ((huc.mul hhc).abs).intervalIntegrable_of_Icc hst
    · exact (continuousOn_const.mul ((continuousOn_id.pow 2).add continuousOn_const |>.div
        ((continuousOn_id.pow 2).sub continuousOn_const |>.pow 2)
        (fun τ hτ => pow_ne_zero 2 (hp τ hτ).ne'))).intervalIntegrable_of_Icc hst
  have A := abs_le.mp (hbd s (left_mem_Icc.mpr hst))
  have B := abs_le.mp (hbd t (right_mem_Icc.mpr hst))
  have C := abs_le.mp hint
  have e2 : 5 * U * s / (c ^ 2 * (s ^ 2 - 1)) = U * s / (c ^ 2 * (s ^ 2 - 1)) + U * s / (c ^ 2 * (s ^ 2 - 1))
      + 3 * U * s / (c ^ 2 * (s ^ 2 - 1)) := by ring
  rw [abs_le]
  constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]

/-- `q_m ≥ (3/4)c²m²τ²` for `mτ ≥ 2`, `χ ≤ c²`. -/
theorem qm_ge_c {c χ m τ : ℝ} (hχc : χ ≤ c ^ 2) (h : 2 ≤ m * τ) : 3 / 4 * c ^ 2 * (m ^ 2 * τ ^ 2) ≤ qm c χ m τ := by
  unfold qm
  have : 4 ≤ m ^ 2 * τ ^ 2 := by nlinarith
  nlinarith [sq_nonneg c]

set_option maxHeartbeats 2000000 in
/-- **The pole value `∫F`, `σ`-free**: `≤ η|ψ(1)| + 4Us/(c²(s² − 1)) + (56/9)(π²/6)U/c²`, `s = 1 + η`. -/
theorem pole_plus_le {c χ U Ξ b η : ℝ} {ψ u : ℝ → ℝ} {M : ℕ} (hc : 0 < c) (hχc : χ ≤ c ^ 2)
    (hη : 0 < η) (hηb : 1 + η ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ) (hM : 1 ≤ M)
    (hU : 0 ≤ U) (hu : ∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc 1 Ξ, |u ξ| ≤ ξ * U) (hcont : ContinuousOn ψ (Icc 1 Ξ))
    (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) :
    |∫ θ in Ioi 1, tailF ψ M b θ|
      ≤ η * |ψ 1| + 4 * U * (1 + η) / (c ^ 2 * ((1 + η) ^ 2 - 1)) + 56 / 9 * (π ^ 2 / 6) * U / c ^ 2 := by
  have hb : 1 ≤ b := by linarith
  have hin : ∀ m ∈ Finset.Icc 1 M, Icc ((m : ℝ) * 1) (m * b) ⊆ Icc 1 Ξ := fun m hm ξ hξ => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    exact ⟨by nlinarith [hξ.1], hξ.2.trans (by nlinarith)⟩
  have e : ∫ θ in Ioi 1, tailF ψ M b θ = ∫ θ in Ioi 1, tailF ψ M b θ * (fun _ => (1 : ℝ)) θ := by simp
  rw [e, integral_tailF_mul ψ _ M hb (fun m hm => by
    simp only [mul_one]
    exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ => hin m hm
      ⟨mul_le_mul_of_nonneg_left hθ.1 (Nat.cast_nonneg m), mul_le_mul_of_nonneg_left hθ.2 (Nat.cast_nonneg m)⟩))]
  simp only [mul_one]
  set B₁ := η * |ψ 1| + 4 * U * (1 + η) / (c ^ 2 * ((1 + η) ^ 2 - 1)) with hB₁
  have hMb : (M : ℝ) * b ≤ Ξ := hΞ
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  -- the first mode
  have h1 : |∫ θ in (1 : ℝ)..b, ψ ((1 : ℕ) * θ)| ≤ B₁ := by
    simp only [Nat.cast_one, one_mul]
    have hc1 : ContinuousOn ψ (Icc 1 b) := hcont.mono (Icc_subset_Icc le_rfl hbΞ)
    have i1 := (hc1.mono (Icc_subset_Icc le_rfl hηb)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      (by linarith : (1 : ℝ) ≤ 1 + η)
    have i2 := (hc1.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hηb
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have hA : |∫ θ in (1 : ℝ)..1 + η, ψ θ| ≤ η * |ψ 1| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 1 + η) (f := ψ) (C := |ψ 1|)
        (fun θ hθ => by
          rw [uIoc_of_le (by linarith)] at hθ
          rw [Real.norm_eq_abs]; exact hedge θ ⟨hθ.1.le, hθ.2.trans (hηb.trans hbΞ)⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + η - 1)] at this
      linarith
    have hs1 : (1 : ℝ) < 1 + η := by linarith
    have hB := first_one_le (U := U) (u := u) hc hχc hs1 hηb hU
      (fun ξ hξ => hu ξ ⟨by linarith [hξ.1], hξ.2.trans hbΞ⟩)
      (fun ξ hξ => hub ξ ⟨by linarith [hξ.1], hξ.2.trans hbΞ⟩) (hc1.mono (Icc_subset_Icc (by linarith) le_rfl))
    calc |(∫ θ in (1 : ℝ)..1 + η, ψ θ) + ∫ θ in 1 + η..b, ψ θ|
        ≤ |∫ θ in (1 : ℝ)..1 + η, ψ θ| + |∫ θ in 1 + η..b, ψ θ| := abs_add_le _ _
      _ ≤ B₁ := by rw [hB₁]; linarith
  -- the higher modes
  have hm2 : ∀ m ∈ Finset.Icc 1 M, m ≠ 1 → |∫ θ in (1 : ℝ)..b, ψ (m * θ)| ≤ 56 / 9 * U / c ^ 2 * (1 / (m : ℝ) ^ 2) :=
    fun m hm hm1 => by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by have := (Finset.mem_Icc.mp hm).1; omega)
    have key := mode_one_le_beta (m := m) (s := 1) (t := b) (β := 3 / 4 * c ^ 2) (χ := χ) hc (by linarith) (by positivity)
      le_rfl hb hU (fun ξ hξ => hu ξ (hin m hm hξ)) (fun ξ hξ => hub ξ (hin m hm hξ)) (hcont.mono (hin m hm))
      (fun τ hτ => qm_ge_c hχc (by nlinarith [hτ.1]))
    refine key.trans (le_of_eq ?_)
    field_simp; ring
  calc |∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, ψ (m * θ)|
      ≤ ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b, ψ (m * θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ((if m = 1 then B₁ else 0) + 56 / 9 * U / c ^ 2 * (1 / (m : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum; intro m hm
        by_cases h : m = 1
        · rw [h, ite_eq_left rfl]
          exact h1.trans (le_add_of_nonneg_right (by positivity))
        · rw [ite_eq_right h, zero_add]; exact hm2 m hm h
    _ = B₁ + 56 / 9 * U / c ^ 2 * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ 1, ite_eq_left (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩),
          Finset.mul_sum]
    _ ≤ B₁ + 56 / 9 * U / c ^ 2 * (π ^ 2 / 6) := by
        gcongr; exact Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M
    _ = _ := by rw [hB₁]; ring

set_option maxHeartbeats 2000000 in
/-- **The pole value `∫F/θ`, `σ`-free**: `≤ η|ψ(1)| + 5Us/(c²(s² − 1)) + (16/3)(π²/6)U/c²`, `s = 1 + η`. -/
theorem pole_minus_le {c χ U Ξ b η : ℝ} {ψ u : ℝ → ℝ} {M : ℕ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2)
    (hη : 0 < η) (hηb : 1 + η ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ) (hM : 1 ≤ M)
    (hU : 0 ≤ U) (hu : ∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc 1 Ξ, |u ξ| ≤ ξ * U) (hcont : ContinuousOn ψ (Icc 1 Ξ))
    (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) :
    |∫ θ in Ioi 1, tailF ψ M b θ / θ|
      ≤ η * |ψ 1| + 5 * U * (1 + η) / (c ^ 2 * ((1 + η) ^ 2 - 1)) + 16 / 3 * (π ^ 2 / 6) * U / c ^ 2 := by
  have hb : 1 ≤ b := by linarith
  have hin : ∀ m ∈ Finset.Icc 1 M, Icc ((m : ℝ) * 1) (m * b) ⊆ Icc 1 Ξ := fun m hm ξ hξ => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    exact ⟨by nlinarith [hξ.1], hξ.2.trans (by nlinarith)⟩
  have e : ∫ θ in Ioi 1, tailF ψ M b θ / θ = ∫ θ in Ioi 1, tailF ψ M b θ * (fun θ => 1 / θ) θ := by
    congr 1; funext θ; simp [div_eq_mul_inv]
  rw [e, integral_tailF_mul ψ _ M hb (fun m hm => by
    apply ContinuousOn.mul
    · exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ => hin m hm
        ⟨mul_le_mul_of_nonneg_left hθ.1 (Nat.cast_nonneg m), mul_le_mul_of_nonneg_left hθ.2 (Nat.cast_nonneg m)⟩)
    · exact continuousOn_const.div continuousOn_id (fun θ hθ => by linarith [hθ.1]))]
  set B₁ := η * |ψ 1| + 5 * U * (1 + η) / (c ^ 2 * ((1 + η) ^ 2 - 1)) with hB₁
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  have h1 : |∫ θ in (1 : ℝ)..b, ψ ((1 : ℕ) * θ) * (1 / θ)| ≤ B₁ := by
    simp only [Nat.cast_one, one_mul]
    have hc1 : ContinuousOn (fun θ => ψ θ * (1 / θ)) (Icc 1 b) :=
      (hcont.mono (Icc_subset_Icc le_rfl hbΞ)).mul (continuousOn_const.div continuousOn_id
        (fun θ hθ => by linarith [hθ.1]))
    have i1 := (hc1.mono (Icc_subset_Icc le_rfl hηb)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      (by linarith : (1 : ℝ) ≤ 1 + η)
    have i2 := (hc1.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hηb
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have hA : |∫ θ in (1 : ℝ)..1 + η, ψ θ * (1 / θ)| ≤ η * |ψ 1| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 1 + η)
        (f := fun θ => ψ θ * (1 / θ)) (C := |ψ 1|)
        (fun θ hθ => by
          rw [uIoc_of_le (by linarith)] at hθ
          have hθ1 : 1 ≤ θ := hθ.1.le
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / θ)]
          have hθ' : 1 / θ ≤ 1 := by rw [div_le_one (by linarith)]; exact hθ1
          have := hedge θ ⟨hθ1, hθ.2.trans (hηb.trans hbΞ)⟩
          calc |ψ θ| * (1 / θ) ≤ |ψ 1| * 1 := mul_le_mul this hθ' (by positivity) (abs_nonneg _)
            _ = |ψ 1| := mul_one _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + η - 1)] at this
      linarith
    have hs1 : (1 : ℝ) < 1 + η := by linarith
    have hB := first_inv_le (U := U) (u := u) hc hχ0 hχc hs1 hηb hU
      (fun ξ hξ => hu ξ ⟨by linarith [hξ.1], hξ.2.trans hbΞ⟩)
      (fun ξ hξ => hub ξ ⟨by linarith [hξ.1], hξ.2.trans hbΞ⟩)
      ((hcont.mono (Icc_subset_Icc le_rfl hbΞ)).mono (Icc_subset_Icc (by linarith) le_rfl))
    have e2 : ∫ θ in 1 + η..b, ψ θ * (1 / θ) = ∫ θ in 1 + η..b, ψ θ / θ := by congr 1; funext θ; ring
    rw [e2]
    calc |(∫ θ in (1 : ℝ)..1 + η, ψ θ * (1 / θ)) + ∫ θ in 1 + η..b, ψ θ / θ|
        ≤ |∫ θ in (1 : ℝ)..1 + η, ψ θ * (1 / θ)| + |∫ θ in 1 + η..b, ψ θ / θ| := abs_add_le _ _
      _ ≤ B₁ := by rw [hB₁]; linarith
  have hm2 : ∀ m ∈ Finset.Icc 1 M, m ≠ 1 →
      |∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ)| ≤ 16 / 3 * U / c ^ 2 * (1 / (m : ℝ) ^ 2) := fun m hm hm1 => by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by have := (Finset.mem_Icc.mp hm).1; omega)
    have key := mode_inv_le_beta (m := m) (s := 1) (t := b) (β := 3 / 4 * c ^ 2) (χ := χ) hc hχ0 (by linarith)
      (by positivity) le_rfl hb hU (fun ξ hξ => hu ξ (hin m hm hξ)) (fun ξ hξ => hub ξ (hin m hm hξ))
      (hcont.mono (hin m hm)) (fun τ hτ => qm_ge_c hχc (by nlinarith [hτ.1]))
    have e2 : ∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ) = ∫ θ in (1 : ℝ)..b, ψ (m * θ) / θ := by
      congr 1; funext θ; ring
    rw [e2]
    refine key.trans (le_of_eq ?_)
    field_simp; ring
  calc |∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ)|
      ≤ ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ((if m = 1 then B₁ else 0) + 16 / 3 * U / c ^ 2 * (1 / (m : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum; intro m hm
        by_cases h : m = 1
        · rw [h, ite_eq_left rfl]
          exact h1.trans (le_add_of_nonneg_right (by positivity))
        · rw [ite_eq_right h, zero_add]; exact hm2 m hm h
    _ = B₁ + 16 / 3 * U / c ^ 2 * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ 1, ite_eq_left (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩),
          Finset.mul_sum]
    _ ≤ B₁ + 16 / 3 * U / c ^ 2 * (π ^ 2 / 6) := by
        gcongr; exact Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M
    _ = _ := by rw [hB₁]; ring

end Cvs.L2a.ModeTailPoleSigmaFree
