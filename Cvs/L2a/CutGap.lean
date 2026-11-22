import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut gap

For `ψ_i(m·)`, `ψ_j(n·)` in the scaled form `pm`, `qm` of Cvs.L2a.NonresonantCrossIntegral, `SturmProductByParts`'s cross coefficient is `−c²δ·pm m·pm n`, and
`δ ≥ Γ = n² − m⁴θ²/(m²θ² − 1)` when `0 ≤ χ_i`, `χ_j ≤ c²`. `Γ > 0` on the cut range: `m ≥ 2` with `θ ≥ 1`, or `m = 1`
past the self-dual point `θ = 2/√3` of the `(1, 2)` pair, where `Γ₁₂ = 0`; `Γ₁₂(5/4) = 11/9`.
-/

namespace Cvs.L2a.CutGap

open Real Set Cvs.L2a.NonresonantCrossIntegral

/-- The orbit gap `Γ_mn(θ) = n² − m⁴θ²/(m²θ² − 1)`. -/
noncomputable def cutGamma (m n θ : ℝ) : ℝ := n ^ 2 - m ^ 4 * θ ^ 2 / (m ^ 2 * θ ^ 2 - 1)

/-- The frequency gap `δ = n²(1 + (1 − x')/(n²θ² − 1)) − m²(1 + (1 − x)/(m²θ² − 1))`. -/
noncomputable def cutDelta (m n θ x x' : ℝ) : ℝ :=
  n ^ 2 * (1 + (1 - x') / (n ^ 2 * θ ^ 2 - 1)) - m ^ 2 * (1 + (1 - x) / (m ^ 2 * θ ^ 2 - 1))

/-- `∂_θ δ`. -/
noncomputable def cutDelta' (m n θ x x' : ℝ) : ℝ :=
  2 * m ^ 4 * θ * (1 - x) / (m ^ 2 * θ ^ 2 - 1) ^ 2 - 2 * n ^ 4 * θ * (1 - x') / (n ^ 2 * θ ^ 2 - 1) ^ 2

/-- The majorant `2n⁴θ/(n²θ² − 1)² + 2m⁴θ/(m²θ² − 1)²` of `|∂_θ δ|`. -/
noncomputable def cutDeltaBound (m n θ : ℝ) : ℝ :=
  2 * n ^ 4 * θ / (n ^ 2 * θ ^ 2 - 1) ^ 2 + 2 * m ^ 4 * θ / (m ^ 2 * θ ^ 2 - 1) ^ 2

/-- `SturmProductByParts`'s cross coefficient for `ψ_i(m·)`, `ψ_j(n·)` in the scaled form `pm`, `qm` (`Cvs.L2a.NonresonantCrossIntegral.Dmr` with two `χ`). -/
noncomputable def crossD (c χi χj m n θ : ℝ) : ℝ := pm n θ * qm c χi m θ - pm m θ * qm c χj n θ

/-- The lower cut: `t₁` for `m = 1`, `1` for `m ≥ 2`. -/
noncomputable def cutLo (t₁ : ℝ) (m : ℕ) : ℝ := if m = 1 then t₁ else 1

/-- The upper cut `max(lo, X/n)`. -/
noncomputable def cutHi (t₁ X : ℝ) (m n : ℕ) : ℝ := max (cutLo t₁ m) (X / n)

theorem crossD_eq {c χi χj m n θ : ℝ} (hc : c ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0) (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) :
    crossD c χi χj m n θ = -(c ^ 2 * cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (pm m θ * pm n θ)) := by
  unfold crossD cutDelta pm qm
  have hpm' : -1 + θ ^ 2 * m ^ 2 ≠ 0 := by intro h; apply hpm; linear_combination h
  have hpn' : -1 + θ ^ 2 * n ^ 2 ≠ 0 := by intro h; apply hpn; linear_combination h
  rw [show m ^ 2 * θ ^ 2 - 1 = -1 + θ ^ 2 * m ^ 2 by ring, show n ^ 2 * θ ^ 2 - 1 = -1 + θ ^ 2 * n ^ 2 by ring]
  field_simp
  ring

theorem cutGamma_le_cutDelta {m n θ x x' : ℝ} (hpm : 0 < m ^ 2 * θ ^ 2 - 1) (hpn : 0 < n ^ 2 * θ ^ 2 - 1)
    (hx : 0 ≤ x) (hx' : x' ≤ 1) : cutGamma m n θ ≤ cutDelta m n θ x x' := by
  unfold cutGamma cutDelta
  have h1 : 0 ≤ n ^ 2 * ((1 - x') / (n ^ 2 * θ ^ 2 - 1)) :=
    mul_nonneg (sq_nonneg n) (div_nonneg (by linarith) hpn.le)
  have h2 : m ^ 2 * (1 + (1 - x) / (m ^ 2 * θ ^ 2 - 1)) ≤ m ^ 4 * θ ^ 2 / (m ^ 2 * θ ^ 2 - 1) := by
    have e : m ^ 4 * θ ^ 2 / (m ^ 2 * θ ^ 2 - 1) = m ^ 2 * (1 + 1 / (m ^ 2 * θ ^ 2 - 1)) := by
      field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg m)
    have : (1 - x) / (m ^ 2 * θ ^ 2 - 1) ≤ 1 / (m ^ 2 * θ ^ 2 - 1) :=
      div_le_div_of_nonneg_right (by linarith) hpm.le
    linarith
  nlinarith

theorem cutGamma_ge_of_two_le {m n θ : ℝ} (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (hθ : 1 ≤ θ) :
    2 * m - 1 / (m ^ 2 - 1) ≤ cutGamma m n θ := by
  unfold cutGamma
  have hm2 : 3 ≤ m ^ 2 - 1 := by nlinarith
  have hθ2 : 1 ≤ θ ^ 2 := by nlinarith
  have hp : m ^ 2 - 1 ≤ m ^ 2 * θ ^ 2 - 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ2 (sq_nonneg m)]
  have hne : m ^ 2 * θ ^ 2 - 1 ≠ 0 := by linarith
  have e : m ^ 4 * θ ^ 2 / (m ^ 2 * θ ^ 2 - 1) = m ^ 2 + m ^ 2 / (m ^ 2 * θ ^ 2 - 1) := by
    field_simp; ring
  have h1 : m ^ 2 / (m ^ 2 * θ ^ 2 - 1) ≤ m ^ 2 / (m ^ 2 - 1) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hp
  have hne2 : m ^ 2 - 1 ≠ 0 := by linarith
  have e2 : m ^ 2 / (m ^ 2 - 1) = 1 + 1 / (m ^ 2 - 1) := by field_simp; ring
  have hn2 : (m + 1) ^ 2 ≤ n ^ 2 := by nlinarith
  rw [e]; linarith

theorem cutGamma_pos_of_two_le {m n θ : ℝ} (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (hθ : 1 ≤ θ) :
    0 < cutGamma m n θ := by
  have h := cutGamma_ge_of_two_le hm hmn hθ
  have hm2 : 3 ≤ m ^ 2 - 1 := by nlinarith
  have : 1 / (m ^ 2 - 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

theorem cutGamma_one_pos {n θ : ℝ} (hn : 2 ≤ n) (hθ : 4 < 3 * θ ^ 2) : 0 < cutGamma 1 n θ := by
  unfold cutGamma
  have hp : 0 < θ ^ 2 - 1 := by linarith
  have h4 : θ ^ 2 / (θ ^ 2 - 1) < 4 := by rw [div_lt_iff₀ hp]; linarith
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  norm_num; linarith

theorem cutGamma_one_mono {n θ θ' : ℝ} (hθ : 1 < θ) (hθθ' : θ ≤ θ') : cutGamma 1 n θ ≤ cutGamma 1 n θ' := by
  unfold cutGamma
  have hp : 0 < θ ^ 2 - 1 := by nlinarith
  have hp' : θ ^ 2 - 1 ≤ θ' ^ 2 - 1 := by nlinarith
  have e : ∀ t : ℝ, 0 < t ^ 2 - 1 → 1 ^ 4 * t ^ 2 / (1 ^ 2 * t ^ 2 - 1) = 1 + 1 / (t ^ 2 - 1) := by
    intro t ht; field_simp; ring
  rw [e θ hp, e θ' (by linarith)]
  have : 1 / (θ' ^ 2 - 1) ≤ 1 / (θ ^ 2 - 1) := one_div_le_one_div_of_le hp hp'
  linarith

theorem cutGamma_pos_of_cutLo_le {m n : ℕ} {t₁ θ : ℝ} (hm : 1 ≤ m) (hmn : m < n) (ht₁ : 1 ≤ t₁)
    (hsd : 4 < 3 * t₁ ^ 2) (hθ : cutLo t₁ m ≤ θ) : 0 < cutGamma m n θ := by
  unfold cutLo at hθ
  split_ifs at hθ with h1
  · subst h1
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast hmn
    have : 4 < 3 * θ ^ 2 := by nlinarith
    simpa using cutGamma_one_pos hn this
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    exact cutGamma_pos_of_two_le hm2 hmn' hθ

/-- On a cut range every dilate is past the edge: `1 < k²θ²` for `m ≤ k`, `θ ≥ lo_m`, `1 < t₁`. -/
theorem one_lt_sq_mul_of_cutLo_le {m k : ℕ} {t₁ θ : ℝ} (hm : 1 ≤ m) (hmk : m ≤ k) (ht₁ : 1 < t₁)
    (hθ : cutLo t₁ m ≤ θ) : 1 < (k : ℝ) ^ 2 * θ ^ 2 := by
  have hk : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold cutLo at hθ
  split_ifs at hθ with h1
  · have hθ1 : 1 < θ := lt_of_lt_of_le ht₁ hθ
    have hk1 : (1 : ℝ) ≤ k := le_trans hm1 hk
    nlinarith [mul_le_mul hk1 hk1 zero_le_one (by linarith), mul_lt_mul hθ1 hθ1.le one_pos (by linarith)]
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have hk2 : (2 : ℝ) ≤ k := le_trans hm2 hk
    nlinarith [mul_le_mul hk2 hk2 (by norm_num) (by linarith), mul_le_mul hθ hθ zero_le_one (by linarith)]

theorem hasDerivAt_cutDelta {m n θ x x' : ℝ} (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0) (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) :
    HasDerivAt (fun t => cutDelta m n t x x') (cutDelta' m n θ x x') θ := by
  have hPm : HasDerivAt (fun t => m ^ 2 * t ^ 2 - 1) (m ^ 2 * (2 * θ)) θ := by
    have := ((hasDerivAt_pow 2 θ).const_mul (m ^ 2)).sub_const 1
    simpa using this
  have hPn : HasDerivAt (fun t => n ^ 2 * t ^ 2 - 1) (n ^ 2 * (2 * θ)) θ := by
    have := ((hasDerivAt_pow 2 θ).const_mul (n ^ 2)).sub_const 1
    simpa using this
  have h1 := ((hasDerivAt_const θ (1 - x')).div hPn hpn).const_add 1 |>.const_mul (n ^ 2)
  have h2 := ((hasDerivAt_const θ (1 - x)).div hPm hpm).const_add 1 |>.const_mul (m ^ 2)
  refine (h1.sub h2).congr_deriv ?_
  unfold cutDelta'
  field_simp
  ring

theorem abs_cutDelta'_le {m n θ x x' : ℝ} (hθ : 0 ≤ θ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hx0' : 0 ≤ x')
    (hx1' : x' ≤ 1) :
    |cutDelta' m n θ x x'| ≤ cutDeltaBound m n θ := by
  unfold cutDelta' cutDeltaBound
  have hA0 : 0 ≤ 2 * m ^ 4 * θ * (1 - x) / (m ^ 2 * θ ^ 2 - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _); have : 0 ≤ 1 - x := by linarith
    positivity
  have hB0 : 0 ≤ 2 * n ^ 4 * θ * (1 - x') / (n ^ 2 * θ ^ 2 - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _); have : 0 ≤ 1 - x' := by linarith
    positivity
  have hA : 2 * m ^ 4 * θ * (1 - x) / (m ^ 2 * θ ^ 2 - 1) ^ 2 ≤ 2 * m ^ 4 * θ / (m ^ 2 * θ ^ 2 - 1) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have : 0 ≤ 2 * m ^ 4 * θ := by positivity
    nlinarith
  have hB : 2 * n ^ 4 * θ * (1 - x') / (n ^ 2 * θ ^ 2 - 1) ^ 2 ≤ 2 * n ^ 4 * θ / (n ^ 2 * θ ^ 2 - 1) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have : 0 ≤ 2 * n ^ 4 * θ := by positivity
    nlinarith
  rw [abs_le]; constructor <;> linarith

end Cvs.L2a.CutGap
