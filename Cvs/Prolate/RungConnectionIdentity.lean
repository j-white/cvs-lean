import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The connection identity: `E(∞) = A²/c` and `λ E(∞) = (2/π) ψ(1)²`

For `c > 0`, `0 ≤ χ < c²` and `g` twice differentiable on `[−1, 1]`, the Cvs.Prolate.CosineTransformSecondOrder asymptotics give
`|E(ξ) − A²/c| ≤ K/ξ` for `ξ ≥ 2`, `A = g(1) + g(−1)`, so `E → A²/c`. For even `g` with `psi c g = μ g` on `[−1, 1]`,
`A = 2g(1)` and `ψ(1) = μ g(1)`, so `λ · A²/c = (2/π) ψ(1)²` with `λ = (c/2π) μ² = (μ √(c/2π))²`.
-/

namespace Cvs.Prolate.RungConnectionIdentity

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.CosineTransformSecondOrder Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity
open scoped Interval

/-- `ξ ≤ ξ² − 1` for `ξ ≥ 2`. -/
theorem le_sq_sub_one {ξ : ℝ} (hξ : 2 ≤ ξ) : ξ ≤ ξ ^ 2 - 1 := by nlinarith

/-- **The split of the energy at infinity**: with `ψ = Aσ/(cξ) + ρ`, `u = Aξκ + r` and `σ² + κ² = 1`,
`aψ² + u²/a − A²/c` is the sum of four explicit pieces. -/
theorem energy_split {c ξ a A σ κ ρ r : ℝ} (hc : c ≠ 0) (hξ : ξ ≠ 0) (ha : a ≠ 0) (hσκ : σ ^ 2 + κ ^ 2 = 1) :
    a * (A * σ / (c * ξ) + ρ) ^ 2 + (A * ξ * κ + r) ^ 2 / a - A ^ 2 / c
      = A ^ 2 * σ ^ 2 * (a - c * ξ ^ 2) / (c ^ 2 * ξ ^ 2) + a * (2 * (A * σ / (c * ξ)) * ρ + ρ ^ 2)
        + A ^ 2 * κ ^ 2 * (c * ξ ^ 2 - a) / (a * c) + (2 * (A * ξ * κ) * r + r ^ 2) / a := by
  have hA : A ^ 2 / c = A ^ 2 * σ ^ 2 / c + A ^ 2 * κ ^ 2 / c := by
    rw [← add_div, ← mul_add, hσκ, mul_one]
  rw [hA]
  field_simp
  ring

/-- The sine piece: `|A²σ²(a − cξ²)/(cξ)²| ≤ A²/(cξ)` when `|a − cξ²| ≤ c`, `σ² ≤ 1`, `ξ ≥ 1`. -/
theorem piece_sin_le {c ξ a A σ : ℝ} (hc : 0 < c) (hξ1 : 1 ≤ ξ) (hd : |a - c * ξ ^ 2| ≤ c) (hσ1 : σ ^ 2 ≤ 1) :
    |A ^ 2 * σ ^ 2 * (a - c * ξ ^ 2) / (c ^ 2 * ξ ^ 2)| ≤ A ^ 2 / c / ξ := by
  have hξ0 : 0 < ξ := by linarith
  rw [abs_div, abs_of_pos (by positivity : 0 < c ^ 2 * ξ ^ 2), div_le_iff₀ (by positivity),
    abs_mul, abs_mul, abs_of_nonneg (sq_nonneg A), abs_of_nonneg (sq_nonneg σ)]
  have e1 : A ^ 2 / c / ξ * (c ^ 2 * ξ ^ 2) = A ^ 2 * c * ξ := by field_simp
  rw [e1]
  have h1 : σ ^ 2 * |a - c * ξ ^ 2| ≤ 1 * c := mul_le_mul hσ1 hd (abs_nonneg _) zero_le_one
  have h2 : A ^ 2 * c * 1 ≤ A ^ 2 * c * ξ := mul_le_mul_of_nonneg_left hξ1 (mul_nonneg (sq_nonneg A) hc.le)
  calc A ^ 2 * σ ^ 2 * |a - c * ξ ^ 2| = A ^ 2 * (σ ^ 2 * |a - c * ξ ^ 2|) := by ring
    _ ≤ A ^ 2 * (1 * c) := mul_le_mul_of_nonneg_left h1 (sq_nonneg A)
    _ = A ^ 2 * c * 1 := by ring
    _ ≤ A ^ 2 * c * ξ := h2

/-- The `ψ`-remainder piece: `|a(2(Aσ/(cξ))ρ + ρ²)| ≤ (2|A|C₁/c² + C₁²/c³)/ξ` when `|ρ| ≤ C₁/(cξ)²`,
`0 < a ≤ cξ²`, `|σ| ≤ 1`, `ξ ≥ 1`. -/
theorem piece_psi_le {c ξ a A σ ρ C1 : ℝ} (hc : 0 < c) (hξ1 : 1 ≤ ξ) (ha : 0 < a) (hhi : a ≤ c * ξ ^ 2)
    (hσa : |σ| ≤ 1) (hρ : |ρ| ≤ C1 / (c * ξ) ^ 2) :
    |a * (2 * (A * σ / (c * ξ)) * ρ + ρ ^ 2)| ≤ (2 * |A| * C1 / c ^ 2 + C1 ^ 2 / c ^ 3) / ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hX : 0 < c * ξ := by positivity
  have hsA : |A * σ / (c * ξ)| ≤ |A| / (c * ξ) := by
    rw [abs_div, abs_of_pos hX, abs_mul]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg A) hσa) hX.le
  have hin : |2 * (A * σ / (c * ξ)) * ρ + ρ ^ 2|
      ≤ 2 * (|A| / (c * ξ)) * (C1 / (c * ξ) ^ 2) + (C1 / (c * ξ) ^ 2) ^ 2 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsA zero_le_two) hρ (abs_nonneg _) (by positivity)
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hρ 2
  rw [abs_mul, abs_of_pos ha]
  calc a * |2 * (A * σ / (c * ξ)) * ρ + ρ ^ 2|
      ≤ c * ξ ^ 2 * (2 * (|A| / (c * ξ)) * (C1 / (c * ξ) ^ 2) + (C1 / (c * ξ) ^ 2) ^ 2) :=
        mul_le_mul hhi hin (abs_nonneg _) (by positivity)
    _ = (2 * |A| * C1 / c ^ 2 + C1 ^ 2 / c ^ 3 / ξ) / ξ := by field_simp
    _ ≤ (2 * |A| * C1 / c ^ 2 + C1 ^ 2 / c ^ 3) / ξ := by
        apply div_le_div_of_nonneg_right _ hξ0.le
        have : C1 ^ 2 / c ^ 3 / ξ ≤ C1 ^ 2 / c ^ 3 := div_le_self (by positivity) hξ1
        linarith

/-- The cosine piece: `|A²κ²(cξ² − a)/(ac)| ≤ A²/(cξ)` when `|a − cξ²| ≤ c`, `cξ ≤ a`, `κ² ≤ 1`. -/
theorem piece_cos_le {c ξ a A κ : ℝ} (hc : 0 < c) (hξ0 : 0 < ξ) (hca : c * ξ ≤ a) (hd : |a - c * ξ ^ 2| ≤ c)
    (hκ1 : κ ^ 2 ≤ 1) :
    |A ^ 2 * κ ^ 2 * (c * ξ ^ 2 - a) / (a * c)| ≤ A ^ 2 / c / ξ := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hca
  rw [abs_div, abs_of_pos (by positivity : 0 < a * c), abs_mul, abs_mul, abs_of_nonneg (sq_nonneg A),
    abs_of_nonneg (sq_nonneg κ), abs_sub_comm, div_le_iff₀ (by positivity)]
  have h1 : κ ^ 2 * |a - c * ξ ^ 2| ≤ 1 * c := mul_le_mul hκ1 hd (abs_nonneg _) zero_le_one
  have e1 : A ^ 2 / c / ξ * (a * c) = A ^ 2 * (a / ξ) := by field_simp
  rw [e1]
  have h4 : c ≤ a / ξ := by rw [le_div_iff₀ hξ0]; linarith
  calc A ^ 2 * κ ^ 2 * |a - c * ξ ^ 2| = A ^ 2 * (κ ^ 2 * |a - c * ξ ^ 2|) := by ring
    _ ≤ A ^ 2 * (1 * c) := mul_le_mul_of_nonneg_left h1 (sq_nonneg A)
    _ = A ^ 2 * c := by ring
    _ ≤ A ^ 2 * (a / ξ) := mul_le_mul_of_nonneg_left h4 (sq_nonneg A)

/-- The `u`-remainder piece: `|(2(Aξκ)r + r²)/a| ≤ (4|A|S + S²)/(cξ)` when `|r| ≤ S`, `c(ξ² − 1) ≤ a`,
`|κ| ≤ 1`, `ξ ≥ 2`. -/
theorem piece_u_le {c ξ a A κ r S : ℝ} (hc : 0 < c) (hξ : 2 ≤ ξ) (hlo : c * (ξ ^ 2 - 1) ≤ a) (hS : 0 ≤ S)
    (hκa : |κ| ≤ 1) (hr : |r| ≤ S) :
    |(2 * (A * ξ * κ) * r + r ^ 2) / a| ≤ (4 * |A| * S + S ^ 2) / c / ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hξξ : ξ ≤ ξ ^ 2 - 1 := le_sq_sub_one hξ
  have hp : 0 < ξ ^ 2 - 1 := by linarith
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hlo
  rw [abs_div, abs_of_pos ha]
  have hin : |2 * (A * ξ * κ) * r + r ^ 2| ≤ 2 * (|A| * ξ) * S + S ^ 2 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_two, abs_mul, abs_mul, abs_of_pos hξ0]
      have : |A| * ξ * |κ| ≤ |A| * ξ := mul_le_of_le_one_right (by positivity) hκa
      exact mul_le_mul (mul_le_mul_of_nonneg_left this zero_le_two) hr (abs_nonneg _) (by positivity)
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  calc |2 * (A * ξ * κ) * r + r ^ 2| / a ≤ (2 * (|A| * ξ) * S + S ^ 2) / (c * (ξ ^ 2 - 1)) :=
        div_le_div₀ (by positivity) hin (by positivity) hlo
    _ ≤ (4 * |A| * S + S ^ 2) / c / ξ := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hAS : 0 ≤ |A| * S := mul_nonneg (abs_nonneg A) hS
        have h1 : 2 * ξ ^ 2 ≤ 4 * (ξ ^ 2 - 1) := by linarith
        have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hAS hc.le)
        have h4 := mul_le_mul_of_nonneg_left hξξ (mul_nonneg (sq_nonneg S) hc.le)
        linarith

/-- **The algebra of the energy at infinity**: with `ψ = A sin(cξ)/(cξ) + ρ`, `u = Aξ cos(cξ) + r`,
`|ρ| ≤ C₁/(cξ)²`, `|r| ≤ S` and `c(ξ² − 1) ≤ a ≤ cξ²`, `ξ ≥ 2`: `|aψ² + u²/a − A²/c| ≤ K/ξ`. -/
theorem energy_alg_le {c ξ a ψ u A C1 S : ℝ} (hc : 0 < c) (hξ : 2 ≤ ξ) (hlo : c * (ξ ^ 2 - 1) ≤ a)
    (hhi : a ≤ c * ξ ^ 2) (hS : 0 ≤ S)
    (hψ : |ψ - A * sin (c * ξ) / (c * ξ)| ≤ C1 / (c * ξ) ^ 2) (hu : |u - A * ξ * cos (c * ξ)| ≤ S) :
    |a * ψ ^ 2 + u ^ 2 / a - A ^ 2 / c|
      ≤ ((2 * A ^ 2 + 4 * |A| * S + S ^ 2) / c + 2 * |A| * C1 / c ^ 2 + C1 ^ 2 / c ^ 3) / ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hξ1 : 1 ≤ ξ := by linarith
  have hξξ : ξ ≤ ξ ^ 2 - 1 := le_sq_sub_one hξ
  have hp : 0 < ξ ^ 2 - 1 := by linarith
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hlo
  have hca : c * ξ ≤ a := le_trans (mul_le_mul_of_nonneg_left hξξ hc.le) hlo
  have hd : |a - c * ξ ^ 2| ≤ c := abs_le.mpr ⟨by linarith, by linarith⟩
  have hσκ : sin (c * ξ) ^ 2 + cos (c * ξ) ^ 2 = 1 := sin_sq_add_cos_sq _
  have hσ1 : sin (c * ξ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (cos (c * ξ))]
  have hκ1 : cos (c * ξ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (sin (c * ξ))]
  have eψ : ψ = A * sin (c * ξ) / (c * ξ) + (ψ - A * sin (c * ξ) / (c * ξ)) := by ring
  have eu : u = A * ξ * cos (c * ξ) + (u - A * ξ * cos (c * ξ)) := by ring
  rw [eψ, eu, energy_split hc.ne' hξ0.ne' ha.ne' hσκ]
  have hT1 := piece_sin_le (A := A) hc hξ1 hd hσ1
  have hT2 := piece_psi_le (A := A) hc hξ1 ha hhi (abs_sin_le_one (c * ξ)) hψ
  have hT3 := piece_cos_le (A := A) hc hξ0 hca hd hκ1
  have hT4 := piece_u_le (A := A) hc hξ hlo hS (abs_cos_le_one (c * ξ)) hu
  have hsum := add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
  have hK : A ^ 2 / c / ξ + (2 * |A| * C1 / c ^ 2 + C1 ^ 2 / c ^ 3) / ξ + A ^ 2 / c / ξ
      + (4 * |A| * S + S ^ 2) / c / ξ
      = ((2 * A ^ 2 + 4 * |A| * S + S ^ 2) / c + 2 * |A| * C1 / c ^ 2 + C1 ^ 2 / c ^ 3) / ξ := by
    field_simp; ring
  rw [← hK]
  refine le_trans ?_ hsum
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact abs_add_le _ _

/-- `c(ξ² − 1) ≤ a(ξ)` for `ξ ≥ 1`, `χ ≤ c²`. -/
theorem le_aP_far {c χ ξ : ℝ} (hχc : χ ≤ c ^ 2) (hξ : 1 ≤ ξ) : c * (ξ ^ 2 - 1) ≤ aP c χ ξ := by
  unfold aP pP qP
  have hp : 0 ≤ ξ ^ 2 - 1 := by nlinarith
  apply le_sqrt_of_sq_le
  have : c ^ 2 * (ξ ^ 2 - 1) ≤ c ^ 2 * ξ ^ 2 - χ := by nlinarith
  calc (c * (ξ ^ 2 - 1)) ^ 2 = (ξ ^ 2 - 1) * (c ^ 2 * (ξ ^ 2 - 1)) := by ring
    _ ≤ (ξ ^ 2 - 1) * (c ^ 2 * ξ ^ 2 - χ) := mul_le_mul_of_nonneg_left this hp

/-- The rate constant `K = (2A² + 4|A|Σ + Σ²)/c + 2|A|C₁/c² + C₁²/c³` of the energy at infinity. -/
noncomputable def energyRate (c : ℝ) (g g₁ g₂ : ℝ → ℝ) : ℝ :=
  (2 * ampl g ^ 2 + 4 * |ampl g| * cstU c g g₁ g₂ + cstU c g g₁ g₂ ^ 2) / c
    + 2 * |ampl g| * cst₁ g₁ g₂ / c ^ 2 + cst₁ g₁ g₂ ^ 2 / c ^ 3

/-- **The energy at infinity, with rate**: for `c > 0`, `0 ≤ χ < c²`, `g` twice differentiable on `[−1, 1]` and
`ξ ≥ 2`, `|E(ξ) − A²/c| ≤ K/ξ` with `A = g(1) + g(−1)`. -/
theorem energy_sub_le {g g₁ g₂ : ℝ → ℝ} {c χ ξ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hξ : 2 ≤ ξ) :
    |energy (aP c χ) (psi c g) (rungU c g) ξ - ampl g ^ 2 / c| ≤ energyRate c g g₁ g₂ / ξ := by
  have hξ1 : 1 ≤ ξ := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hψ := psi_sub_le hg hg₁ hg₂c (by positivity : c * ξ ≠ 0)
  have hu := u_sub_le hg hg₁ hg₂c hc hξ1
  have hu' : |rungU c g ξ - ampl g * ξ * cos (c * ξ)| ≤ cstU c g g₁ g₂ := by
    refine hu.trans ?_
    unfold cstU ampl
    gcongr
    exact div_le_self (abs_nonneg _) hξ1
  exact energy_alg_le hc hξ (le_aP_far hχc.le hξ1) (Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.aP_le hc hχ0 hξ1)
    (cstU_nonneg hc) hψ hu'

/-- **The energy at infinity**: `E(ξ) → A²/c` as `ξ → ∞`, `A = g(1) + g(−1)`. -/
theorem tendsto_energy {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (energy (aP c χ) (psi c g) (rungU c g)) atTop (𝓝 (ampl g ^ 2 / c)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun ξ => energyRate c g g₁ g₂ / ξ) (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_ge_atTop 2] with ξ hξ
  rw [Real.norm_eq_abs]
  exact energy_sub_le hg hg₁ hg₂c hc hχ0 hχc hξ

/-- **The connection identity**: for even `g` with `psi c g = μ g` on `[−1, 1]`,
`(c/2π) μ² · A²/c = (2/π) ψ(1)²`. -/
theorem connection_identity {g : ℝ → ℝ} {c μ : ℝ} (hc : c ≠ 0) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    c / (2 * π) * μ ^ 2 * (ampl g ^ 2 / c) = 2 / π * psi c g 1 ^ 2 := by
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  unfold ampl
  rw [heven 1 h1, hμ 1 h1]
  field_simp
  ring

/-- The connection identity in the mirror eigenvalue `τ = μ √(c/2π)`: `τ² · A²/c = (2/π) ψ(1)²`. -/
theorem tau_sq_connection {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (μ * √(c / (2 * π))) ^ 2 * (ampl g ^ 2 / c) = 2 / π * psi c g 1 ^ 2 := by
  rw [mul_pow, sq_sqrt (by positivity), ← connection_identity hc.ne' heven hμ]
  ring

end Cvs.Prolate.RungConnectionIdentity
