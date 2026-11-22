import Mathlib
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.TailOfModes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.ModeMellinDyadicRange
import Cvs.Prolate.Mellin.ModesMellinSummed
import Cvs.Prolate.ModeSmoothWeightByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole and Mellin values of the tail of `M` modes

With `|u(ξ)| ≤ ξU` and `σ² = c² − χ`: `|∫F| ≤ (π²/6)(2U/σ² + 2c²U/σ⁴)`, `|∫F/θ| ≤ (π²/6)(2U/σ² + 3c²U/(2σ⁴))`;
and for `|t| ≤ T`, `2T² + ½ ≤ σ²`, the Mellin values `|∫F y_t|, |∫F ỹ_t|` obey `ModesMellinSummed`'s bound at `Y = 1`, `V = T + ½`.
-/

namespace Cvs.L2a.TailModesPoleMellinValues

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes

variable {c χ U b Ξ : ℝ} {ψ u : ℝ → ℝ} {M : ℕ}

/-- **The pole value `∫F`.** -/
theorem pole_plus_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hb : 1 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hU : 0 ≤ U) (hu : ∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc 1 Ξ, |u ξ| ≤ ξ * U) (hcont : ContinuousOn ψ (Icc 1 Ξ)) :
    |∫ θ in Ioi 1, tailF ψ M b θ|
      ≤ π ^ 2 / 6 * (2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2) := by
  have hd : 0 < c ^ 2 - χ := by linarith
  have hin : ∀ m ∈ Finset.Icc 1 M, Icc ((m : ℝ) * 1) (m * b) ⊆ Icc 1 Ξ := fun m hm ξ hξ => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    exact ⟨by nlinarith [hξ.1], hξ.2.trans (by nlinarith)⟩
  have e : ∫ θ in Ioi 1, tailF ψ M b θ = ∫ θ in Ioi 1, tailF ψ M b θ * (fun _ => (1 : ℝ)) θ := by simp
  rw [e, integral_tailF_mul ψ _ M hb (fun m hm => by
    simp only [mul_one]
    exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ => hin m hm ⟨mul_le_mul_of_nonneg_left hθ.1 (Nat.cast_nonneg m), mul_le_mul_of_nonneg_left hθ.2 (Nat.cast_nonneg m)⟩))]
  simp only [mul_one]
  calc |∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, ψ (m * θ)|
      ≤ ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b, ψ (m * θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
        apply Finset.sum_le_sum; intro m hm
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have key := Cvs.Prolate.ModeSmoothWeightByParts.mode_one_le (m := m) (s := 1) (t := b) hc hχ0 hχ hm1 le_rfl hb hU
          (fun ξ hξ => hu ξ (hin m hm hξ)) (fun ξ hξ => hub ξ (hin m hm hξ)) (hcont.mono (hin m hm))
        refine key.trans (le_of_eq ?_)
        field_simp
    _ = (2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M) (by positivity)

/-- **The pole value `∫F/θ`.** -/
theorem pole_minus_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hb : 1 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hU : 0 ≤ U) (hu : ∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hub : ∀ ξ ∈ Icc 1 Ξ, |u ξ| ≤ ξ * U) (hcont : ContinuousOn ψ (Icc 1 Ξ)) :
    |∫ θ in Ioi 1, tailF ψ M b θ / θ|
      ≤ π ^ 2 / 6 * (2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2)) := by
  have hd : 0 < c ^ 2 - χ := by linarith
  have hin : ∀ m ∈ Finset.Icc 1 M, Icc ((m : ℝ) * 1) (m * b) ⊆ Icc 1 Ξ := fun m hm ξ hξ => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    exact ⟨by nlinarith [hξ.1], hξ.2.trans (by nlinarith)⟩
  have e : ∫ θ in Ioi 1, tailF ψ M b θ / θ = ∫ θ in Ioi 1, tailF ψ M b θ * (fun θ => 1 / θ) θ := by
    congr 1; funext θ; simp [div_eq_mul_inv]
  rw [e, integral_tailF_mul ψ _ M hb (fun m hm => by
    apply ContinuousOn.mul
    · exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ => hin m hm ⟨mul_le_mul_of_nonneg_left hθ.1 (Nat.cast_nonneg m), mul_le_mul_of_nonneg_left hθ.2 (Nat.cast_nonneg m)⟩)
    · exact continuousOn_const.div continuousOn_id (fun θ hθ => by linarith [hθ.1]))]
  calc |∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ)|
      ≤ ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2)) * (1 / (m : ℝ) ^ 2) := by
        apply Finset.sum_le_sum; intro m hm
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have key := Cvs.Prolate.ModeSmoothWeightByParts.mode_inv_le (m := m) (s := 1) (t := b) hc hχ0 hχ hm1 le_rfl hb hU
          (fun ξ hξ => hu ξ (hin m hm hξ)) (fun ξ hξ => hub ξ (hin m hm hξ)) (hcont.mono (hin m hm))
        have e2 : ∫ θ in (1 : ℝ)..b, ψ (m * θ) * (1 / θ) = ∫ θ in (1 : ℝ)..b, ψ (m * θ) / θ := by
          congr 1; funext θ; ring
        rw [e2]
        refine key.trans (le_of_eq ?_)
        field_simp
    _ = (2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2)) * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M) (by positivity)

/-- The bound Cvs.Prolate.Mellin.ModesMellinSummed gives, at `Y = 1`, `V = T + ½`. -/
noncomputable def mellinBound (c χ G η T : ℝ) (ψ1 : ℝ) : ℝ :=
  η * |ψ1| * 1 + 8 * √2 * |ψ1| * (T + 1 / 2) / (c * √(c ^ 2 - χ)) + 32 * √2 * √(c * G) * 1 / (c ^ 2 - χ)
    + 2 * Cvs.Prolate.Mellin.ModeMellinDyadicRange.P c χ 1 G 1 (T + 1 / 2) 2
    + π ^ 2 / 6 * (16 / 3 * ((T + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) + 1 * √(2 * c * G)) / c ^ 2)

/-- **The Mellin values of the tail** below `T`, for either kernel. -/
theorem mellin_le {G η T t : ℝ} (J : ℕ) {y v : ℝ → ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hT : 2 * T ^ 2 + 1 / 2 ≤ c ^ 2 - χ) (ht : |t| ≤ T) (hG0 : 0 ≤ G) (hη : 0 < η)
    (hηθ : 1 + η ≤ √(1 + √(c ^ 2 - χ) / c))
    (hψ : ∀ ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)), energy (aP c χ) ψ u ξ ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 ((M : ℝ) * 2 ^ (J + 1)))) (hM : 1 ≤ M)
    (hedge : ∀ ξ ∈ Icc (1 : ℝ) 2, |ψ ξ| ≤ |ψ 1|)
    (hy : ∀ τ, 0 < τ → HasDerivAt (y t) (v t τ / τ ^ 2) τ)
    (hv : ∀ τ, 0 < τ → HasDerivAt (v t) (-((t ^ 2 + 1 / 4) * y t τ)) τ)
    (hyb : ∀ τ, 0 < τ → |y t τ| ≤ 1 / √τ) (hvb : ∀ τ, 0 < τ → |v t τ| ≤ (|t| + 1 / 2) * √τ) :
    |∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ * y t θ| ≤ mellinBound c χ G η T (ψ 1) := by
  have hpow : (1 : ℝ) ≤ 2 ^ (J + 1) := one_le_pow₀ (by norm_num)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsubc : Icc (1 : ℝ) (2 ^ (J + 1)) ⊆ Icc 1 ((M : ℝ) * 2 ^ (J + 1)) := fun ξ hξ =>
    ⟨hξ.1, hξ.2.trans (by nlinarith)⟩
  rw [integral_tailF_mul ψ (y t) M hpow (fun m hm => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    apply ContinuousOn.mul
    · exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
        ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩)
    · exact fun θ hθ => (hy θ (by linarith [hθ.1])).continuousAt.continuousWithinAt)]
  have hw : 0 ≤ t ^ 2 + 1 / 4 := by positivity
  have hgap : 2 * (t ^ 2 + 1 / 4) ≤ c ^ 2 - χ := by
    have : t ^ 2 ≤ T ^ 2 := by
      have := sq_abs t ▸ pow_le_pow_left₀ (abs_nonneg t) ht 2; linarith
    linarith
  have hV : 0 ≤ T + 1 / 2 := by linarith [abs_nonneg t]
  have key := Cvs.Prolate.Mellin.ModesMellinSummed.modes_le (ψ := ψ) (u := u) (y := y t) (v := v t) (Y := 1) (V := T + 1 / 2)
    J M hc hχ0 hχ hw hgap hG0 zero_le_one hV hη hηθ hψ hu hG (hcont.mono hsubc) hedge
    (fun τ hτ => hy τ (by linarith [hτ.1])) (fun τ hτ => hv τ (by linarith [hτ.1]))
    (fun τ hτ => hyb τ (by linarith [hτ.1]))
    (fun τ hτ => (hvb τ (by linarith [hτ.1])).trans (mul_le_mul_of_nonneg_right (by linarith) (sqrt_nonneg _)))
  unfold mellinBound
  exact key

end Cvs.L2a.TailModesPoleMellinValues
