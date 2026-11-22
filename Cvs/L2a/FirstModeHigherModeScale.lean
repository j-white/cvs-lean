import Mathlib
import Cvs.L2a.ExactRootPairMonomials
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailCrossModeCounts
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first mode against a higher mode at one scale, for every `χ < c²`

For `n ≥ 2`, `1 ≤ s`, `s² ≤ c`, `ℓ ≤ (c² − χ)/c²`, `L = 5/ℓ + 1`, `W = √(10/(√3ℓ))/σ`, `s' = (3/5)sℓ`:
`|∫_1^b ψ(nθ)ψ(θ)| ≤ G X_n`, `X_n = (LA/s)[s' < 6n]/n² + (A/c + 2W/s)[6n ≤ s']/n + κ(32s√c/(9c²) + 20s/c² + 64s/(9c²))/n²
+ 32√L κ√s/(3c² n√n)` (Cvs.L2a.ExactRootPairMonomials at `k = 1`); summed over `n`, `Σ X_n ≤ X̄`, closed form (Cvs.L2a.TailCrossModeCounts).
-/

namespace Cvs.L2a.FirstModeHigherModeScale

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.StationaryPairsWeightedTotal (Aw κw)

/-- The window weight `W = √(10/(√3ℓ))/σ`. -/
noncomputable def Ww (c χ ℓ : ℝ) : ℝ := √(10 / (√3 * ℓ)) / √(c ^ 2 - χ)

/-- `X_n`. -/
noncomputable def X (c χ K s ℓ n : ℝ) : ℝ :=
  (5 / ℓ + 1) * Aw c χ K / s * (if 3 / 5 * (s * ℓ) < 6 * n then 1 / n ^ 2 else 0)
    + (Aw c χ K / c + 2 * Ww c χ ℓ / s) * (if 6 * n ≤ 3 / 5 * (s * ℓ) then 1 / n else 0)
    + κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2 + 64 * s / (9 * c ^ 2)) * (1 / n ^ 2)
    + 32 * √(5 / ℓ + 1) * κw c χ * √s / (3 * c ^ 2) * (1 / (n * √n))

theorem X_nonneg {c χ K s ℓ n : ℝ} (hc : 0 < c) (hs : 0 < s) (hn : 0 < n) (hℓ : 0 < ℓ) :
    0 ≤ X c χ K s ℓ n := by
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hW : 0 ≤ Ww c χ ℓ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have h1 : 0 ≤ (if 3 / 5 * (s * ℓ) < 6 * n then 1 / n ^ 2 else 0) := by split_ifs <;> positivity
  have h2 : 0 ≤ (if 6 * n ≤ 3 / 5 * (s * ℓ) then 1 / n else 0) := by split_ifs <;> positivity
  unfold X
  have t1 : 0 ≤ (5 / ℓ + 1) * Aw c χ K / s * (if 3 / 5 * (s * ℓ) < 6 * n then 1 / n ^ 2 else 0) :=
    mul_nonneg (by positivity) h1
  have t2 : 0 ≤ (Aw c χ K / c + 2 * Ww c χ ℓ / s) * (if 6 * n ≤ 3 / 5 * (s * ℓ) then 1 / n else 0) :=
    mul_nonneg (by positivity) h2
  have t3 : 0 ≤ κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2 + 64 * s / (9 * c ^ 2)) * (1 / n ^ 2) := by
    positivity
  have t4 : 0 ≤ 32 * √(5 / ℓ + 1) * κw c χ * √s / (3 * c ^ 2) * (1 / (n * √n)) := by positivity
  linarith

set_option maxHeartbeats 2000000 in
/-- **The first mode against the mode `n`**, for every `χ < c²`. -/
theorem first_cross_le {c χ G K Ξ b s ℓ n : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2)
    (hn : 2 ≤ n) (hs1 : 1 ≤ s) (hsc : s ^ 2 ≤ c) (hb : 3 ≤ b) (hhi : n * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ θ in (1 : ℝ)..b, ψ (n * θ) * ψ θ| ≤ G * X c χ K s ℓ n := by
  have hc0 : 0 < c := by linarith
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < s := by linarith
  have hsn : 0 < √n := sqrt_pos.mpr hn0
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hW : 0 ≤ Ww c χ ℓ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have h5ℓ : 0 < 5 / ℓ := by positivity
  have hL1 : 1 ≤ √(5 / ℓ + 1) := Real.le_sqrt_of_sq_le (by linarith)
  have e : ∫ θ in (1 : ℝ)..b, ψ (n * θ) * ψ θ = ∫ t in (1 : ℝ)..b, ψ (n * t) * ψ (1 / 1 * t) := by
    congr 1; funext t; simp
  rw [e]
  have hkm : (2 : ℝ) ≤ 1 * n := by linarith
  by_cases h : 10 * (1 * n) ≤ s * ℓ
  · have key := Cvs.L2a.ExactRootPairMonomials.strip_mono (k := 1) (m := n) (s := s) hc hχ0 hχ hℓ0 hℓ le_rfl hkm
      (by linarith) hs1 hsc h (by linarith) hhi hψ hu hG hG0 hK hcont hedge hedge1
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    unfold X
    rw [if_neg (by linarith), if_pos (by linarith)]
    change Aw c χ K / (c * n) + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (s * n)
        + κw c χ * (32 * s * √c / (9 * c ^ 2 * 1 ^ 2 * n ^ 3) + 20 * s / (c ^ 2 * 1 * n ^ 2)
          + 32 * √s / (3 * c ^ 2 * √1 * (n * √n))) ≤ _
    rw [sqrt_one]
    have hn3 : 32 * s * √c / (9 * c ^ 2 * 1 ^ 2 * n ^ 3) ≤ 32 * s * √c / (9 * c ^ 2) * (1 / n ^ 2) := by
      rw [show 32 * s * √c / (9 * c ^ 2) * (1 / n ^ 2) = 32 * s * √c / (9 * c ^ 2 * 1 ^ 2 * n ^ 2) by field_simp]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : n ^ 2 ≤ n ^ 3 := by nlinarith
      nlinarith [this]
    have e1 : Aw c χ K / (c * n) + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (s * n)
        = (Aw c χ K / c + 2 * Ww c χ ℓ / s) * (1 / n) := by unfold Ww; field_simp
    have e2 : 20 * s / (c ^ 2 * 1 * n ^ 2) = 20 * s / c ^ 2 * (1 / n ^ 2) := by field_simp
    have e3 : 32 * √s / (3 * c ^ 2 * 1 * (n * √n)) = 32 * √s / (3 * c ^ 2) * (1 / (n * √n)) := by field_simp
    rw [e1, e2, e3]
    have p4 : 0 ≤ κw c χ * (32 * √s / (3 * c ^ 2) * (1 / (n * √n))) := by positivity
    have p4' : κw c χ * (32 * √s / (3 * c ^ 2) * (1 / (n * √n)))
        ≤ 32 * √(5 / ℓ + 1) * κw c χ * √s / (3 * c ^ 2) * (1 / (n * √n)) := by
      have := le_mul_of_one_le_left p4 hL1
      calc _ ≤ √(5 / ℓ + 1) * (κw c χ * (32 * √s / (3 * c ^ 2) * (1 / (n * √n)))) := this
        _ = _ := by ring
    have p5 : 0 ≤ κw c χ * (64 * s / (9 * c ^ 2)) * (1 / n ^ 2) := by positivity
    have split : κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2 + 64 * s / (9 * c ^ 2)) * (1 / n ^ 2)
        = κw c χ * (32 * s * √c / (9 * c ^ 2) * (1 / n ^ 2)) + κw c χ * (20 * s / c ^ 2 * (1 / n ^ 2))
          + κw c χ * (64 * s / (9 * c ^ 2)) * (1 / n ^ 2) := by ring
    have hk3 := mul_le_mul_of_nonneg_left hn3 hκ
    have p0 : 0 ≤ (5 / ℓ + 1) * Aw c χ K / s * 0 := by simp
    nlinarith [hk3, p4', p5, split]
  · have hlt : s * ℓ < 10 * (1 * n) := lt_of_not_ge h
    have key := Cvs.L2a.ExactRootPairMonomials.edge_mono (k := 1) (m := n) (s := s) hc hχ0 hχ hℓ0 le_rfl hkm
      (by linarith) hs1 hlt (by linarith) hhi hψ hu hG hG0 hK hcont hedge hedge1
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    unfold X
    rw [if_pos (by linarith), if_neg (by linarith)]
    change (5 / ℓ + 1) * Aw c χ K / (s * 1 * n ^ 2)
        + κw c χ * (64 * s / (9 * c ^ 2 * 1 * n ^ 2)
          + 32 * √(5 / ℓ + 1) * √s / (3 * c ^ 2 * √1 * (n * √n))) ≤ _
    rw [sqrt_one]
    have e1 : (5 / ℓ + 1) * Aw c χ K / (s * 1 * n ^ 2) = (5 / ℓ + 1) * Aw c χ K / s * (1 / n ^ 2) := by
      field_simp
    have e2 : 64 * s / (9 * c ^ 2 * 1 * n ^ 2) = 64 * s / (9 * c ^ 2) * (1 / n ^ 2) := by field_simp
    have e3 : 32 * √(5 / ℓ + 1) * √s / (3 * c ^ 2 * 1 * (n * √n))
        = 32 * √(5 / ℓ + 1) * √s / (3 * c ^ 2) * (1 / (n * √n)) := by field_simp
    rw [e1, e2, e3]
    have p1 : 0 ≤ κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2) * (1 / n ^ 2) := by positivity
    have p2 : 0 ≤ (Aw c χ K / c + 2 * Ww c χ ℓ / s) * 0 := by simp
    have : κw c χ * (64 * s / (9 * c ^ 2) * (1 / n ^ 2) + 32 * √(5 / ℓ + 1) * √s / (3 * c ^ 2) * (1 / (n * √n)))
        = κw c χ * (64 * s / (9 * c ^ 2)) * (1 / n ^ 2)
          + 32 * √(5 / ℓ + 1) * κw c χ * √s / (3 * c ^ 2) * (1 / (n * √n)) := by ring
    have hsplit : κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2 + 64 * s / (9 * c ^ 2)) * (1 / n ^ 2)
        = κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2) * (1 / n ^ 2)
          + κw c χ * (64 * s / (9 * c ^ 2)) * (1 / n ^ 2) := by ring
    linarith

/-- `X̄`. -/
noncomputable def Xbar (c χ K s ℓ : ℝ) : ℝ :=
  (5 / ℓ + 1) * Aw c χ K / s * (3 * √(6 / (3 / 5 * (s * ℓ))))
    + (Aw c χ K / c + 2 * Ww c χ ℓ / s) * (1 + log (3 / 5 * (s * ℓ)))
    + κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2 + 64 * s / (9 * c ^ 2)) * (π ^ 2 / 6)
    + 32 * √(5 / ℓ + 1) * κw c χ * √s / (3 * c ^ 2) * 3

/-- **The modes summed**: `Σ_{n ≤ M} X_n ≤ X̄`, uniformly in `M`, for `(3/5)sℓ ≥ 1`. -/
theorem X_sum_le {c χ K s ℓ : ℝ} (M : ℕ) (hc : 0 < c) (hs : 1 ≤ s) (hℓ : 0 < ℓ)
    (hsℓ : 1 ≤ 3 / 5 * (s * ℓ)) :
    ∑ n ∈ Finset.Icc 1 M, X c χ K s ℓ n ≤ Xbar c χ K s ℓ := by
  have hs0 : 0 < s := by linarith
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hW : 0 ≤ Ww c χ ℓ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  unfold X Xbar
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := Cvs.L2a.TailCrossModeCounts.edge_count M (by linarith : (0 : ℝ) < 3 / 5 * (s * ℓ))
  have h2 := Cvs.L2a.TailCrossModeCounts.strip_harm M hsℓ
  have h3 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M
  have h4 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_mul_sqrt_le M
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (5 / ℓ + 1) * Aw c χ K / s)
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Aw c χ K / c + 2 * Ww c χ ℓ / s)
  have g3 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ κw c χ * (32 * s * √c / (9 * c ^ 2) + 20 * s / c ^ 2 + 64 * s / (9 * c ^ 2)))
  have g4 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 32 * √(5 / ℓ + 1) * κw c χ * √s / (3 * c ^ 2))
  linarith

end Cvs.L2a.FirstModeHigherModeScale
