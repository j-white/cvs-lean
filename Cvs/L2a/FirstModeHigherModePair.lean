import Mathlib
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.StationaryPairAtDelta
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
# The first mode against a higher mode, at one scale

For `n ≥ 2` and window scale `1 ≤ s`, `s² ≤ c`: `|∫_1^b ψ(nθ) ψ(θ)| ≤ G X_n`,
`X_n = (4A/s)[s < 6n]/n² + (A/c + 2Q/s)[6n ≤ s]/n + κ₀'(16s√c/(3c²) + 16s/c² + 16s/(3c²))/n² + 16κ₀'√s/(c² n√n)`
(Cvs.L2a.StationaryPairAtDelta at `k = 1`), `κ₀' = √(c/σ)`; summed over `n`, `Σ X_n ≤ X`, closed form (Cvs.L2a.TailCrossModeCounts).
-/

namespace Cvs.L2a.FirstModeHigherModePair

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.StationaryPairsWeightedTotal (Aw Qw κw)

/-- The per-mode stationary bound at `k = 1`. -/
noncomputable def X (c χ K s n : ℝ) : ℝ :=
  4 * Aw c χ K / s * (if s < 6 * n then 1 / n ^ 2 else 0) + (Aw c χ K / c + 2 * Qw c χ / s) * (if 6 * n ≤ s then 1 / n else 0)
    + κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2)
    + 16 * κw c χ * √s / c ^ 2 * (1 / (n * √n))

theorem X_nonneg {c χ K s n : ℝ} (hc : 0 < c) (hs : 0 < s) (hn : 0 < n) (hK : 0 ≤ K) (hχ : χ < c ^ 2) :
    0 ≤ X c χ K s n := by
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hQ : 0 ≤ Qw c χ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have h1 : 0 ≤ (if s < 6 * n then 1 / n ^ 2 else 0) := by split_ifs <;> positivity
  have h2 : 0 ≤ (if 6 * n ≤ s then 1 / n else 0) := by split_ifs <;> positivity
  unfold X
  have t1 : 0 ≤ 4 * Aw c χ K / s * (if s < 6 * n then 1 / n ^ 2 else 0) := mul_nonneg (by positivity) h1
  have t2 : 0 ≤ (Aw c χ K / c + 2 * Qw c χ / s) * (if 6 * n ≤ s then 1 / n else 0) := mul_nonneg (by positivity) h2
  have t3 : 0 ≤ κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2) := by
    positivity
  have t4 : 0 ≤ 16 * κw c χ * √s / c ^ 2 * (1 / (n * √n)) := by positivity
  linarith

/-- **The first mode against the mode `n ≥ 2`.** -/
theorem first_cross_le {c χ G K Ξ b s n : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c) (hn : 2 ≤ n) (hs1 : 1 ≤ s)
    (hsc : s ^ 2 ≤ c) (hb : 3 ≤ b) (hhi : n * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ θ in (1 : ℝ)..b, ψ (n * θ) * ψ θ| ≤ G * X c χ K s n := by
  have hc0 : 0 < c := by linarith
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < s := by linarith
  have hsn : 0 < √n := sqrt_pos.mpr hn0
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have e : ∫ θ in (1 : ℝ)..b, ψ (n * θ) * ψ θ = ∫ t in (1 : ℝ)..b, ψ (n * t) * ψ (1 / 1 * t) := by
    congr 1; funext t; simp
  rw [e]
  have hkm : (2 : ℝ) ≤ 1 * n := by linarith
  by_cases h : 6 * (1 * n) ≤ s
  · have key := Cvs.L2a.StationaryPairAtDelta.strip_mono (k := 1) (m := n) (s := s) hc hχ0 hχ hχs le_rfl hkm (by linarith)
      hs1 hsc h (by linarith) hhi hψ hu hG hG0 hK hcont hedge hedge1
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    unfold X
    rw [if_neg (by linarith), if_pos (by linarith)]
    change Aw c χ K / (c * n) + 2 * Qw c χ / (s * n)
        + κw c χ * (16 * s * √c / (3 * c ^ 2 * 1 ^ 2 * n ^ 3) + 16 * s / (c ^ 2 * 1 * n ^ 2)
          + 8 * √s / (c ^ 2 * √1 * (n * √n))) ≤ _
    rw [sqrt_one]
    have hn3 : 16 * s * √c / (3 * c ^ 2 * 1 ^ 2 * n ^ 3) ≤ 16 * s * √c / (3 * c ^ 2) * (1 / n ^ 2) := by
      rw [show 16 * s * √c / (3 * c ^ 2) * (1 / n ^ 2) = 16 * s * √c / (3 * c ^ 2 * 1 ^ 2 * n ^ 2) by field_simp]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : n ^ 2 ≤ n ^ 3 := by nlinarith
      nlinarith [this]
    have e1 : Aw c χ K / (c * n) + 2 * Qw c χ / (s * n) = (Aw c χ K / c + 2 * Qw c χ / s) * (1 / n) := by field_simp
    have e2 : 16 * s / (c ^ 2 * 1 * n ^ 2) = 16 * s / c ^ 2 * (1 / n ^ 2) := by field_simp
    have e3 : 8 * √s / (c ^ 2 * 1 * (n * √n)) = 8 * √s / c ^ 2 * (1 / (n * √n)) := by field_simp
    have p1 : 0 ≤ 16 * s / (3 * c ^ 2) * (1 / n ^ 2) := by positivity
    have p2 : 0 ≤ 8 * √s / c ^ 2 * (1 / (n * √n)) := by positivity
    rw [e1, e2, e3]
    have : κw c χ * (16 * s * √c / (3 * c ^ 2 * 1 ^ 2 * n ^ 3) + 16 * s / c ^ 2 * (1 / n ^ 2)
        + 8 * √s / c ^ 2 * (1 / (n * √n)))
        ≤ κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2)
          + 16 * κw c χ * √s / c ^ 2 * (1 / (n * √n)) := by
      have hh : 16 * s * √c / (3 * c ^ 2 * 1 ^ 2 * n ^ 3) + 16 * s / c ^ 2 * (1 / n ^ 2)
          + 8 * √s / c ^ 2 * (1 / (n * √n))
          ≤ (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2)
            + 2 * (8 * √s / c ^ 2 * (1 / (n * √n))) := by
        have : (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2)
            = 16 * s * √c / (3 * c ^ 2) * (1 / n ^ 2) + 16 * s / c ^ 2 * (1 / n ^ 2)
              + 16 * s / (3 * c ^ 2) * (1 / n ^ 2) := by ring
        linarith
      calc _ ≤ κw c χ * ((16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2)
              + 2 * (8 * √s / c ^ 2 * (1 / (n * √n)))) := mul_le_mul_of_nonneg_left hh hκ
        _ = _ := by ring
    have p0 : 0 ≤ 4 * Aw c χ K / s * 0 := by simp
    linarith
  · have key := Cvs.L2a.StationaryPairAtDelta.edge_mono (k := 1) (m := n) (s := s) hc hχ0 hχ le_rfl hkm (by linarith)
      hs1 (lt_of_not_ge h) (by linarith) hhi hψ hu hG hG0 hK hcont hedge hedge1
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    unfold X
    rw [if_pos (by linarith), if_neg (by linarith)]
    change 4 * Aw c χ K / (s * 1 * n ^ 2)
        + κw c χ * (16 * s / (3 * c ^ 2 * 1 * n ^ 2) + 16 * √s / (c ^ 2 * √1 * (n * √n))) ≤ _
    rw [sqrt_one]
    have e1 : 4 * Aw c χ K / (s * 1 * n ^ 2) = 4 * Aw c χ K / s * (1 / n ^ 2) := by field_simp
    have e2 : 16 * s / (3 * c ^ 2 * 1 * n ^ 2) = 16 * s / (3 * c ^ 2) * (1 / n ^ 2) := by field_simp
    have e3 : 16 * √s / (c ^ 2 * 1 * (n * √n)) = 16 * √s / c ^ 2 * (1 / (n * √n)) := by field_simp
    rw [e1, e2, e3]
    have p1 : 0 ≤ κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2) * (1 / n ^ 2) := by positivity
    have p2 : 0 ≤ (Aw c χ K / c + 2 * Qw c χ / s) * 0 := by simp
    have : κw c χ * (16 * s / (3 * c ^ 2) * (1 / n ^ 2) + 16 * √s / c ^ 2 * (1 / (n * √n)))
        = κw c χ * (16 * s / (3 * c ^ 2)) * (1 / n ^ 2) + 16 * κw c χ * √s / c ^ 2 * (1 / (n * √n)) := by ring
    have hsplit : κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (1 / n ^ 2)
        = κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2) * (1 / n ^ 2)
          + κw c χ * (16 * s / (3 * c ^ 2)) * (1 / n ^ 2) := by ring
    linarith

/-- The closed form of `Σ_n X_n`. -/
noncomputable def Xbar (c χ K s : ℝ) : ℝ :=
  4 * Aw c χ K / s * (3 * √(6 / s)) + (Aw c χ K / c + 2 * Qw c χ / s) * (1 + log s)
    + κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (π ^ 2 / 6)
    + 16 * κw c χ * √s / c ^ 2 * 3

/-- **The modes summed**: `Σ_{n ≤ M} X_n ≤ X̄`, uniformly in `M`. -/
theorem X_sum_le {c χ K s : ℝ} (M : ℕ) (hc : 0 < c) (hs : 1 ≤ s) (hK : 0 ≤ K) (hχ : χ < c ^ 2) :
    ∑ n ∈ Finset.Icc 1 M, X c χ K s n ≤ Xbar c χ K s := by
  have hs0 : 0 < s := by linarith
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hQ : 0 ≤ Qw c χ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  unfold X Xbar
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := Cvs.L2a.TailCrossModeCounts.edge_count M hs0
  have h2 := Cvs.L2a.TailCrossModeCounts.strip_harm M hs
  have h3 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M
  have h4 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_mul_sqrt_le M
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * Aw c χ K / s)
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Aw c χ K / c + 2 * Qw c χ / s)
  have g3 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)))
  have g4 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 16 * κw c χ * √s / c ^ 2)
  linarith

end Cvs.L2a.FirstModeHigherModePair
