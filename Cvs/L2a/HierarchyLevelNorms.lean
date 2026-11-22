import Mathlib
import Cvs.L2a.DilatedVNormMasses
import Cvs.L2a.HierarchyLeafMasses
import Cvs.L2a.RungChiHierarchy
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The level norms against the mass sum

With `0 ≤ χ_i ≤ χ`, `|χ_i − χ̄| ≤ S` and `M_i ≥ 0`, the `χ`-weighted mass sums are at most `χ^{2k}` and
`S²χ^{2k}` times `N₀ = Σ a_i²M_i`, so the norm of the level `k` of a dilation is at most `(1/m)χ^{2k}N₀` (Cvs.L2a.HierarchyLeafMasses)
and `(1 − ε/2)` times its `V`-norm on `[L, R]` at most `V χ^{2k} N₀`, `V = (A/2ε + 1 + δ/2)/m + B m³ S²/2δ`
(Cvs.L2a.DilatedVNormMasses on the bump interval `[L − h, R + h]`): every norm of the hierarchy in units of `N₀`.
-/

namespace Cvs.L2a.HierarchyLevelNorms

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Σ (a_i χ_i^k)² M_i ≤ χ^{2k} Σ a_i² M_i` for `0 ≤ χ_i ≤ χ`, `M_i ≥ 0`. -/
theorem mass_sum_le {a χ Mm : ι → ℝ} {χm : ℝ} (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hM : ∀ i, 0 ≤ Mm i) (k : ℕ) :
    ∑ i, (a i * χ i ^ k) ^ 2 * Mm i ≤ χm ^ (2 * k) * ∑ i, a i ^ 2 * Mm i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have h1 : χ i ^ (2 * k) ≤ χm ^ (2 * k) := pow_le_pow_left₀ (hχ i).1 (hχ i).2 _
  calc (a i * χ i ^ k) ^ 2 * Mm i = χ i ^ (2 * k) * (a i ^ 2 * Mm i) := by ring
    _ ≤ χm ^ (2 * k) * (a i ^ 2 * Mm i) := mul_le_mul_of_nonneg_right h1 (by nlinarith [sq_nonneg (a i), hM i])

/-- `Σ (a_i χ_i^k (χ_i − χ̄))² M_i ≤ S² χ^{2k} Σ a_i² M_i` when moreover `|χ_i − χ̄| ≤ S`. -/
theorem mass_sum_centred_le {a χ Mm : ι → ℝ} {χm χb S : ℝ} (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hM : ∀ i, 0 ≤ Mm i)
    (hS : ∀ i, |χ i - χb| ≤ S) (k : ℕ) :
    ∑ i, (a i * χ i ^ k * (χ i - χb)) ^ 2 * Mm i ≤ S ^ 2 * χm ^ (2 * k) * ∑ i, a i ^ 2 * Mm i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have h1 : χ i ^ (2 * k) ≤ χm ^ (2 * k) := pow_le_pow_left₀ (hχ i).1 (hχ i).2 _
  have h2 : (χ i - χb) ^ 2 ≤ S ^ 2 := by
    have := hS i; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hnn : 0 ≤ a i ^ 2 * Mm i := by nlinarith [sq_nonneg (a i), hM i]
  calc (a i * χ i ^ k * (χ i - χb)) ^ 2 * Mm i = (χ i - χb) ^ 2 * χ i ^ (2 * k) * (a i ^ 2 * Mm i) := by ring
    _ ≤ S ^ 2 * χm ^ (2 * k) * (a i ^ 2 * Mm i) := by
        apply mul_le_mul_of_nonneg_right _ hnn
        exact mul_le_mul h2 h1 (pow_nonneg (hχ i).1 _) (sq_nonneg _)

/-- **The norm of a level** on `[L, R]`, `1 ≤ mL`: `∫ G_k(mθ)² ≤ (1/m) χ^{2k} N₀`. -/
theorem level_norm_le {m L R : ℝ} {a χ Mm : ι → ℝ} {χm : ℝ} {ψ : ι → ℝ → ℝ} (K : ι → ι → ℝ) (k : ℕ)
    (hm : 0 < m) (hL : 1 ≤ m * L) (hLR : L ≤ R)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hM : ∀ i, 0 ≤ Mm i) (hcont : ∀ i, ContinuousOn (ψ i) (Ici 1))
    (hcross : ∀ i j, i ≠ j → ∀ t, m * R ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, m * R ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i) :
    ∫ θ in L..R, Gk a χ ψ k (m * θ) ^ 2 ≤ 1 / m * (χm ^ (2 * k) * ∑ i, a i ^ 2 * Mm i) := by
  have h := Cvs.L2a.HierarchyLeafMasses.dilated_norm_le hm hL hLR ψ (fun i => a i * χ i ^ k) K Mm hcont hcross hmass
  have e : (fun θ => Gk a χ ψ k (m * θ) ^ 2) = fun θ => (∑ i, (a i * χ i ^ k) * ψ i (m * θ)) ^ 2 := by
    funext θ; rfl
  rw [e]
  calc _ ≤ 1 / m * ∑ i, (a i * χ i ^ k) ^ 2 * Mm i := h
    _ ≤ _ := mul_le_mul_of_nonneg_left (mass_sum_le hχ hM k) (by positivity)

/-- **The `V`-norm of a level** on `[L, R]` through the bump on `[L − h, R + h]`:
`(1 − ε/2) ∫_L^R (mU_k(m·))²/((m²θ² − 1) q̄) ≤ ((A/2ε + 1 + δ/2)/m + B m³ S²/2δ) χ^{2k} N₀`. -/
theorem level_V_norm_le {c m χb L R h ε δ A B : ℝ} {a χ Mm : ι → ℝ} {χm S : ℝ} {ψ u : ι → ℝ → ℝ}
    (K : ι → ι → ℝ) (k : ℕ)
    (hm : 0 < m) (hh : 0 < h) (hα : 1 < m * (L - h)) (hχb : χb < c ^ 2 * m ^ 2 * (L - h) ^ 2) (hLR : L ≤ R)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hM : ∀ i, 0 ≤ Mm i) (hS : ∀ i, |χ i - χb| ≤ S)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, m * (R + h) ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, m * (R + h) ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hA : ∀ θ ∈ Icc (L - h) (R + h), 2 * (m ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
        + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3) ≤ A)
    (hB : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 2 ≤ B) :
    (1 - ε / 2) * ∫ θ in L..R,
        (m * Gk a χ u k (m * θ)) ^ 2 / ((m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb))
      ≤ ((A / (2 * ε) + 1 + δ / 2) / m + B * m ^ 3 * S ^ 2 / (2 * δ)) * (χm ^ (2 * k) * ∑ i, a i ^ 2 * Mm i) := by
  have hαβ : L - h + h ≤ R + h - h := by linarith
  have hV := Cvs.L2a.DilatedVNormMasses.V_norm_masses (a := a) (α := L - h) (β := R + h) K Mm k hm hα hχb hh hαβ hε hε2 hδ hψ hu
    hψc huc hcross hmass hA hB
  have e1 : L - h + h = L := by ring
  have e2 : R + h - h = R := by ring
  rw [e1, e2] at hV
  have hA0 : 0 ≤ A := by
    have := hA (L - h) ⟨le_rfl, by linarith⟩
    have hp : 0 < m ^ 2 * (L - h) ^ 2 - 1 := by nlinarith
    have hq : 0 < c ^ 2 * m ^ 4 * (L - h) ^ 2 - m ^ 2 * χb := by
      have : 0 < m ^ 2 * (c ^ 2 * m ^ 2 * (L - h) ^ 2 - χb) := mul_pos (by positivity) (by linarith)
      nlinarith
    exact le_trans (by positivity) this
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB (L - h) ⟨le_rfl, by linarith⟩)
  have hN0 : 0 ≤ ∑ i, a i ^ 2 * Mm i := Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (a i), hM i]
  calc _ ≤ _ := hV
    _ ≤ (A / (2 * ε) + 1 + δ / 2) * (1 / m * (χm ^ (2 * k) * ∑ i, a i ^ 2 * Mm i))
          + B * m ^ 3 / (2 * δ) * (S ^ 2 * χm ^ (2 * k) * ∑ i, a i ^ 2 * Mm i) := by
        gcongr
        · exact mass_sum_le hχ hM k
        · exact mass_sum_centred_le hχ hM hS k
    _ = _ := by field_simp

end Cvs.L2a.HierarchyLevelNorms
