import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `χ`-hierarchy of a combination of rungs, and its dilations

For rungs `ψ_i' = u_i/p`, `u_i' = −(c²ξ² − χ_i)ψ_i` with the same `p = ξ² − 1`, the combinations
`G_k = Σ a_iχ_i^kψ_i`, `U_k = Σ a_iχ_i^ku_i` satisfy `G_k' = U_k/p` and `U_k' = −c²ξ²G_k + G_{k+1}`: the `χ`-free
equation with the next level as source. Dilated by `m`, `f = G_k(m·)` has `f' = mU_k(m·)/(m²θ² − 1)` and
`(mU_k(m·))' = −c²m⁴θ² f + m²G_{k+1}(m·)`, the form the cross identity with sources takes.
-/

namespace Cvs.L2a.RungChiHierarchy

open Real Set Finset Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {ι : Type} [Fintype ι]

/-- `G_k = Σ_i a_i χ_i^k ψ_i`. -/
def Gk (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) (k : ℕ) (ξ : ℝ) : ℝ := ∑ i, a i * χ i ^ k * ψ i ξ

/-- **The hierarchy**: `G_k' = U_k/p` and `U_k' = −c²ξ²G_k + G_{k+1}` at every `ξ` where the rungs solve their
equations. -/
theorem hasDerivAt_Gk {c : ℝ} {a χ : ι → ℝ} {ψ u : ι → ℝ → ℝ} {ξ : ℝ} (k : ℕ)
    (hψ : ∀ i, HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ) :
    HasDerivAt (Gk a χ ψ k) (Gk a χ u k ξ / pP ξ) ξ ∧
    HasDerivAt (Gk a χ u k) (-(c ^ 2 * ξ ^ 2 * Gk a χ ψ k ξ) + Gk a χ ψ (k + 1) ξ) ξ := by
  constructor
  · have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i => fun ξ => a i * χ i ^ k * ψ i ξ)
      (A' := fun i => a i * χ i ^ k * (u i ξ / pP ξ)) (fun i _ => (hψ i).const_mul _)
    refine h.congr_deriv ?_
    unfold Gk; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
  · have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i => fun ξ => a i * χ i ^ k * u i ξ)
      (A' := fun i => a i * χ i ^ k * -(qP c (χ i) ξ * ψ i ξ)) (fun i _ => (hu i).const_mul _)
    refine h.congr_deriv ?_
    unfold Gk qP; rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring

/-- **The dilated hierarchy**: `f = G_k(m·)` has `f' = mU_k(m·)/(m²θ² − 1)` and
`(mU_k(m·))' = −c²m⁴θ² f + m²G_{k+1}(m·)`. -/
theorem hasDerivAt_Gk_dilate {c m : ℝ} {a χ : ι → ℝ} {ψ u : ι → ℝ → ℝ} {θ : ℝ} (k : ℕ)
    (hψ : ∀ i, HasDerivAt (ψ i) (u i (m * θ) / pP (m * θ)) (m * θ))
    (hu : ∀ i, HasDerivAt (u i) (-(qP c (χ i) (m * θ) * ψ i (m * θ))) (m * θ)) :
    HasDerivAt (fun θ => Gk a χ ψ k (m * θ)) (m * Gk a χ u k (m * θ) / (m ^ 2 * θ ^ 2 - 1)) θ ∧
    HasDerivAt (fun θ => m * Gk a χ u k (m * θ))
      (-(c ^ 2 * m ^ 4 * θ ^ 2 * Gk a χ ψ k (m * θ)) + m ^ 2 * Gk a χ ψ (k + 1) (m * θ)) θ := by
  obtain ⟨hG, hU⟩ := hasDerivAt_Gk (c := c) (a := a) (χ := χ) (ξ := m * θ) k hψ hu
  have hm : HasDerivAt (fun θ : ℝ => m * θ) m θ := by simpa using (hasDerivAt_id θ).const_mul m
  constructor
  · have h := hG.comp θ hm
    refine h.congr_deriv ?_
    unfold pP; ring
  · have h := (hU.comp θ hm).const_mul m
    refine h.congr_deriv ?_
    ring

end Cvs.L2a.RungChiHierarchy
