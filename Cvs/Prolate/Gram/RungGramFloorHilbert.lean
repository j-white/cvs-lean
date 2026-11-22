import Mathlib
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ProlateWronskianIntegral
import Cvs.Upstream.HilbertInequalityUniformGap

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung Gram floor directly from the Wronskian form and Hilbert's inequality

For rungs `ψ_i` regular at `1` at one `c`, with pairwise gaps `|χ_i − χ_j| ≥ D`, the Gram off-diagonal is the real
bilinear Hilbert form `(u_i(b)ψ_j(b) − ψ_i(b)u_j(b))/(χ_i − χ_j)` (Cvs.Prolate.ProlateWronskianIntegral), so Cvs.Upstream.HilbertInequalityUniformGap gives, for any `A > 0`,
`∫₁ᵇ (Σ a_iψ_i)² ≥ Σ_i a_i²(∫₁ᵇ ψ_i² − (π/D)(Aψ_i(b)² + u_i(b)²/A))`: at `A = a(b)` the subtracted term is the energy.
-/

noncomputable section

namespace Cvs.Prolate.Gram.RungGramFloorHilbert

open Real Set Finset Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The rung Gram floor from Hilbert's inequality**: `∫₁ᵇ (Σ a_iψ_i)² ≥ Σ_i a_i²(∫₁ᵇ ψ_i² − (π/D)(Aψ_i(b)² + u_i(b)²/A))`. -/
theorem gram_floor_hilbert {c b D A : ℝ} (hb : 1 ≤ b) (hD : 0 < D) (hA : 0 < A)
    (χ : ι → ℝ) (ψ u : ι → ℝ → ℝ) (a : ι → ℝ) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|)
    (hψ : ∀ i, ∀ ξ ∈ Ioo 1 b, HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ ∈ Ioo 1 b, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hcψ : ∀ i, ContinuousOn (ψ i) (Icc 1 b)) (hcu : ∀ i, ContinuousOn (u i) (Icc 1 b))
    (hu1 : ∀ i, u i 1 = 0) :
    ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - π / D * (A * ψ i b ^ 2 + u i b ^ 2 / A))
      ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2 := by
  set N : ι → ι → ℝ := fun i j => ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ j ξ with hN
  have hI : ∀ i j, IntervalIntegrable (fun ξ => ψ i ξ * ψ j ξ) MeasureTheory.volume 1 b :=
    fun i j => ((hcψ i).mul (hcψ j)).intervalIntegrable_of_Icc hb
  have hsq : ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2 = ∑ i, ∑ j, a i * a j * N i j := by
    have e : ∀ ξ, (∑ i, a i * ψ i ξ) ^ 2 = ∑ i, ∑ j, a i * a j * (ψ i ξ * ψ j ξ) := by
      intro ξ; rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro i _
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl; intro j _; rw [intervalIntegral.integral_const_mul]
      · intro j _; exact (hI i j).const_mul _
    · intro i _
      have h := IntervalIntegrable.sum (Finset.univ) fun j _ => (hI i j).const_mul (a i * a j)
      simpa only [Finset.sum_fn] using h
  -- the off-diagonal is the Wronskian form
  have hoff : ∀ i j, i ≠ j → N i j = (u i b * ψ j b - ψ i b * u j b) / (χ i - χ j) := by
    intro i j hij
    have hne : χ i - χ j ≠ 0 := by
      intro h; have := hgap i j hij; rw [h, abs_zero] at this; linarith
    have h := Cvs.Prolate.ProlateWronskianIntegral.wronskian_integral (c := c) hb (hψ i) (hu i) (hψ j) (hu j) (hcψ i) (hcu i)
      (hcψ j) (hcu j) (hu1 i) (hu1 j)
    rw [eq_div_iff hne, mul_comm]; exact h
  -- split the double sum
  have hsplit : ∑ i, ∑ j, a i * a j * N i j
      = ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2)
        + 2 * ∑ i, ∑ j, (if i = j then 0 else (a i * u i b) * (a j * ψ j b) / (χ i - χ j)) := by
    have hrow : ∀ i, ∑ j, a i * a j * N i j = a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2)
        + ∑ j, (if i = j then 0 else a i * a j * ((u i b * ψ j b - ψ i b * u j b) / (χ i - χ j))) := by
      intro i
      conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add]
      congr 1
      · simp only [hN]
        rw [show (fun ξ => ψ i ξ * ψ i ξ) = fun ξ => ψ i ξ ^ 2 by funext ξ; ring]; ring
      · apply Finset.sum_congr rfl; intro j hj
        have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        rw [if_neg hij, hoff i j hij]
    simp_rw [hrow]
    rw [Finset.sum_add_distrib]
    congr 1
    -- the two halves of the Wronskian are equal by the swap `i ↔ j`
    have h1 : ∑ i, ∑ j, (if i = j then 0 else a i * a j * ((u i b * ψ j b - ψ i b * u j b) / (χ i - χ j)))
        = ∑ i, ∑ j, (if i = j then 0 else (a i * u i b) * (a j * ψ j b) / (χ i - χ j))
          + ∑ i, ∑ j, (if i = j then 0 else (a j * u j b) * (a i * ψ i b) / (χ j - χ i)) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
      split_ifs with h
      · simp
      · have hne : χ i - χ j ≠ 0 := by
          intro e; have := hgap i j h; rw [e, abs_zero] at this; linarith
        have hne' : χ j - χ i ≠ 0 := by intro e; apply hne; linarith
        field_simp; ring
    have h2 : ∑ i, ∑ j, (if i = j then 0 else (a j * u j b) * (a i * ψ i b) / (χ j - χ i))
        = ∑ i, ∑ j, (if i = j then 0 else (a i * u i b) * (a j * ψ j b) / (χ i - χ j)) := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]
    rw [h1, h2]; ring
  rw [hsq, hsplit]
  have hmv := Cvs.Upstream.HilbertInequalityUniformGap.hilbert_real_bilinear (freq := χ) hD hgap (fun i => a i * u i b)
    (fun j => a j * ψ j b) (Real.sqrt_pos.mpr (inv_pos.mpr hA))
  have hs2 : Real.sqrt A⁻¹ ^ 2 = A⁻¹ := Real.sq_sqrt (inv_pos.mpr hA).le
  rw [hs2] at hmv
  have e : ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - π / D * (A * ψ i b ^ 2 + u i b ^ 2 / A))
      = ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2)
        - 2 * (π / 2 * (A⁻¹ * ∑ r, (a r * u r b) ^ 2 + (∑ r, (a r * ψ r b) ^ 2) / A⁻¹) / D) := by
    have e2 : 2 * (π / 2 * (A⁻¹ * ∑ r, (a r * u r b) ^ 2 + (∑ r, (a r * ψ r b) ^ 2) / A⁻¹) / D)
        = ∑ r, a r ^ 2 * (π / D * (A * ψ r b ^ 2 + u r b ^ 2 / A)) := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      have e3 : ∀ x : ℝ, 2 * (π / 2 * x / D) = π / D * x := fun x => by ring
      rw [e3, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _; field_simp; ring
    rw [e2, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [e]
  have := neg_abs_le (∑ r, ∑ t, (if r = t then 0 else (a r * u r b) * (a t * ψ t b) / (χ r - χ t)))
  linarith

end Cvs.Prolate.Gram.RungGramFloorHilbert
