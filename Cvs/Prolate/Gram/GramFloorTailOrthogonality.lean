import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Gram floor from orthogonality at infinity and the tails beyond `b`

If the pairs satisfy `|∫₁ᵗ ψ_iψ_j| ≤ K_ij/t` for every `t ≥ b` and the tails `∫_b^t ψ_j² ≤ T_j`, then for every `t`
`∫₁ᵇ (Σ a_iψ_i)² = ∫₁ᵗ (Σ a_iψ_i)² − ∫_b^t (Σ a_iψ_i)² ≥ Σ a_i² ∫₁ᵇ ψ_i² − Σ_{i≠j}|a_ia_j|K_ij/t − (Σ a_i²) Σ_j T_j`,
and `t → ∞` leaves `∫₁ᵇ (Σ a_iψ_i)² ≥ Σ_i a_i² (∫₁ᵇ ψ_i² − Σ_j T_j)`: a Gram floor with no gap between the `χ_i`.
-/

namespace Cvs.Prolate.Gram.GramFloorTailOrthogonality

open Real Set Finset intervalIntegral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The square of a combination integrates to the double sum of the pair integrals. -/
theorem integral_sq_sum {lo hi : ℝ} (ψ : ι → ℝ → ℝ) (a : ι → ℝ)
    (hI : ∀ i j, IntervalIntegrable (fun ξ => ψ i ξ * ψ j ξ) MeasureTheory.volume lo hi) :
    ∫ ξ in lo..hi, (∑ i, a i * ψ i ξ) ^ 2 = ∑ i, ∑ j, a i * a j * ∫ ξ in lo..hi, ψ i ξ * ψ j ξ := by
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

/-- **The Gram floor from the tails**: with `|∫₁ᵗ ψ_iψ_j| ≤ K_ij/t` (`i ≠ j`) and `∫_b^t ψ_j² ≤ T_j` for every
`t ≥ b`, `Σ_i a_i² (∫₁ᵇ ψ_i² − Σ_j T_j) ≤ ∫₁ᵇ (Σ_i a_iψ_i)²`. -/
theorem gram_floor_tail {b : ℝ} (hb : 1 ≤ b) (ψ : ι → ℝ → ℝ) (a : ι → ℝ) (K : ι → ι → ℝ) (T : ι → ℝ)
    (hcont : ∀ i, ContinuousOn (ψ i) (Ici 1))
    (hcross : ∀ i j, i ≠ j → ∀ t, b ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (htail : ∀ j, ∀ t, b ≤ t → ∫ ξ in b..t, ψ j ξ ^ 2 ≤ T j) :
    ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - ∑ j, T j)
      ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  set S : ℝ := ∑ i, ∑ j, if i = j then 0 else |a i * a j| * K i j with hS
  set t : ℝ := max b (|S| / ε + 1) with ht
  have hbt : b ≤ t := le_max_left _ _
  have ht1 : 1 ≤ t := hb.trans hbt
  have ht0 : 0 < t := by linarith
  have hSt : S / t ≤ ε := by
    have h1 : |S| / ε + 1 ≤ t := le_max_right _ _
    have h2 : |S| ≤ ε * t := by
      have : |S| / ε ≤ t - 1 := by linarith
      rw [div_le_iff₀ hε] at this; nlinarith
    rw [div_le_iff₀ ht0]; linarith [le_abs_self S]
  -- continuity and integrability on `[1, t]` and `[b, t]`
  have hsub1 : Icc (1 : ℝ) t ⊆ Ici 1 := Icc_subset_Ici_self
  have hsubb : Icc b t ⊆ Ici 1 := Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hb)
  have hsub1b : Icc (1 : ℝ) b ⊆ Ici 1 := Icc_subset_Ici_self
  have hI : ∀ i j, IntervalIntegrable (fun ξ => ψ i ξ * ψ j ξ) MeasureTheory.volume 1 t := fun i j =>
    (((hcont i).mono hsub1).mul ((hcont j).mono hsub1)).intervalIntegrable_of_Icc ht1
  have hsqi : ∀ i, IntervalIntegrable (fun ξ => ψ i ξ ^ 2) MeasureTheory.volume 1 b := fun i =>
    (((hcont i).mono hsub1b).pow 2).intervalIntegrable_of_Icc hb
  have hsqi' : ∀ i, IntervalIntegrable (fun ξ => ψ i ξ ^ 2) MeasureTheory.volume b t := fun i =>
    (((hcont i).mono hsubb).pow 2).intervalIntegrable_of_Icc hbt
  have hcomb : ∀ s : Set ℝ, s ⊆ Ici 1 → ContinuousOn (fun ξ => (∑ i, a i * ψ i ξ) ^ 2) s := fun s hs =>
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hcont i).mono hs)).pow 2
  have hsq1 : IntervalIntegrable (fun ξ => (∑ i, a i * ψ i ξ) ^ 2) MeasureTheory.volume 1 b :=
    (hcomb _ hsub1b).intervalIntegrable_of_Icc hb
  have hsq2 : IntervalIntegrable (fun ξ => (∑ i, a i * ψ i ξ) ^ 2) MeasureTheory.volume b t :=
    (hcomb _ hsubb).intervalIntegrable_of_Icc hbt
  -- split at `b`
  have hsplit : ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2
      = (∫ ξ in (1 : ℝ)..t, (∑ i, a i * ψ i ξ) ^ 2) - ∫ ξ in b..t, (∑ i, a i * ψ i ξ) ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hsq1 hsq2]; ring
  -- the double sum on `[1, t]`
  have hexp := integral_sq_sum (lo := 1) (hi := t) ψ a hI
  have hrow : ∀ i, ∑ j, a i * a j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ
      = a i ^ 2 * (∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2)
        + ∑ j, (if i = j then 0 else a i * a j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ) := by
    intro i
    conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add]
    congr 1
    · rw [show (fun ξ => ψ i ξ * ψ i ξ) = fun ξ => ψ i ξ ^ 2 by funext ξ; ring]; ring
    · apply Finset.sum_congr rfl; intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj).symm]
  have h1 : ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2)
      ≤ ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2) := by
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hsqi i) (hsqi' i)]
    linarith [intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (f := fun ξ => ψ i ξ ^ 2) hbt
      (fun ξ _ => sq_nonneg (ψ i ξ))]
  have h2 : -(S / t) ≤ ∑ i, ∑ j, (if i = j then 0 else a i * a j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ) := by
    have e : S / t = ∑ i, ∑ j, (if i = j then 0 else |a i * a j| * K i j) / t := by
      rw [hS, Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_div]
    rw [e, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro j _
    split_ifs with hij
    · simp
    · have hK := hcross i j hij t hbt
      have hn := neg_abs_le (a i * a j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ)
      rw [abs_mul] at hn
      have h3 : |a i * a j| * |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ |a i * a j| * (K i j / t) :=
        mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      rw [mul_div_assoc]
      linarith
  have hmain : ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - S / t
      ≤ ∫ ξ in (1 : ℝ)..t, (∑ i, a i * ψ i ξ) ^ 2 := by
    rw [hexp]; simp_rw [hrow]; rw [Finset.sum_add_distrib]; linarith
  -- the tail beyond `b`
  have htail' : ∫ ξ in b..t, (∑ i, a i * ψ i ξ) ^ 2 ≤ (∑ i, a i ^ 2) * ∑ j, T j := by
    calc ∫ ξ in b..t, (∑ i, a i * ψ i ξ) ^ 2 ≤ ∫ ξ in b..t, (∑ i, a i ^ 2) * ∑ j, ψ j ξ ^ 2 := by
          apply intervalIntegral.integral_mono_on hbt hsq2
          · exact (continuousOn_const.mul (continuousOn_finsetSum _ fun j _ =>
              ((hcont j).mono hsubb).pow 2)).intervalIntegrable_of_Icc hbt
          · intro ξ _; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ i, a i ^ 2) * ∑ j, ∫ ξ in b..t, ψ j ξ ^ 2 := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
          intro j _; exact hsqi' j
      _ ≤ (∑ i, a i ^ 2) * ∑ j, T j := by
          apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
          exact Finset.sum_le_sum fun j _ => htail j t hbt
  have hdist : ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - ∑ j, T j)
      = ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - (∑ i, a i ^ 2) * ∑ j, T j := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hdist, hsplit]
  linarith

end Cvs.Prolate.Gram.GramFloorTailOrthogonality
