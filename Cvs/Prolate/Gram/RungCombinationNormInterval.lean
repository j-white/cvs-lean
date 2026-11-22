import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.Gram.GramFloorTailOrthogonality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The norm of a combination on any interval, from orthogonality at infinity

If the pairs satisfy `|∫₁ᵗ ψ_iψ_j| ≤ K_ij/t` for every large `t` and each rung has `∫₁ᵗ ψ_i² ≤ M_i`, then for every
`[lo, hi] ⊆ [1, ∞)` and every coefficient vector, `∫_{lo}^{hi} (Σ b_iψ_i)² ≤ Σ b_i² M_i`: the double sum on `[1, t]`
has diagonal at most `Σ b_i² M_i` and off-diagonal at most `S/t`, and `t → ∞`. No pointwise value of the combination
enters, so the bound carries no factor of the number of rungs.
-/

namespace Cvs.Prolate.Gram.RungCombinationNormInterval

open Real Set Finset intervalIntegral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The norm of a combination on `[lo, hi]`** is at most `Σ b_i² M_i`, `M_i` bounding the rung masses `∫₁ᵗ ψ_i²`,
when the pairs are `O(1/t)`-orthogonal. -/
theorem span_norm_le {lo hi : ℝ} (hlo : 1 ≤ lo) (hle : lo ≤ hi) (ψ : ι → ℝ → ℝ) (b : ι → ℝ) (K : ι → ι → ℝ)
    (Mm : ι → ℝ) (hcont : ∀ i, ContinuousOn (ψ i) (Ici 1))
    (hcross : ∀ i j, i ≠ j → ∀ t, hi ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, hi ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i) :
    ∫ ξ in lo..hi, (∑ i, b i * ψ i ξ) ^ 2 ≤ ∑ i, b i ^ 2 * Mm i := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  set S : ℝ := ∑ i, ∑ j, if i = j then 0 else |b i * b j| * K i j with hS
  set t : ℝ := max hi (|S| / ε + 1) with ht
  have hht : hi ≤ t := le_max_left _ _
  have ht1 : 1 ≤ t := (hlo.trans hle).trans hht
  have ht0 : 0 < t := by linarith
  have hSt : S / t ≤ ε := by
    have h1 : |S| / ε + 1 ≤ t := le_max_right _ _
    have h2 : |S| ≤ ε * t := by
      have : |S| / ε ≤ t - 1 := by linarith
      rw [div_le_iff₀ hε] at this; nlinarith
    rw [div_le_iff₀ ht0]; linarith [le_abs_self S]
  have hsub1 : Icc (1 : ℝ) t ⊆ Ici 1 := Icc_subset_Ici_self
  have hI : ∀ i j, IntervalIntegrable (fun ξ => ψ i ξ * ψ j ξ) MeasureTheory.volume 1 t := fun i j =>
    (((hcont i).mono hsub1).mul ((hcont j).mono hsub1)).intervalIntegrable_of_Icc ht1
  have hcomb : ContinuousOn (fun ξ => (∑ i, b i * ψ i ξ) ^ 2) (Icc 1 t) :=
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hcont i).mono hsub1)).pow 2
  -- `∫_{lo}^{hi} ≤ ∫₁ᵗ` for the nonnegative integrand
  have hmono : ∫ ξ in lo..hi, (∑ i, b i * ψ i ξ) ^ 2 ≤ ∫ ξ in (1 : ℝ)..t, (∑ i, b i * ψ i ξ) ^ 2 := by
    have hI1 : IntervalIntegrable (fun ξ => (∑ i, b i * ψ i ξ) ^ 2) MeasureTheory.volume 1 t :=
      hcomb.intervalIntegrable_of_Icc ht1
    have sub : ∀ a' b', 1 ≤ a' → b' ≤ t → a' ≤ b' →
        IntervalIntegrable (fun ξ => (∑ i, b i * ψ i ξ) ^ 2) MeasureTheory.volume a' b' :=
      fun a' b' ha hb hab => hI1.mono_set (by rw [uIcc_of_le hab, uIcc_of_le ht1]; exact Icc_subset_Icc ha hb)
    have e1 : ∫ ξ in (1 : ℝ)..t, (∑ i, b i * ψ i ξ) ^ 2
        = (∫ ξ in (1 : ℝ)..lo, (∑ i, b i * ψ i ξ) ^ 2) + (∫ ξ in lo..hi, (∑ i, b i * ψ i ξ) ^ 2)
          + ∫ ξ in hi..t, (∑ i, b i * ψ i ξ) ^ 2 := by
      rw [integral_add_adjacent_intervals (sub 1 lo le_rfl (hle.trans hht) hlo) (sub lo hi hlo hht hle),
        integral_add_adjacent_intervals (sub 1 hi le_rfl hht (hlo.trans hle)) (sub hi t (hlo.trans hle) le_rfl hht)]
    have h1 : 0 ≤ ∫ ξ in (1 : ℝ)..lo, (∑ i, b i * ψ i ξ) ^ 2 := integral_nonneg hlo fun ξ _ => sq_nonneg _
    have h2 : 0 ≤ ∫ ξ in hi..t, (∑ i, b i * ψ i ξ) ^ 2 := integral_nonneg hht fun ξ _ => sq_nonneg _
    linarith
  -- the double sum on `[1, t]`
  have hexp := Cvs.Prolate.Gram.GramFloorTailOrthogonality.integral_sq_sum (lo := 1) (hi := t) ψ b hI
  have hrow : ∀ i, ∑ j, b i * b j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ
      = b i ^ 2 * (∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2)
        + ∑ j, (if i = j then 0 else b i * b j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ) := by
    intro i
    conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add]
    congr 1
    · rw [show (fun ξ => ψ i ξ * ψ i ξ) = fun ξ => ψ i ξ ^ 2 by funext ξ; ring]; ring
    · apply Finset.sum_congr rfl; intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj).symm]
  have h1 : ∑ i, b i ^ 2 * (∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2) ≤ ∑ i, b i ^ 2 * Mm i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmass i t hht) (sq_nonneg _)
  have h2 : ∑ i, ∑ j, (if i = j then 0 else b i * b j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ) ≤ S / t := by
    have e : S / t = ∑ i, ∑ j, (if i = j then 0 else |b i * b j| * K i j) / t := by
      rw [hS, Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_div]
    rw [e]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    split_ifs with hij
    · simp
    · have hK := hcross i j hij t hht
      have hn := le_abs_self (b i * b j * ∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ)
      rw [abs_mul] at hn
      have h3 : |b i * b j| * |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ |b i * b j| * (K i j / t) :=
        mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      rw [mul_div_assoc]
      linarith
  have hmain : ∫ ξ in (1 : ℝ)..t, (∑ i, b i * ψ i ξ) ^ 2 ≤ ∑ i, b i ^ 2 * Mm i + S / t := by
    rw [hexp]; simp_rw [hrow]; rw [Finset.sum_add_distrib]; linarith
  linarith

end Cvs.Prolate.Gram.RungCombinationNormInterval
