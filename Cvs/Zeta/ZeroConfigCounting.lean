import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Cvs.Zeta.ZeroConfigDefs

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Cvs.Zeta.Base/Defs/Counting.lean — elementary counting facts for an abstract ZeroConfig.
[eq:trivialchain] at the abstract level; Statement.lean transfers it to ζ.
-/

open Set

noncomputable section

namespace Cvs.Zeta.Base.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂

lemma window_subset_carrier : Z.window T₁ T₂ ⊆ Z.carrier := inter_subset_left

/-- For s inside a window: #s ≤ Σ_{ρ∈s} m_ρ (since m_ρ ≥ 1). -/
lemma ncard_le_finsum_mult {s : Set ℂ} (hs : s ⊆ Z.window T₁ T₂) :
    s.ncard ≤ ∑ᶠ ρ ∈ s, Z.mult ρ := by
  have hfin : s.Finite := (Z.window_finite T₁ T₂).subset hs
  rw [Set.ncard_eq_toFinset_card s hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  exact Z.one_le_mult ρ (Z.window_subset_carrier T₁ T₂ (hs (hfin.mem_toFinset.mp hρ)))

/-- Monotonicity of Σ m_ρ over finite subsets of a window. -/
lemma finsum_mult_mono {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ Z.window T₁ T₂) :
    ∑ᶠ ρ ∈ s, Z.mult ρ ≤ ∑ᶠ ρ ∈ t, Z.mult ρ := by
  have htf : t.Finite := (Z.window_finite T₁ T₂).subset ht
  have hsf : s.Finite := htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf, finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst

lemma ncard_mono {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ Z.window T₁ T₂) : s.ncard ≤ t.ncard :=
  Set.ncard_le_ncard hst ((Z.window_finite T₁ T₂).subset ht)

/-- [eq:trivialchain] for an abstract zero configuration:
N₀ˢ ≤ N₀* ≤ N₀ ≤ N and N₀ˢ ≤ Nˢ ≤ N_d ≤ N. -/
theorem trivial_chain :
    Z.N0s T₁ T₂ ≤ Z.N0star T₁ T₂ ∧ Z.N0star T₁ T₂ ≤ Z.N0 T₁ T₂ ∧ Z.N0 T₁ T₂ ≤ Z.N T₁ T₂ ∧
    Z.N0s T₁ T₂ ≤ Z.Ns T₁ T₂ ∧ Z.Ns T₁ T₂ ≤ Z.Nd T₁ T₂ ∧ Z.Nd T₁ T₂ ≤ Z.N T₁ T₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Z.ncard_mono T₁ T₂ inter_subset_left inter_subset_left
  · exact Z.ncard_le_finsum_mult T₁ T₂ inter_subset_left
  · exact Z.finsum_mult_mono T₁ T₂ inter_subset_left subset_rfl
  · exact Z.ncard_mono T₁ T₂ (inter_subset_inter_left _ inter_subset_left) inter_subset_left
  · exact Z.ncard_mono T₁ T₂ inter_subset_left subset_rfl
  · exact Z.ncard_le_finsum_mult T₁ T₂ subset_rfl

end Cvs.Zeta.Base.ZeroConfig
