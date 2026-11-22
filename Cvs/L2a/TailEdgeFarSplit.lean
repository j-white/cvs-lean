import Mathlib
import Cvs.L2a.TailOfModes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge–far split of the tail and its pairing

The tail `F = Σ_m Φ(m·)` on `(1, b]` splits pointwise into the Poisson sums of the edge part (`mθ < k`) and the far
part (`mθ ≥ k`) of `Φ`, and their pairing `∫F_e F_f` is the sum over mode pairs `m < m′` of the window integrals of
`Φ(mθ)Φ(m′θ)` over `{k/m′ ≤ θ < k/m} ∩ (1, b]`, the pairs `m ≥ m′` contributing nothing: the correlation of Cvs.L2a.FarMassPlateau is
carried by the dilation windows alone.
-/

namespace Cvs.L2a.TailEdgeFarSplit

open Real Set MeasureTheory
open Cvs.L2a.TailOfModes

/-- The edge Poisson sum: the modes of `Φ` below `k`, on `(1, b]`. -/
noncomputable def edgeF (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  Set.indicator (Ioc 1 b) (fun θ => ∑ m ∈ Finset.Icc 1 M, Set.indicator {θ | θ < (k : ℝ) / m} (fun θ => Φ (m * θ)) θ) θ

/-- The far Poisson sum: the modes of `Φ` beyond `k`, on `(1, b]`. -/
noncomputable def farF (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  Set.indicator (Ioc 1 b) (fun θ => ∑ m ∈ Finset.Icc 1 M, Set.indicator {θ | (k : ℝ) / m ≤ θ} (fun θ => Φ (m * θ)) θ) θ

/-- **The split is pointwise**: `tailF = edgeF + farF`. -/
theorem tailF_eq_edge_add_far (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) (θ : ℝ) :
    tailF Φ M b θ = edgeF Φ M b k θ + farF Φ M b k θ := by
  unfold tailF edgeF farF
  by_cases hθ : θ ∈ Ioc 1 b
  · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : θ < (k : ℝ) / m
    · rw [Set.indicator_of_mem (show θ ∈ {θ | θ < (k : ℝ) / m} from h),
        Set.indicator_of_notMem (show θ ∉ {θ | (k : ℝ) / m ≤ θ} from not_le.mpr h), add_zero]
    · rw [Set.indicator_of_notMem (show θ ∉ {θ | θ < (k : ℝ) / m} from h),
        Set.indicator_of_mem (show θ ∈ {θ | (k : ℝ) / m ≤ θ} from not_lt.mp h), zero_add]
  · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, add_zero]

end Cvs.L2a.TailEdgeFarSplit
