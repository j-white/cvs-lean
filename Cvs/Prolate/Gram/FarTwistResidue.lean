import Mathlib
import Cvs.Prolate.Gram.BulkFloorFromFullTwist
import Cvs.Prolate.Gram.FullTwistOuterCell
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far-twist residue from the far out-of-band weights

For `0 ≤ λ ≤ 1`, `(1 − √λ)² ≤ 1 − λ`. So a bound `ρ` on `Σ_{j<k} (1 − λ_j)v_j²`, the out-of-band weights of the far
rungs, at the vectors whose image vanishes below `k`, bounds the far-twist residue, and with the central-square
exclusion gives the bulk floor `2/5`.
-/

noncomputable section

open Real Filter Matrix Finset

namespace Cvs.Prolate.Gram.FarTwistResidue
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam levT)

/-- `(1 − √l)² ≤ 1 − l` for `0 ≤ l ≤ 1`. -/
theorem one_sub_sqrt_sq_le {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) : (1 - √l) ^ 2 ≤ 1 - l := by
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg l
  have hs1 : √l ≤ 1 := Real.sqrt_le_one.2 h1
  nlinarith

/-- The far out-of-band residue `ρ` below `k`: every `v` whose image `Cv` vanishes below `k` has
`Σ_{j<k} (1 − λ_j) v_j² ≤ ρ Σ_{j ≥ k} v_j²`. -/
def FarBandRes (x : ℕ) (k : Fin x) (ρ : ℝ) : Prop :=
  ∀ v : Fin x → ℝ, (∀ j, ¬ k ≤ j → (cellGram x *ᵥ v) j = 0) →
    ∑ j ∈ univ.filter (fun j => ¬ k ≤ j), (1 - lam x j) * v j ^ 2 ≤ ρ * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2

/-- **The far-twist residue from the out-of-band residue**. -/
theorem farTwistRes_of_farBandRes {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : Fin x} {ρ : ℝ} (h : FarBandRes x k ρ) :
    Cvs.Prolate.Gram.BulkFloorFromFullTwist.FarTwistRes x k ρ := fun v hv => by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (h v hv)
  exact mul_le_mul_of_nonneg_right
    (one_sub_sqrt_sq_le (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_nonneg x j) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2)) (sq_nonneg _)

/-- **Central-square exclusion with the out-of-band residue at the cut `T₀`**. -/
def CentralSquareBandFloor (T₀ ε ρ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧
    Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquarePair x k₀ ε ∧ FarBandRes x k₀ ρ

end Cvs.Prolate.Gram.FarTwistResidue
