import Mathlib
import Cvs.Prolate.Gram.HalfBandLayerFloor
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (WF₂) from the twisted-pair floor of the cell Gram

The twist `d_j = √λ_j` on the layer `A = {j ≥ k}` lies in `[√½, 1]` (`λ_j ≥ λ_t ≥ ½`), and `C ≼ 1`, so Cvs.Upstream.TwistedPairLayerFloor turns a
floor `1 − ε` of `C + D′CD′` on `A` into `F_k ≥ ½ − ε/√2`.
`TwistFloor T₀ ε` asks for that floor at the first rung of `{T ≥ T₀}`; with `ε < √2(½ − μ*C₀∞/2)` it gives (WF′),
hence (WF₂).
-/

noncomputable section

open Real Filter Matrix Finset

namespace Cvs.Prolate.Gram.TwoCutFromTwistedPair
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam lamTop levT)

/-- `C ≼ 1`: `wᵀCw ≤ |w|²`. -/
theorem quad_cellGram_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (w : Fin x → ℝ) :
    w ⬝ᵥ (cellGram x *ᵥ w) ≤ w ⬝ᵥ w := by
  have h := (Cvs.Prolate.Gram.HalfBandLayerFloor.one_sub_cellGram_posSemidef hx).dotProduct_mulVec_nonneg w
  simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub] at h
  linarith

/-- The twist lies in `[√½, 1]`. -/
theorem sqrt_lam_mem {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : √(1 / 2) ≤ √(lam x j) ∧ √(lam x j) ≤ 1 := by
  have h2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx
  have hj : (j : ℕ) ≤ x - 1 := by omega
  have hlo : lamTop x ≤ lam x j := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_anti hx (by omega) hj
  exact ⟨Real.sqrt_le_sqrt ((Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx).trans hlo),
    Real.sqrt_le_one.mpr (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2)⟩

/-- `2√½ = √2`. -/
theorem two_mul_sqrt_half : 2 * √(1 / 2 : ℝ) = √2 := by
  rw [show (1 / 2 : ℝ) = 2 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

end Cvs.Prolate.Gram.TwoCutFromTwistedPair
