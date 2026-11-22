import Mathlib
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TwoCutFromBulkFloor
import Cvs.Prolate.Gram.TwoCutFromTwistedPair
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.FullTwistLayerFloor
import Cvs.Upstream.PencilLayerBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bulk floor from the full-twist floor of the cell Gram

The full twist `d_j = √λ_j` of the cell Gram lies in `[√½, 1]` on every rung, and `C ≼ 1`, so Cvs.Upstream.FullTwistLayerFloor turns a floor
`1 − ε` of `C + DCD` on the layer `A = {j ≥ k}`, together with a bound `ρ` on the far twist `Σ_{j<k}(1 − √λ_j)²v_j²`
at the vectors whose image vanishes off `A`, into `F_k ≥ ½ − (ε + ρ)/√2`. At the first rung of `{T ≥ T₀}` this is
the bulk floor `Cvs.Prolate.Gram.TwoCutFromBulkFloor.BulkFloor T₀ (½ − (ε + ρ)/√2)`, and `ε + ρ ≤ √2/10` gives the bulk floor `2/5`.
-/

noncomputable section

open Real Filter Matrix Finset

namespace Cvs.Prolate.Gram.BulkFloorFromFullTwist
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam levT)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (floorC)

/-- The full twist `Dv` of the cell Gram: `v_j ↦ √λ_j v_j` on every rung. -/
def cellTwistAll (x : ℕ) (v : Fin x → ℝ) : Fin x → ℝ := Cvs.Upstream.FullTwistLayerFloor.twistAll (fun j => √(lam x j)) v

/-- The full-twist floor `1 − ε` of the cell Gram on the layer `{j ≥ k}`. -/
def FullTwistPair (x : ℕ) (k : Fin x) (ε : ℝ) : Prop :=
  ∀ v : Fin x → ℝ, (1 - ε) * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2
    ≤ v ⬝ᵥ (cellGram x *ᵥ v) + cellTwistAll x v ⬝ᵥ (cellGram x *ᵥ cellTwistAll x v)

/-- The far-twist residue `ρ` below `k`: every `v` whose image `Cv` vanishes below `k` has
`Σ_{j<k} (1 − √λ_j)² v_j² ≤ ρ Σ_{j ≥ k} v_j²`. -/
def FarTwistRes (x : ℕ) (k : Fin x) (ρ : ℝ) : Prop :=
  ∀ v : Fin x → ℝ, (∀ j, ¬ k ≤ j → (cellGram x *ᵥ v) j = 0) →
    ∑ j ∈ univ.filter (fun j => ¬ k ≤ j), (1 - √(lam x j)) ^ 2 * v j ^ 2 ≤ ρ * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2

/-- **The full-twist floor at the cut `T₀`**: eventually the first rung `k₀` of `{T ≥ T₀}` exists, the cell Gram has
the full-twist floor `1 − ε` on its layer, and the far-twist residue below it is at most `ρ`. -/
def FullTwistFloor (T₀ ε ρ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧
    FullTwistPair x k₀ ε ∧ FarTwistRes x k₀ ρ

/-- **The full-twist floor bound**: the full-twist floor `1 − ε` and the far-twist residue `ρ` on `{j ≥ k}`, with
`0 ≤ ε + ρ`, give `F_k ≥ ½ − (ε + ρ)/√2`. -/
theorem half_sub_le_floorC_full {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : Fin x} {ε ρ : ℝ} (hερ : 0 ≤ ε + ρ)
    (hN : FullTwistPair x k ε) (hρ : FarTwistRes x k ρ) : 1 / 2 - (ε + ρ) / √2 ≤ floorC x k := by
  rw [Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC_eq hx, ← Cvs.Prolate.Gram.TwoCutFromTwistedPair.two_mul_sqrt_half]
  exact Cvs.Upstream.FullTwistLayerFloor.half_sub_le_layerFloor_full (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx) (Cvs.Prolate.Gram.TwoCutFromTwistedPair.quad_cellGram_le hx)
    (by positivity) (fun j _ => Cvs.Prolate.Gram.TwoCutFromTwistedPair.sqrt_lam_mem hx j) hερ hρ hN

/-- **The bulk floor from the full-twist floor**: `0 ≤ ε + ρ` and `FullTwistFloor T₀ ε ρ` give
`BulkFloor T₀ (½ − (ε + ρ)/√2)`. -/
theorem bulkFloor_of_fullTwistFloor {T₀ ε ρ : ℝ} (hερ : 0 ≤ ε + ρ) (h : FullTwistFloor T₀ ε ρ) :
    Cvs.Prolate.Gram.TwoCutFromBulkFloor.BulkFloor T₀ (1 / 2 - (ε + ρ) / √2) := by
  filter_upwards [h, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x ⟨k₀, h1, h2, hN, hρ⟩ hx
  exact ⟨k₀, h1, h2, half_sub_le_floorC_full hx hερ hN hρ⟩

end Cvs.Prolate.Gram.BulkFloorFromFullTwist
