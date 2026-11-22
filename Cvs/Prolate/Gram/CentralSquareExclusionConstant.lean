import Mathlib
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The central-square exclusion constant and its test-vector bound

`ε_cse(k) = 1 − λ_min S_k(N)` of the pair Gram `N = C + DCD` is the least `ε` with `CentralSquarePair x k ε`; it
lies in `[−1, 1)` and decreases as the layer `{j ≥ k}` shrinks. Every eigenvector `NΦ = νΦ` with layer weight `a`
gives `1 − ε_cse ≤ ν/a`, so a leakage rate beating the layer-weight rate at the cut makes `CentralSquareCut T₀ ε`
false for every `ε < 1`, and `CentralSquareCut` is monotone in the cut `T₀`.
-/

noncomputable section

open Real Filter Matrix Finset

namespace Cvs.Prolate.Gram.CentralSquareExclusionConstant
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (levT)
open Cvs.Upstream.PencilLayerBound (IsFloor layer layerFloor)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)

/-! ### The constant `ε_cse` -/

/-! ### The test-vector bound -/

/-! ### The positive control: an eigenvector whose leakage outruns its layer weight -/

/-- The hV threshold `√2(½ − μ*C₀∞(57/60)/2)` is below `1`. -/
theorem threshold_lt_one : √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2) < 1 := by
  have h1 := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos
  have h2 := Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf_pos (57 / 60)
  have hs : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have : 0 < muStar * C0inf (57 / 60) := mul_pos h1 h2
  nlinarith

/-! ### Monotonicity in the cut -/

end Cvs.Prolate.Gram.CentralSquareExclusionConstant

end
