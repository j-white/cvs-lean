import Mathlib
import Cvs.Prolate.Gram.BulkFloorFromFullTwist
import Cvs.Prolate.Gram.FullTwistOuterCell
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TwoCutFromBulkFloor
import Cvs.Prolate.Gram.TwoCutLayerBound
import Cvs.Route.Visibility.AliasRemainderCentreBound
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV after wave 14

(WF′) from the full-twist floor of Cvs.Prolate.Gram.BulkFloorFromFullTwist below the threshold `√2(½ − μ*C₀∞/2)`, so (WF₂) needs no plunge floor;
the deep cell floor from `EndpointAmplitudeFloor`'s discrete potential; the window input from an earlier result's circle and edge laws.
-/

noncomputable section
open Real Filter
open Cvs.ZeroCounting
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.VisibilityFullTwistPotential
open Cvs.ZeroCounting

/-- (WF′) from a bulk floor strictly above `μ*C₀∞/2`. -/
theorem wfprime_of_bulkFloor {Wt T₀ φ : ℝ} (hφ : muStar * C0inf Wt / 2 < φ) (h : Cvs.Prolate.Gram.TwoCutFromBulkFloor.BulkFloor T₀ φ) :
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.WFprime Wt T₀ :=
  ⟨φ - muStar * C0inf Wt / 2, sub_pos.2 hφ, by
    filter_upwards [h] with x ⟨k₀, h1, h2, h3⟩
    exact ⟨k₀, h1, h2, by linarith⟩⟩

/-- (WF′) from the full-twist floor with `0 ≤ ε + ρ < √2(½ − μ*C₀∞/2)`. -/
theorem wfprime_of_fullTwistFloor {Wt T₀ ε ρ : ℝ} (hερ : 0 ≤ ε + ρ)
    (hlt : ε + ρ < √2 * (1 / 2 - muStar * C0inf Wt / 2)) (h : Cvs.Prolate.Gram.BulkFloorFromFullTwist.FullTwistFloor T₀ ε ρ) :
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.WFprime Wt T₀ := by
  refine wfprime_of_bulkFloor ?_ (Cvs.Prolate.Gram.BulkFloorFromFullTwist.bulkFloor_of_fullTwistFloor hερ h)
  have hs : 0 < √(2 : ℝ) := by positivity
  have : (ε + ρ) / √2 < 1 / 2 - muStar * C0inf Wt / 2 := by
    rw [div_lt_iff₀ hs]; linarith
  linarith

/-- The full-twist threshold at `W̃ = 57/60` exceeds `1/50`. -/
theorem twistThreshold_57_60_gt : 1 / 50 < √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2) := by
  have hth := (Cvs.Route.Visibility.AliasRemainderCentreBound.threshold_57_60_mem).2
  have hs : (1414 / 1000 : ℝ) < √2 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  nlinarith

/-- (WF₂) from central-square exclusion with `0 ≤ ε + ρ < √2(½ − μ*C₀∞/2)`. -/
theorem wfTwo_of_centralSquare {Wt T₀ ε ρ : ℝ} (hερ : 0 ≤ ε + ρ)
    (hlt : ε + ρ < √2 * (1 / 2 - muStar * C0inf Wt / 2)) (h : Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquareFloor T₀ ε ρ) :
    Cvs.Prolate.Gram.TwoCutLayerBound.WFtwo Wt T₀ :=
  Cvs.Prolate.Gram.TwoCutLayerBound.wfTwo_of_wfprime (wfprime_of_fullTwistFloor hερ hlt ((Cvs.Prolate.Gram.FullTwistOuterCell.centralSquareFloor_iff T₀ ε ρ).1 h))

end Cvs.Route.Visibility.VisibilityFullTwistPotential

end
