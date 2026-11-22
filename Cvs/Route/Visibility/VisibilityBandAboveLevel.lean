import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.BandFloorFromResolvent
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.InverseCellGramResolvent
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.TunnellingFloorSumAbove
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.CentralTraceHighpass
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.HighpassExtensionRung
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.VisibilityHardyModule
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV from the band central resolvent, highpass extensions or Hardy energies above some level `τ < 1`

`BandFloorFromResolvent`'s and an earlier result's reductions restricted to the rungs with `T_j > τ`; any statement on `T_j > ¾ + c^{−1/2}`
implies the one above every `τ ∈ (¾, 1)`, so the layer `¾ < T_j ≤ ¾ + c^{−1/2}` drops out of hV.
-/

noncomputable section

open Real Filter

namespace Cvs.Route.Visibility.VisibilityBandAboveLevel
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.Gram.CentralResolventTrace (selB)

/-- **The band resolvent bound above `τ`**: `B_jj ≤ x^ε` on the rungs with `T_j > τ`, for every `ε > 0`. -/
def BandResolventAbove (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, τ < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    selB x (finOfSF j) ≤ (x : ℝ) ^ ε

/-- **The band highpass extensions above `τ`**: on the rungs with `T_j > τ`, `h_{4j}|_I` has a highpass extension
`v` with `∫v² ≤ x^ε`, for every `ε > 0`. -/
def BandHighpassAbove (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, τ < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ∃ v : ℝ → ℝ, Cvs.Prolate.Hardy.HighpassExtensionRung.IsHighpassExt (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) v ∧ ∫ t, v t ^ 2 ≤ (x : ℝ) ^ ε

/-- **The band Hardy energies above `τ`**: `‖J_c(Qh_{4j})‖² ≤ x^ε` on the rungs with `T_j > τ`, for every `ε > 0`. -/
def BandHardyAbove (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, τ < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ‖Cvs.Prolate.Hardy.HardyExtensionOperator.hardyJ (2 * π * x) (Cvs.Prolate.Hardy.CentralRungExpansion.qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk (2 * π * x) (2 * (j : ℕ))))‖ ^ 2 ≤ (x : ℝ) ^ ε

/-- **The main-band highpass extensions**: the highpass extensions of `BandHighpassAbove` on the rungs with
`T_j > ¾ + c^{−1/2}`, `c = 2πx`. -/
def BandHighpassMain : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 + (2 * π * x) ^ (-(1 / 2) : ℝ) < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ∃ v : ℝ → ℝ, Cvs.Prolate.Hardy.HighpassExtensionRung.IsHighpassExt (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) v ∧ ∫ t, v t ^ 2 ≤ (x : ℝ) ^ ε

/-- **The main-band Hardy energies**: `‖J_c(Qh_{4j})‖² ≤ x^ε` on the rungs with `T_j > ¾ + c^{−1/2}`. -/
def BandHardyMain : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 + (2 * π * x) ^ (-(1 / 2) : ℝ) < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ‖Cvs.Prolate.Hardy.HardyExtensionOperator.hardyJ (2 * π * x) (Cvs.Prolate.Hardy.CentralRungExpansion.qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk (2 * π * x) (2 * (j : ℕ))))‖ ^ 2 ≤ (x : ℝ) ^ ε

/-- **The band floor above `τ` from the band resolvent bound above `τ`.** -/
theorem bandFloorAbove_of_bandResolventAbove {τ : ℝ} (hR : BandResolventAbove τ) : Cvs.Prolate.Gram.TunnellingFloorSumAbove.BandFloorAbove τ := by
  intro ε hε
  set K : ℝ := 2 / (1 - muStar * (9 / 50))
  have hm := Cvs.Prolate.Gram.InverseCellGramResolvent.muStar_mul_lt_one
  have hK : 0 ≤ K := div_nonneg (by norm_num) (by linarith)
  filter_upwards [hR (ε / 2) (by linarith), Cvs.Prolate.Gram.InverseCellGramResolvent.eventually_cellGram_inv_le,
    Cvs.Prolate.Gram.BandFloorFromResolvent.eventually_add_mul_rpow_le hε hK, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hB hC hpow hx j hj
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hinv : (cellGram x)⁻¹ (finOfSF j) (finOfSF j) ≤ (x : ℝ) ^ ε := by
    have h1 := hC (finOfSF j)
    have h2 : 1 + 2 * selB x (finOfSF j) / (1 - muStar * (9 / 50)) = 1 + K * selB x (finOfSF j) := by
      simp only [K]; ring
    have h3 := mul_le_mul_of_nonneg_left (hB j hj) hK
    linarith
  have hpos : 0 < (cellGram x)⁻¹ (finOfSF j) (finOfSF j) := by
    have h := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx) (finOfSF j)
    unfold Cvs.Upstream.CellFloorSandwichPosDef.sigmaP at h
    exact inv_pos.mp h
  rw [rpow_neg hx0.le]
  unfold Cvs.Upstream.CellFloorSandwichPosDef.sigmaP
  exact inv_anti₀ hpos hinv

/-- **The band resolvent bound above `τ` from band highpass extensions above `τ`** (Cvs.Prolate.Hardy.CentralTraceHighpass: `B_jj ≤ 2∫v²`). -/
theorem bandResolventAbove_of_bandHighpassAbove {τ : ℝ} (hH : BandHighpassAbove τ) : BandResolventAbove τ := by
  intro ε hε
  filter_upwards [hH (ε / 2) (by linarith), Cvs.Prolate.Gram.BandFloorFromResolvent.eventually_add_mul_rpow_le hε (by norm_num : (0 : ℝ) ≤ 2),
    eventually_ge_atTop 1] with x hv hpow hx1 j hj
  obtain ⟨v, hv, hE⟩ := hv j hj
  have hx : (0 : ℝ) < 2 * π * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    positivity
  have h := Cvs.Prolate.Hardy.CentralTraceHighpass.resQuad_le hx hv
  have : selB x (finOfSF j) = Cvs.Prolate.Gram.CentralResolventTrace.resQuad (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) := rfl
  rw [this]
  linarith

/-- **Band highpass extensions above `τ` from the band Hardy energies above `τ`**: `v = J_c(Qh_{4j})`. -/
theorem bandHighpassAbove_of_bandHardyAbove {τ : ℝ} (hH : BandHardyAbove τ) : BandHighpassAbove τ := by
  intro ε hε
  filter_upwards [hH ε hε, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hx hsc j hj
  have hc : 0 < 2 * π * x := by linarith
  have hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hsc (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j)
  refine ⟨_, Cvs.Prolate.Hardy.TraceLimitHighpassOperator.isHighpassExt_rung (Cvs.Route.Visibility.VisibilityHardyModule.hardyJ_highpassOp hc) hk, ?_⟩
  rw [Cvs.Prolate.Hardy.TraceLimitHighpassOperator.integral_sq_eq_norm_sq]
  exact hx j hj

/-- `c^{−1/2} < τ − ¾` eventually at `c = 2πx`, for `τ > ¾`. -/
theorem eventually_layer_lt {τ : ℝ} (hτ : 3 / 4 < τ) :
    ∀ᶠ x : ℕ in atTop, 3 / 4 + (2 * π * x) ^ (-(1 / 2) : ℝ) < τ := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π))
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < τ - 3 / 4 by linarith))] with x hx
  simp only [Function.comp] at hx
  linarith

/-- **Main-band Hardy energies give the Hardy energies above every `τ > ¾`.** -/
theorem bandHardyAbove_of_main (h : BandHardyMain) {τ : ℝ} (hτ : 3 / 4 < τ) : BandHardyAbove τ :=
  fun ε hε => by
    filter_upwards [h ε hε, eventually_layer_lt hτ] with x hx hl j hj
    exact hx j (hl.trans hj)

end Cvs.Route.Visibility.VisibilityBandAboveLevel

end
