import Mathlib
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CellGramTraceComparison
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.EvenProlateParsevalSplit
import Cvs.Prolate.Gram.FiniteFourierSplitCells
import Cvs.Prolate.Gram.InnerResolventObjective
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.RungFixedFourierTransfer
import Cvs.Prolate.Gram.TraceComparisonHolds
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Route.Visibility.CEBoundFromTrace
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.ScalarTraceBudget
import Cvs.Route.Visibility.VisibilityHardyModule
import Cvs.Upstream.ContractionInverseDiagonal

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Each diagonal entry of the inverse prolate cell Gram is bounded by its central resolvent entry

At `c = 2πx`, when `T_c` is well posed with `μ*T_c < 1`, `(C⁻¹)_jj ≤ 1 + 2B_jj/(1 − μ*T_c)` for every rung, where
`B_jj = ⟨Qh_{4j}, (I − A)⁻¹Qh_{4j}⟩`; with the trace limit `T_c ≤ 9/50` this holds eventually at `T_c = 9/50`.
-/

noncomputable section

open Real Filter

namespace Cvs.Prolate.Gram.InverseCellGramResolvent
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2 rungE innerProj)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam cellGram)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar)
open Cvs.Prolate.Gram.CentralResolventTrace (Tc WellPosed gpoly selB)
open Cvs.Prolate.Gram.CellGramTraceComparison (prolE IsInnerSol selIdx prolE_selIdx)

/-- **The per-rung transfer on the prolate cell Gram**: if `T_c` is well posed and `μ*T_c < 1`, then
`(C⁻¹)_jj ≤ 1 + 2B_jj/(1 − μ*T_c)`. -/
theorem cellGram_inv_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (hW : WellPosed (2 * π * x)) (hT : muStar * Tc x < 1)
    (j : Fin x) : (cellGram x)⁻¹ j j ≤ 1 + 2 * selB x j / (1 - muStar * Tc x) := by
  have hc : 0 < 2 * π * x := by linarith
  choose t ht using fun k : LevelIdx (2 * π * x) => Cvs.Prolate.Gram.EvenProlateParsevalSplit.exists_innerSol hc (prolE k)
  obtain ⟨hs, hle⟩ := Cvs.Prolate.Gram.TraceComparisonHolds.hasSum_le_Tc hx hW ht
  set T := ∑' k, Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm (2 * π * x) t k
  have hsel : ∀ j, IsInnerSol (2 * π * x) (rungE hx j) (t (selIdx hx j)) := fun j => by
    rw [← prolE_selIdx]; exact ht _
  set Bb : Fin x → ℝ := fun b => inner ℝ (t (selIdx hx b)) (innerProj (rungE hx b))
  have hB0 : ∀ b, 0 ≤ Bb b := fun b => Cvs.Prolate.Gram.CellGramTraceComparison.inner_innerSol_nonneg hc (hsel b)
  have hTs : ∑ b : Fin x, gpoly √(lam x b) * Bb b ≤ T := by
    have h := sum_le_hasSum (Finset.univ.map ⟨selIdx hx, Cvs.Prolate.Gram.CellGramTraceComparison.selIdx_injective hx⟩)
      (fun k _ => Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm_nonneg hc ht k) hs.hasSum
    rw [Finset.sum_map] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun b _ => ?_) h
    simp only [Function.Embedding.coeFn_mk, Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm, prolE_selIdx, Bb]
    rw [show Cvs.Prolate.Gram.CentralResolventTrace.sigma (2 * π * x) (selIdx hx b) = √(lam x b) from Cvs.Prolate.Gram.CentralResolventTrace.sigma_two_mul hx b]
  have hμ := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos
  have hq : ∑ b : Fin x, (1 - √(lam x b)) * Bb b ≤ muStar * Tc x := by
    calc ∑ b : Fin x, (1 - √(lam x b)) * Bb b ≤ ∑ b : Fin x, muStar * (gpoly √(lam x b) * Bb b) :=
          Finset.sum_le_sum fun b _ => by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (Cvs.Prolate.Gram.CentralResolventTrace.delta_le_muStar_mul hx b) (hB0 b)
      _ = muStar * ∑ b : Fin x, gpoly √(lam x b) * Bb b := by rw [Finset.mul_sum]
      _ ≤ muStar * Tc x := mul_le_mul_of_nonneg_left (hTs.trans hle) hμ.le
  have hq1 : ∑ b : Fin x, (1 - √(lam x b)) * Bb b < 1 := lt_of_le_of_lt hq hT
  have hCpos : (Matrix.gram ℝ fun b => rungE hx b - innerProj (rungE hx b)).PosDef := by
    rw [Cvs.Prolate.Gram.WindowFloorTransferSolutions.gram_cellPart]; exact Cvs.Prolate.Gram.RungCellGramDisplacement.rungCellGram_posDef hx
  have hmain := Cvs.Upstream.ContractionInverseDiagonal.inv_diag_le Cvs.Prolate.Gram.WindowFloorTransferSolutions.isSymmProj_innerProj (Cvs.Prolate.Gram.FiniteFourierSplitCells.fourierE2_symm _)
    (Cvs.Prolate.Gram.FiniteFourierSplitCells.norm_fourierE2_le hc) (Cvs.Prolate.Gram.RungFixedFourierTransfer.fourierFixed_symm hx) (Cvs.Prolate.Gram.RungFixedFourierTransfer.fourierFixed_norm_le hx)
    (Cvs.Prolate.Gram.WindowFloorTransferSolutions.inner_rungE hx) (Cvs.Prolate.Gram.CellGramTraceComparison.fourierE2_rungE hx) (Cvs.Prolate.Gram.CellGramTraceComparison.fourierFixed_eq hx) (fun b => (hsel b).1)
    (fun b => (hsel b).2) hCpos (fun b => Real.sqrt_le_one.mpr (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx b.2)) hq1 j
  rw [← Cvs.Prolate.Gram.CellGramTraceComparison.cellGram_eq_gram hx] at hmain
  have hBj : Bb j ≤ selB x j := by
    have h := Cvs.Prolate.Gram.InnerResolventObjective.inner_le_resQuad (selIdx hx j) (ht (selIdx hx j)) (hW.1 _ (selIdx hx j).2)
    rw [prolE_selIdx] at h
    exact h
  have hden : 0 < 1 - muStar * Tc x := by linarith
  have hden' : 1 - muStar * Tc x ≤ 1 - ∑ b : Fin x, (1 - √(lam x b)) * Bb b := by linarith
  have hsel0 : 0 ≤ selB x j := (hB0 j).trans hBj
  refine hmain.trans ?_
  have : 2 * Bb j / (1 - ∑ b : Fin x, (1 - √(lam x b)) * Bb b) ≤ 2 * selB x j / (1 - muStar * Tc x) :=
    div_le_div₀ (by linarith) (by linarith) hden hden'
  linarith

/-- `μ* · 9/50 < 1`. -/
theorem muStar_mul_lt_one : muStar * (9 / 50) < 1 := by
  have := Cvs.Route.Visibility.ScalarTraceBudget.muStar_le_seven_tenths
  nlinarith [Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos]

/-- **Eventually** every rung has `(C⁻¹)_jj ≤ 1 + 2B_jj/(1 − 9μ*/50)`, from the trace limit `T_c ≤ 9/50`. -/
theorem eventually_cellGram_inv_le :
    ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, (cellGram x)⁻¹ j j ≤ 1 + 2 * selB x j / (1 - muStar * (9 / 50)) := by
  have hTL : Cvs.Route.Visibility.CEBoundFromTrace.TraceLimit := Cvs.Prolate.Hardy.TraceLimitHighpassOperator.traceLimit Cvs.Route.Visibility.VisibilityHardyModule.highpassColumnLimsup_three_fifths
  filter_upwards [hTL, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hWT hx j
  obtain ⟨hW, hT⟩ := hWT
  have hμ := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos
  have hm := muStar_mul_lt_one
  have hT' : muStar * Tc x ≤ muStar * (9 / 50) := mul_le_mul_of_nonneg_left hT hμ.le
  have hsel0 : 0 ≤ selB x j := Cvs.Prolate.Gram.CentralResolventTrace.resQuad_nonneg (hW.1 _ (Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j))
  refine (cellGram_inv_le hx hW (lt_of_le_of_lt hT' hm) j).trans ?_
  have : 2 * selB x j / (1 - muStar * Tc x) ≤ 2 * selB x j / (1 - muStar * (9 / 50)) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  linarith

end Cvs.Prolate.Gram.InverseCellGramResolvent

end
