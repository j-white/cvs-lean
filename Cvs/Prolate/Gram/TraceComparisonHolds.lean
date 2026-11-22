import Mathlib
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CellGramTraceComparison
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.EvenProlateParsevalSplit
import Cvs.Prolate.Gram.InnerResolventObjective
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Route.Visibility.CEBoundFromTrace
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.InverseExcessPencilTop

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trace comparison (B) holds

At `c = 2πx` the inner solutions `t_k` exist and `⟨t_k, Qh_{2k}⟩ ≤ ⟨Qh_{2k}, (I − A)⁻¹Qh_{2k}⟩` when `T_c` is well
posed, so the eigenbasis trace is at most `T_c`; the finite transfer bound gives `R ≤ 2a_tT_c/(1 − μ*T_c)` when
`μ*T_c < 1`, which is `ExcessComparison` and `TraceComparison`.
-/

noncomputable section

open Real Filter

namespace Cvs.Prolate.Gram.TraceComparisonHolds
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar)
open Cvs.Prolate.Gram.CentralResolventTrace (Tc WellPosed aTop)
open Cvs.Prolate.Gram.CellGramTraceComparison (prolE IsInnerSol)

/-- The eigenbasis trace is at most `T_c`: for inner solutions `t_k` and a well-posed `T_c`, the series
`Σ_k g(σ_k)⟨t_k, Qh_{2k}⟩` is summable with sum at most `T_c`. -/
theorem hasSum_le_Tc {x : ℕ} (hx : 80 ≤ 2 * π * x) (hW : WellPosed (2 * π * x)) {t : LevelIdx (2 * π * x) → E2}
    (ht : ∀ k, IsInnerSol (2 * π * x) (prolE k) (t k)) :
    Summable (Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm (2 * π * x) t) ∧ ∑' k, Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm (2 * π * x) t k ≤ Tc x := by
  have hc : 0 < 2 * π * x := by linarith
  set θ := Cvs.Prolate.Gram.CentralResolventTrace.traceTerm (2 * π * x)
  have hle : ∀ k : LevelIdx (2 * π * x), Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm (2 * π * x) t k ≤ θ k := by
    intro k
    simp only [θ, Cvs.Prolate.Gram.CentralResolventTrace.traceTerm, ite_eq_left k.2, Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm]
    exact mul_le_mul_of_nonneg_left (Cvs.Prolate.Gram.InnerResolventObjective.inner_le_resQuad k (ht k) (hW.1 k k.2))
      (Cvs.Prolate.Gram.CentralResolventTrace.gpoly_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc k.2))
  have hθs : Summable fun k : LevelIdx (2 * π * x) => θ k := hW.2.subtype (fun k => ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) k χ)
  have hs : Summable (Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm (2 * π * x) t) :=
    Summable.of_nonneg_of_le (Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm_nonneg hc ht) hle hθs
  refine ⟨hs, (hs.tsum_le_tsum hle hθs).trans (le_of_eq ?_)⟩
  have hsupp : Function.support θ ⊆ {k | ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) k χ} := by
    intro k hk
    by_contra h
    exact hk (by simp only [θ, Cvs.Prolate.Gram.CentralResolventTrace.traceTerm]; exact ite_eq_right h)
  exact tsum_subtype_eq_of_support_subset hsupp

/-- **(B), excess form**: `ExcessComparison` holds. -/
theorem excessComparison : Cvs.Route.Visibility.CEBoundFromTrace.ExcessComparison := by
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hx hW hT
  have hc : 0 < 2 * π * x := by linarith
  choose t ht using fun k : LevelIdx (2 * π * x) => Cvs.Prolate.Gram.EvenProlateParsevalSplit.exists_innerSol hc (prolE k)
  obtain ⟨hs, hle⟩ := hasSum_le_Tc hx hW ht
  set T := ∑' k, Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm (2 * π * x) t k
  have hμ := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos
  have hmT : muStar * T < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hμ.le) hT
  have hT0 : 0 ≤ T := tsum_nonneg (Cvs.Prolate.Gram.CellGramTraceComparison.traceTerm_nonneg hc ht)
  have h := Cvs.Prolate.Gram.CellGramTraceComparison.excessTrace_le_trace hx ht hs.hasSum hmT
  exact h.trans (Cvs.Route.Visibility.CEBoundFromTrace.budget_mono hμ (Cvs.Prolate.Gram.CentralResolventTrace.aTop_nonneg hx) le_rfl hle (hT0.trans hle) hT)

/-- **(B)**: `TraceComparison` holds. -/
theorem traceComparison : Cvs.Route.Visibility.CEBoundFromTrace.TraceComparison := Cvs.Route.Visibility.CEBoundFromTrace.traceComparison_of_excess excessComparison

end Cvs.Prolate.Gram.TraceComparisonHolds

end
