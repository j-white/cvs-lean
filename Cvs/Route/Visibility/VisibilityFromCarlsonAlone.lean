import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.PotentialFloorFromCounts
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.TraceComparisonHolds
import Cvs.Prolate.Gram.TunnellingFloorSumAbove
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Hardy.BandRungHardyBound
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Prolate.Mellin.RungExteriorBoxBound
import Cvs.Prolate.TunnellingIntegralsAgree
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.AliasOffDiagonalIncoherence
import Cvs.Route.Visibility.CEBoundFromTrace
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.EvenBulkFloorFailsOffRh
import Cvs.Route.Visibility.EvenFirstCellPoisson
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.LogTailRateCellFloor
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.PerRungLogTailLaw
import Cvs.Route.Visibility.RungXBoxExplicit
import Cvs.Route.Visibility.ScalarTraceBudget
import Cvs.Route.Visibility.SummableBesselDisc
import Cvs.Route.Visibility.VisibilityAliasPlungeDischarge
import Cvs.Route.Visibility.VisibilityBandAboveLevel
import Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson
import Cvs.Route.Visibility.VisibilityHardyModule
import Cvs.Route.Visibility.VisibilityLandauBandCarlson
import Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor
import Cvs.Route.Visibility.WindowBesselDiscBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Route.Visibility.WindowLogEnergyCellFloor
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopIffFiniteBand
import Cvs.StepA.Edge.FreeInterpHolds
import Cvs.StepA.Edge.LemmaCFromCarlson
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.Upstream.InverseExcessPencilTop
import Cvs.Upstream.PencilLayerBound
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf
import Cvs.Zeta.ZeroCounting.InghamImpliesCarlson
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `AL`, `BandHardyMain` and `ExtTunnelSum` are unconditional, giving `hV` from `CarlsonBound` alone

Cancelling `1 − λ_t` between `energyE_le` and `a_t` proves `AL` without `LandauTransition`, and `Cvs.Prolate.Hardy.BandRungHardyBound`'s band-rung
bound `‖J_c(Qh_k)‖ ≤ 100` discharges `BandHardyMain` and `ExtTunnelSum`, giving `hV` from `CarlsonBound` alone.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace Cvs.Route.Visibility.VisibilityFromCarlsonAlone
open Cvs.ZeroCounting

/-! ### Unconditional main-band Hardy, resolvent, floor and tunnelling bounds -/

/-- **Main-band Hardy energies are `O(1)`**: `BandHardyMain` holds unconditionally. -/
theorem bandHardyMain : Cvs.Route.Visibility.VisibilityBandAboveLevel.BandHardyMain := by
  intro ε hε
  have hc_tend : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hpow_tend : Tendsto (fun x : ℕ => (x : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hc_tend.eventually_ge_atTop 2255,
    hpow_tend.eventually_ge_atTop 10000] with x hx80 hc2255 hpow j hj
  set T : ℝ := Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j
  have hc0 : 0 < (2 * π * x) := by linarith
  have hcinv : 0 < (2 * π * x) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hT : 3 / 4 ≤ T := by linarith
  have hT1 : T ≤ 1 := by
    have heq : T = Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j) := Cvs.Prolate.TunnellingIntegralsAgree.tLev_eq j
    rw [heq]
    exact (Cvs.Prolate.Gram.PotentialFloorFromCounts.levT_lt_one hx80 _).le
  have hδ : 1 ≤ (2 * π * x) * Cvs.Prolate.Hardy.BandRungHardyBound.delT T := by
    have hd := Cvs.Prolate.Hardy.BandRungHardyBound.delT_ge hT hT1
    have hsqrt : (2 * π * x) * (2 * π * x) ^ (-(1 / 2) : ℝ) = √(2 * π * x) := by
      calc (2 * π * x) * (2 * π * x) ^ (-(1 / 2) : ℝ) = (2 * π * x) ^ (1 : ℝ) * (2 * π * x) ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_one]
        _ = (2 * π * x) ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add hc0 1 (-(1 / 2))).symm
        _ = √(2 * π * x) := by norm_num [Real.sqrt_eq_rpow]
    have h4 : 4 ≤ √(2 * π * x) := by
      rw [show (4 : ℝ) = √16 by norm_num]
      exact Real.sqrt_le_sqrt (by linarith only [hc2255])
    have h1 : (2 * π * x) ^ (-(1 / 2) : ℝ) / 4 ≤ Cvs.Prolate.Hardy.BandRungHardyBound.delT T := by linarith only [hj, hd]
    have h2 : (2 * π * x) * ((2 * π * x) ^ (-(1 / 2) : ℝ) / 4) ≤ (2 * π * x) * Cvs.Prolate.Hardy.BandRungHardyBound.delT T := mul_le_mul_of_nonneg_left h1 hc0.le
    linarith only [hsqrt, h4, h2]
  have hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx80 (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j)
  have hχ : Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) = (2 * π * x) ^ 2 * T := by
    change Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) = (2 * π * x) ^ 2 * (Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) / (2 * π * x) ^ 2)
    rw [mul_div_cancel₀ _ (by positivity)]
  have hJ := Cvs.Prolate.Hardy.BandRungHardyBound.norm_hardyJ_rung_le hT hT1 hc2255 hδ hk (even_two_mul _) hχ
  have hJ2 : ‖Cvs.Prolate.Hardy.HardyExtensionOperator.hardyJ (2 * π * x) (Cvs.Prolate.Hardy.CentralRungExpansion.qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk (2 * π * x) (2 * (j : ℕ))))‖ ^ 2 ≤ 10000 := by
    nlinarith [norm_nonneg (Cvs.Prolate.Hardy.HardyExtensionOperator.hardyJ (2 * π * x) (Cvs.Prolate.Hardy.CentralRungExpansion.qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk (2 * π * x) (2 * (j : ℕ)))))]
  exact hJ2.trans hpow

/-- **Band Hardy energies above every `τ > ¾`** hold unconditionally. -/
theorem bandHardyAbove {τ : ℝ} (hτ : 3 / 4 < τ) : Cvs.Route.Visibility.VisibilityBandAboveLevel.BandHardyAbove τ :=
  Cvs.Route.Visibility.VisibilityBandAboveLevel.bandHardyAbove_of_main bandHardyMain hτ

/-- **Band highpass extensions above every `τ > ¾`** hold unconditionally. -/
theorem bandHighpassAbove {τ : ℝ} (hτ : 3 / 4 < τ) : Cvs.Route.Visibility.VisibilityBandAboveLevel.BandHighpassAbove τ :=
  Cvs.Route.Visibility.VisibilityBandAboveLevel.bandHighpassAbove_of_bandHardyAbove (bandHardyAbove hτ)

/-- **The band resolvent bound above every `τ > ¾`** holds unconditionally. -/
theorem bandResolventAbove {τ : ℝ} (hτ : 3 / 4 < τ) : Cvs.Route.Visibility.VisibilityBandAboveLevel.BandResolventAbove τ :=
  Cvs.Route.Visibility.VisibilityBandAboveLevel.bandResolventAbove_of_bandHighpassAbove (bandHighpassAbove hτ)

/-- **The band floor above every `τ > ¾`** holds unconditionally. -/
theorem bandFloorAbove {τ : ℝ} (hτ : 3 / 4 < τ) : Cvs.Prolate.Gram.TunnellingFloorSumAbove.BandFloorAbove τ :=
  Cvs.Route.Visibility.VisibilityBandAboveLevel.bandFloorAbove_of_bandResolventAbove (bandResolventAbove hτ)

/-- **The exterior tunnelling sum** holds unconditionally for every `η ≥ 0`. -/
theorem extTunnelSum {η : ℝ} (hη : 0 ≤ η) : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η :=
  Cvs.Prolate.Gram.TunnellingFloorSumAbove.extTunnelSum_of_bandFloorAbove (τ := 4 / 5) (by norm_num) (bandFloorAbove (by norm_num)) hη

/-- **The per-rung box bound** with saving `1` holds unconditionally. -/
theorem rungBox_one : Cvs.Route.Visibility.PerRungBoxBound.RungBox 1 :=
  Cvs.Route.Visibility.RungXBoxExplicit.rungBox_one_of_lemmaX ⟨1 / 4, by norm_num, by norm_num, extTunnelSum (by norm_num)⟩ Cvs.Prolate.Mellin.RungExteriorBoxBound.rungLemmaX

/-! ### Unconditional `AL` and cell floors without `LandauTransition` or `TopCeiling` -/

/-- Cancelling `1 − λ_t` in `a_t`: `2(1 − λ_t)a_t = 4/(λ_t(1 + √λ_t)³) ≤ 5/3` for all `λ_t ∈ [½, 1)`. -/
theorem two_mul_one_sub_mul_aTop_le {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    2 * (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Prolate.Gram.CentralResolventTrace.aTop x ≤ 5 / 3 := by
  set l := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x
  have hl1 : l < 1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have hl2 : 1 / 2 ≤ l := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have hs0 : 0 ≤ √l := Real.sqrt_nonneg l
  have hsl : √l ^ 2 = l := Real.sq_sqrt (by linarith)
  have hs7 : 7 / 10 ≤ √l := by nlinarith
  have hcube : (17 / 10 : ℝ) ^ 3 ≤ (1 + √l) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hden : 12 / 5 ≤ l * (1 + √l) ^ 3 :=
    calc (12 / 5 : ℝ) ≤ 1 / 2 * (17 / 10) ^ 3 := by norm_num
      _ ≤ l * (1 + √l) ^ 3 := mul_le_mul hl2 hcube (by norm_num) (by linarith)
  unfold Cvs.Prolate.Gram.CentralResolventTrace.aTop
  have h1l : 1 - l ≠ 0 := by linarith
  have heq : 2 * (1 - l) * (2 / ((1 - l) * l * (1 + √l) ^ 3)) = 4 / (l * (1 + √l) ^ 3) := by
    field_simp
    ring
  change 2 * (1 - l) * (2 / ((1 - l) * l * (1 + √l) ^ 3)) ≤ 5 / 3
  rw [heq, div_le_iff₀ (by linarith)]
  linarith

/-- Eventually `(1 − λ_t)c_E^C ≤ (μ* + 7/10)/2`, unconditionally (without `TopCeiling`). -/
theorem eventually_one_sub_lamTop_mul_cE_le :
    ∀ᶠ x : ℕ in atTop, (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Route.Visibility.LayerFloorDeepRemainderB.cE x ≤ (Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10) / 2 := by
  filter_upwards [Cvs.Prolate.Gram.TraceComparisonHolds.traceComparison, Cvs.Prolate.Hardy.TraceLimitHighpassOperator.traceLimit Cvs.Route.Visibility.VisibilityHardyModule.highpassColumnLimsup_three_fifths,
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hcmp ⟨hW, hTc⟩ hx
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hTc0 : 0 ≤ Cvs.Prolate.Gram.CentralResolventTrace.Tc x := tsum_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.traceTerm_nonneg hc0 hW)
  have hden := Cvs.Route.Visibility.ScalarTraceBudget.denominator_ge Cvs.Route.Visibility.ScalarTraceBudget.muStar_le_seven_tenths hTc0 hTc
  have hmT : Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar * Cvs.Prolate.Gram.CentralResolventTrace.Tc x < 1 := by linarith
  have hcE := hcmp hW hmT
  have hl1 : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x < 1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have hl2 : 1 / 2 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have hm := mul_le_mul_of_nonneg_left hcE (by linarith : 0 ≤ 1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x)
  have hex := Cvs.Route.Visibility.ScalarTraceBudget.prolate_excess_lt_seven_tenths (two_mul_one_sub_mul_aTop_le hx) hTc0 hTc
  have hrew : (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * (2 * Cvs.Prolate.Gram.CentralResolventTrace.aTop x * Cvs.Prolate.Gram.CentralResolventTrace.Tc x / (1 - Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar * Cvs.Prolate.Gram.CentralResolventTrace.Tc x)) =
      (2 * (2 * (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Prolate.Gram.CentralResolventTrace.aTop x) * Cvs.Prolate.Gram.CentralResolventTrace.Tc x / (1 - Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar * Cvs.Prolate.Gram.CentralResolventTrace.Tc x)) / 2 := by
    ring
  have hmu : (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar ≤ Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar / 2 := by
    have := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos; nlinarith
  linarith

/-- **`AL` holds unconditionally**: for some `η₀ ∈ (0, 1)`, `AL η₀` holds without any prolate ceiling hypothesis. -/
theorem exists_al : ∃ η₀, 0 < η₀ ∧ η₀ < 1 ∧ Cvs.Route.Visibility.WindowChainCellFloors.AL η₀ := by
  have hm := Cvs.Upstream.InverseExcessPencilTop.excess_seven_tenths_margin
  have hC0p := Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf_pos (57 / 60)
  have hmp := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos
  set L := Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf (57 / 60) * ((Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10) / 2)
  have hL0 : 0 < L := by positivity
  have hL1 : L < 1 := by simp only [L]; linarith
  set κ := (L + 1) / 2
  have hκ0 : 0 < κ := by simp only [κ]; linarith
  have hκ1 : κ < 1 := by simp only [κ]; linarith
  have hlim : Tendsto (fun x : ℕ => Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0 (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC x * ((Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10) / 2))
      atTop (𝓝 L) := (Cvs.Route.Visibility.LayerFloorDeepRemainderB.tendsto_C0 (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC).mul_const _
  refine ⟨√κ, Real.sqrt_pos.2 hκ0, ?_, ?_⟩
  · rw [Real.sqrt_lt' one_pos]; simpa using hκ1
  filter_upwards [hlim.eventually (gt_mem_nhds (show L < κ by simp only [κ]; linarith)),
    eventually_one_sub_lamTop_mul_cE_le, Cvs.Route.Visibility.VisibilityAliasPlungeDischarge.alr, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hC hce hr hx b
  rw [Real.sq_sqrt hκ0.le]
  have hE := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.energyE_le hx b
  have hc0 := Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0_nonneg (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC x
  have hM : 0 ≤ ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  set A := ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2
  calc (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2
      ≤ Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0 (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC x * Cvs.Prolate.Gram.ProlateCellGramHalfUnit.energyE x b := hr b
    _ ≤ Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0 (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC x * ((1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Route.Visibility.LayerFloorDeepRemainderB.cE x * A) :=
        mul_le_mul_of_nonneg_left hE hc0
    _ = Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0 (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC x * ((1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Route.Visibility.LayerFloorDeepRemainderB.cE x) * A := by ring
    _ ≤ Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0 (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC x * ((Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10) / 2) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hce hc0) hM
    _ ≤ κ * A := mul_le_mul_of_nonneg_right hC.le hM

/-- **The prolate cell floors hold unconditionally.** -/
theorem exists_isCellFloor :
    ∃ η₀, 0 < η₀ ∧ η₀ < 1 ∧ ∀ᶠ x : ℕ in atTop, Cvs.Route.Visibility.CaseFiniteCellFloorRates.IsCellFloor x (Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) := by
  obtain ⟨η₀, h0, h1, hAL⟩ := exists_al
  refine ⟨η₀, h0, h1, ?_⟩
  filter_upwards [Cvs.Route.Visibility.WindowChainCellFloors.cellFloor_le_of_al h0 h1 hAL, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x h hx
  exact ⟨Cvs.Route.Visibility.WindowChainCellFloors.cellFloor_pos hx h1, h⟩

/-! ### `hV` on `TopAttained` unconditionally, and from `CarlsonBound` (or `LemmaC`) alone in general -/

/-- **Case F (`TopAttained`) is unconditional**: if off-line zeros attain a maximum real part, the zero even bulk floor
fails at all large `x`. -/
theorem hV_of_topAttained (hTop : Cvs.StepA.Edge.FiniteTopIffFiniteBand.TopAttained) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := fun hRH => by
  obtain ⟨S, δ, hS⟩ := hTop hRH
  obtain ⟨η₀, -, hη₀, hδ⟩ := exists_isCellFloor
  obtain ⟨A, hA, hB⟩ := Cvs.Route.Visibility.SummableBesselDisc.exists_besselDiscS
  have hη0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hη1 : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hTun := extTunnelSum hη0.le
  obtain ⟨F, ν, hBx, hs⟩ := Cvs.Route.Visibility.PerRungBoxBound.rungBox_cellFloor hη₀ rungBox_one
  have hT : ∀ δ' : ℝ, 0 < δ' → δ' < 1 / 2 →
      Cvs.Route.Visibility.CaseFiniteCellFloorRates.LogTailRate (1 / 2 - (δ' + (1 / 2 - δ') / 2)) (1 / 2 + (δ' + (1 / 2 - δ') / 2)) :=
    fun δ' _ _ => Cvs.Route.Visibility.LogTailRateCellFloor.logTailRate_of_profile hη₀ hδ hTun (Cvs.Route.Visibility.PerRungLogTailLaw.logTailProfile hη0 hη1) (by linarith) (by linarith)
  have hEx : ∀ δ' : ℝ, 0 < δ' → δ' < 1 / 2 →
      Cvs.Route.Visibility.CaseFiniteCellFloorRates.ExtFloorSum (fun x => Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) (1 / 2 + (δ' + (1 / 2 - δ') / 2)) :=
    fun δ' _ _ => Cvs.Route.Visibility.CaseFiniteFromWindowChain.extFloorSum_of_tunnel (by linarith) hη0 hη1 hη₀ hTun
  have hh := Cvs.Route.Visibility.CaseFiniteCellFloorRates.caseF_h_of_floor hδ (fun S' _ _ => Cvs.Route.Visibility.PerRungBoxBound.xFloorSum_of_box le_rfl hBx hs S') hEx hT hA
    (Cvs.Route.Visibility.PerRungBoxBound.besselDisc_of_besselDiscS hB)
  exact Cvs.Route.Visibility.EvenBulkFloorFailsOffRh.eventually_not_evenBulkFloor_of_m1_m2 hS (hh S δ hS)

/-- **`hV` from `LemmaC` alone** (zero prolate hypotheses). -/
theorem hV_of_lemmaC (hC : Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  obtain ⟨η₀, -, hη₀, hδ⟩ := exists_isCellFloor
  have hη0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hη1 : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hTun := extTunnelSum hη0.le
  rcases Cvs.Route.Visibility.VisibilityLandauBandCarlson.winInput with ⟨ν, hν, hWR⟩ | ⟨η', hη', hWT⟩
  · exact Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson.hV_of_cellFloor hη₀ hδ hη0 hη1 hTun (Cvs.Route.Visibility.PerRungLogTailLaw.logTailProfile hη0 hη1) rungBox_one
      (Cvs.Route.Visibility.WindowBesselDiscBound.m1PrimeHalf_of_winLogReg hWR hν) Cvs.StepA.Edge.DbarTransplantHolds.dbarTransplant Cvs.StepA.Edge.FreeInterpHolds.freeInterp hC
  · exact Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson.hV_of_cellFloor hη₀ hδ hη0 hη1 hTun (Cvs.Route.Visibility.PerRungLogTailLaw.logTailProfile hη0 hη1) rungBox_one
      (Cvs.Route.Visibility.WindowBesselDiscBound.m1PrimeHalf_of_winLogReg (Cvs.Route.Visibility.WindowLogEnergyCellFloor.winLogReg_of_profile hη₀ hδ (extTunnelSum hη') hWT) one_pos)
      Cvs.StepA.Edge.DbarTransplantHolds.dbarTransplant Cvs.StepA.Edge.FreeInterpHolds.freeInterp hC

/-- **`hV` from `CarlsonBound` alone**. -/
theorem hV_of_carlson (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  hV_of_lemmaC (Cvs.StepA.Edge.LemmaCFromCarlson.lemmaC_of_carlson hCarl)

/-- **`hV` from `CarlsonDensity` alone**. -/
theorem hV_of_carlsonDensity (hCD : Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.CarlsonDensity) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  hV_of_carlson (Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.carlsonBound_of_carlsonDensity hCD)

/-- **`hV` from `InghamDensity` alone**. -/
theorem hV_of_ingham (hIng : Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.InghamDensity) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  hV_of_carlsonDensity (Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.carlsonDensity_of_inghamDensity hIng)

/-- **`hV` in `Cvs.WeilForm.EvenBulkVisibility`'s visibility form** from `LemmaC` alone. -/
theorem hV_visible_of_lemmaC (hC : Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Cvs.Route.L1FloorFromBulkD0.Dom x → ℝ) (b : Cvs.Route.L1FloorFromBulkD0.Dom x), b ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x ∧
      (∀ u ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, Cvs.Route.WindowPositivityBulkCoupling.Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b) < 4 * ‖b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b‖ ^ 4 :=
  Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor.hV_iff.2 (hV_of_lemmaC hC)

/-- **`hV` in `Cvs.WeilForm.EvenBulkVisibility`'s visibility form** from `CarlsonBound` alone. -/
theorem hV_visible_of_carlson (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Cvs.Route.L1FloorFromBulkD0.Dom x → ℝ) (b : Cvs.Route.L1FloorFromBulkD0.Dom x), b ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x ∧
      (∀ u ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, Cvs.Route.WindowPositivityBulkCoupling.Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b) < 4 * ‖b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b‖ ^ 4 :=
  Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor.hV_iff.2 (hV_of_carlson hCarl)

/-- **`hV` in `Cvs.WeilForm.EvenBulkVisibility`'s visibility form** from `InghamDensity` alone. -/
theorem hV_visible_of_ingham (hIng : Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.InghamDensity) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Cvs.Route.L1FloorFromBulkD0.Dom x → ℝ) (b : Cvs.Route.L1FloorFromBulkD0.Dom x), b ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x ∧
      (∀ u ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, Cvs.Route.WindowPositivityBulkCoupling.Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b) < 4 * ‖b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b‖ ^ 4 :=
  Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor.hV_iff.2 (hV_of_ingham hIng)

/-! ### `RiemannHypothesis` routes via `Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor` and `Cvs.WeilForm.EvenBulkVisibility` -/

/-- **`RiemannHypothesis` from the eventual even bulk floor** and `LemmaC` alone. -/
theorem rh_of_evenBulkFloor_lemmaC (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hC : Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC) : RiemannHypothesis :=
  Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor.rh_of_eventually_evenBulkFloor_of_frequently_visible (fun hRH => (hV_of_lemmaC hC hRH).frequently) hF

/-- **`RiemannHypothesis` from the eventual even bulk floor** and `CarlsonBound` alone. -/
theorem rh_of_evenBulkFloor_carlson (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) : RiemannHypothesis :=
  rh_of_evenBulkFloor_lemmaC hF (Cvs.StepA.Edge.LemmaCFromCarlson.lemmaC_of_carlson hCarl)

/-- **`RiemannHypothesis` from the eventual even bulk floor** and `CarlsonDensity` alone. -/
theorem rh_of_evenBulkFloor_carlsonDensity (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hCD : Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.CarlsonDensity) : RiemannHypothesis :=
  rh_of_evenBulkFloor_carlson hF (Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.carlsonBound_of_carlsonDensity hCD)

/-- **`RiemannHypothesis` from the eventual even bulk floor** and `InghamDensity` alone. -/
theorem rh_of_evenBulkFloor_ingham (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hIng : Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.InghamDensity) : RiemannHypothesis :=
  rh_of_evenBulkFloor_carlsonDensity hF (Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.carlsonDensity_of_inghamDensity hIng)

/-- **`RiemannHypothesis` via `Cvs.WeilForm.EvenBulkVisibility`** from the eventual even bulk floor and `CarlsonBound` alone. -/
theorem rh_of_visible_carlson (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) : RiemannHypothesis :=
  Cvs.WeilForm.EvenBulkVisibility.rh_of_eventually_evenBulkFloor_of_visible (hV_visible_of_carlson hCarl) hF

/-- **`RiemannHypothesis` via `Cvs.WeilForm.EvenBulkVisibility`** from the eventual even bulk floor and `InghamDensity` alone. -/
theorem rh_of_visible_ingham (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hIng : Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.InghamDensity) : RiemannHypothesis :=
  rh_of_visible_carlson hF (Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.carlsonBound_of_carlsonDensity (Cvs.Zeta.ZeroCounting.InghamImpliesCarlson.carlsonDensity_of_inghamDensity hIng))

end Cvs.Route.Visibility.VisibilityFromCarlsonAlone

end
