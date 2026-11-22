import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.EvenBulkFloorFailsOffRh
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.LogTailRateCellFloor
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.PerRungLogTailLaw
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.SummableBesselDisc
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.VisibilityFromCarlsonAlone
import Cvs.Route.Visibility.VisibilityLandauBandCarlson
import Cvs.Route.Visibility.WindowBesselDiscBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Route.Visibility.WindowLogEnergyCellFloor
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.DeepJointShare
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.DeepZerosAboveCutoff
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopIffFiniteBand
import Cvs.StepA.Edge.FreeInterpHolds
import Cvs.StepA.Edge.GapRectangleBlaschke
import Cvs.StepA.Edge.LemmaCFromCarlson
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
import Cvs.Zeta.ZeroCounting.GappedCutoffPairMass
import Cvs.Zeta.ZeroCounting.SublinearZeroDensity
import Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroTailInverseSquare

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Unconditional `LemmaC`, Case ∞ (`NoTop`), and unconditional `hV`

`Cvs.Zeta.ZeroCounting.SublinearZeroDensity.sublinearZeroDensity` bounds `#deepSet δ_D T` sublinearly (`O(T^{1 - 2κ})`, `0 < κ ≤ 1`), discharging
`Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC` and `Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop` unconditionally, and hence proving `hV` and `hV_visible` unconditionally via `Cvs.Route.Visibility.VisibilityFromCarlsonAlone`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset Asymptotics
open scoped InnerProductSpace
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (bexp)
open Cvs.StepA.Edge.GapRectangleBlaschke (kcg qg)
open Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff (phiNear)
open Cvs.Zeta.ZeroCounting.SublinearZeroDensity (SublinearZeroDensity)

namespace Cvs.Route.Visibility.VisibilityUnconditional
open Cvs.ZeroCounting

/-! ### Unconditional sublinear deep-set count and `LemmaC` -/

/-- **Sublinear deep-set count**: `SublinearZeroDensity` gives `0 < κ ≤ 1` with `#deepSet δ_D T ≤ C · T^{1 - 2κ}` for
all `T ≥ T₀`. -/
theorem deepSet_card_le_of_sublinear (hSub : SublinearZeroDensity) {δD : ℝ} (hδ : 0 < δD)
    (hδ' : δD < 1 / 2) :
    ∃ κ C T₀ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ((deepSet δD T).card : ℝ) ≤ C * T ^ (1 - 2 * κ) := by
  obtain ⟨θ₀, hθ0, hθ1, hO⟩ := hSub (1 / 2 + δD) (by linarith [hδ]) (by linarith [hδ'])
  set κ : ℝ := min ((1 - θ₀) / 2) (δD ^ 2)
  have hκ0 : 0 < κ := lt_min (by linarith [hθ1]) (by positivity)
  have hκ1 : κ ≤ 1 := (min_le_right _ _).trans (by nlinarith [hδ, hδ', hθ0])
  have hθ_le : θ₀ ≤ 1 - 2 * κ := by
    have hmin := min_le_left ((1 - θ₀) / 2) (δD ^ 2)
    linarith
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hc
  refine ⟨κ, 4 * max c 0, max T₁ 1, hκ0, hκ1, by positivity, fun T hT => ?_⟩
  have hT_ge1 : 1 ≤ T := (le_max_right T₁ 1).trans hT
  have hT0 : 0 ≤ T := by linarith
  have h1 := hT₁ T ((le_max_left T₁ 1).trans hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hT0 _)] at h1
  have h2 : ((deepSet δD T).card : ℝ) ≤ 4 * (Cvs.GaussKernel.carlsonCount (1 / 2 + δD) T : ℝ) := by
    rw [Cvs.StepA.Edge.DeepZerosAboveCutoff.deepSet_eq_offLineWindow]
    exact_mod_cast Cvs.GaussKernel.offLineCount_le_four_mul_carlsonCount hδ T
  have h3 : (Cvs.GaussKernel.carlsonCount (1 / 2 + δD) T : ℝ)
      ≤ Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.N_zero (1 / 2 + δD) T := by
    exact_mod_cast Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.carlsonCount_le_N_zero (by linarith [hδ]) hT0
  have h4 : c * T ^ θ₀ ≤ max c 0 * T ^ (1 - 2 * κ) :=
    calc c * T ^ θ₀ ≤ max c 0 * T ^ θ₀ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hT0 _)
      _ ≤ max c 0 * T ^ (1 - 2 * κ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT_ge1 hθ_le) (le_max_right _ _)
  linarith

/-- **Unconditional sublinear deep-set count** for every `0 < δ_D < 1/2`. -/
theorem deepSet_card_le {δD : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) :
    ∃ κ C T₀ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ((deepSet δD T).card : ℝ) ≤ C * T ^ (1 - 2 * κ) :=
  deepSet_card_le_of_sublinear Cvs.Zeta.ZeroCounting.SublinearZeroDensity.sublinearZeroDensity hδ hδ'

/-- Eventual scale and sublinear-density smallness at `X = x^{ε₂}` for any `κ > 0`. -/
theorem eventually_big_sublinear {ε₂ κ C T₀ : ℝ} (hε₂ : 0 < ε₂) (hκ : 0 < κ) :
    ∀ᶠ x : ℕ in atTop, 1 ≤ x ∧ 12 ≤ (x : ℝ) ^ ε₂ ∧ T₀ ≤ 4 * (x : ℝ) ^ ε₂
      ∧ 12 * C * 4 ^ (1 - 2 * κ) * (x : ℝ) ^ (ε₂ * ((1 - 2 * κ) - 1)) ≤ 1 := by
  have h1 := Cvs.Route.Visibility.ExtPairingRatesSubpoly.tendsto_natCast_rpow hε₂
  have h2 : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε₂ * ((1 - 2 * κ) - 1))) atTop (𝓝 0) := by
    have heq : ε₂ * ((1 - 2 * κ) - 1) = -(2 * κ * ε₂) := by ring
    rw [heq]
    exact (tendsto_rpow_neg_atTop (mul_pos (mul_pos two_pos hκ) hε₂)).comp tendsto_natCast_atTop_atTop
  have h3 := h2.const_mul (12 * C * 4 ^ (1 - 2 * κ))
  rw [mul_zero] at h3
  filter_upwards [eventually_ge_atTop 1, h1.eventually_ge_atTop 12, h1.eventually_ge_atTop (T₀ / 4),
    h3.eventually (ge_mem_nhds one_pos)] with x hx a1 a2 a3
  exact ⟨hx, a1, by linarith, a3⟩

set_option maxHeartbeats 4000000 in
/-- **`LemmaC` holds from `SublinearZeroDensity`** with `α = 2(bexp + 1) + 1`. -/
theorem lemmaC_of_sublinear (hSub : SublinearZeroDensity) : Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC := by
  refine ⟨2 * ((bexp : ℝ) + 1) + 1, by positivity, fun δD hδ hδ' => ?_⟩
  obtain ⟨κ, Cc, T₀, hκ0, hκ1, hCc, hcount⟩ := deepSet_card_le_of_sublinear hSub hδ hδ'
  refine ⟨κ, hκ0, fun ε₂ hε₂ hαε => ?_⟩
  set θ := 1 - 2 * κ with hθ
  have hbig := eventually_big_sublinear (C := Cc) (T₀ := T₀) hε₂ hκ0
  have hcnt : ∀ x : ℕ, 1 ≤ x → T₀ ≤ 4 * (x : ℝ) ^ ε₂ →
      12 * Cc * 4 ^ θ * (x : ℝ) ^ (ε₂ * (θ - 1)) ≤ 1 →
      ((deepSet δD (4 * (x : ℝ) ^ ε₂)).card : ℝ) ≤ Cc * (4 * (x : ℝ) ^ ε₂) ^ θ
        ∧ 12 * ((deepSet δD (4 * (x : ℝ) ^ ε₂)).card : ℝ) ≤ (x : ℝ) ^ ε₂ := by
    intro x hx hT hs
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    have hc := hcount _ hT
    refine ⟨hc, ?_⟩
    rw [Cvs.StepA.Edge.LemmaCFromCarlson.four_mul_rpow hx0] at hc
    have hX0 : 0 ≤ (x : ℝ) ^ ε₂ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs hX0]
  have hex : ∀ᶠ x : ℕ in atTop, ∃ H, Cvs.StepA.Edge.LemmaCFromCarlson.GoodCut δD ε₂ x H := by
    filter_upwards [hbig] with x hxb
    obtain ⟨hx, hX, hT, hs⟩ := hxb
    obtain ⟨_, hsmall⟩ := hcnt x hx hT hs
    obtain ⟨h2N, hJ1, _⟩ := Cvs.StepA.Edge.LemmaCFromCarlson.nJ_facts hX hsmall
    exact Cvs.Zeta.ZeroCounting.GappedCutoffPairMass.lemmaP (by linarith) hJ1 h2N
  have hcut : Cvs.StepA.Edge.CaseInfinityJointRates.Cutoff ε₂ (Cvs.StepA.Edge.LemmaCFromCarlson.cutH δD ε₂) :=
    hex.mono fun x h => ⟨(Cvs.StepA.Edge.LemmaCFromCarlson.goodCut_cutH h).1, (Cvs.StepA.Edge.LemmaCFromCarlson.goodCut_cutH h).2.1⟩
  refine ⟨Cvs.StepA.Edge.LemmaCFromCarlson.cutH δD ε₂, hcut, Cvs.StepA.Edge.LemmaCFromCarlson.qC δD Cc θ ε₂, Cvs.StepA.Edge.LemmaCFromCarlson.subPoly_qC hδ hCc hε₂, ?_⟩
  have hαε' : ((bexp : ℝ) + 1) * ε₂ < δD / 8 := by nlinarith [hαε]
  have hq := Cvs.StepA.Edge.FreeInterpHolds.eventually_good hδ hδ' hε₂ hαε' hcut 0
  have hm : 0 < 2 * κ * ε₂ := by positivity
  have hq1 := Cvs.Route.Visibility.ExtPairingRatesSubpoly.eventually_mul_rpow_le (Cvs.StepA.Edge.LemmaCFromCarlson.subPoly_q1 (θ := θ) hCc hε₂).1 hm 0 one_pos
  filter_upwards [hbig, hex, hq, hq1, (Cvs.StepA.Edge.LemmaCFromCarlson.subPoly_q1 (θ := θ) hCc hε₂).2] with x hxb hgood hqx hq1x hq1n
  intro hx0
  obtain ⟨hx, hX, hT, hs⟩ := hxb
  obtain ⟨_, _, _, hqq, _⟩ := hqx
  set X := (x : ℝ) ^ ε₂ with hXdef
  set H := Cvs.StepA.Edge.LemmaCFromCarlson.cutH δD ε₂ x
  have hG := Cvs.StepA.Edge.LemmaCFromCarlson.goodCut_cutH hgood
  obtain ⟨hc, hsmall⟩ := hcnt x hx hT hs
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hexp : ε₂ * (θ - 1) = 0 - 2 * κ * ε₂ := by rw [hθ]; ring
  have hPm := Cvs.StepA.Edge.LemmaCFromCarlson.pairMass_le hx hX hc hsmall hG
  rw [hexp] at hPm
  rw [Real.rpow_zero, mul_one] at hq1x
  have hP1 := hPm.trans hq1x
  have hqg : qg x δD H ≤ 1 / 2 := (Cvs.StepA.Edge.LemmaCFromCarlson.qg_le_qq x δD H hδ (by linarith [hG.1])).trans hqq
  obtain ⟨hH1, hH2, hgap, _⟩ := hG
  have hsum := Cvs.StepA.Edge.DeepZerosAboveCutoff.sum_above_proj_le hx0 hδ hδ' (by linarith) hgap hqg (M := 4 * X) (by linarith)
    (by have := Real.exp_one_lt_d9; linarith) hP1
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  set y := (x : ℝ) ^ (-(κ * ε₂)) with hy
  have hy0 : 0 ≤ y := by positivity
  have hP2 : phiNear δD H (4 * X) + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * X)
      ≤ Cvs.StepA.Edge.LemmaCFromCarlson.q1 Cc θ ε₂ x * y := by
    refine hPm.trans (mul_le_mul_of_nonneg_left ?_ hq1n)
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hκ0, hε₂])
  have hkc := Cvs.StepA.Edge.DbarTransplantHolds.kc_le hδ hδ' (by linarith : (1 : ℝ) ≤ X) hH1 hH2
  have hkcg := (Cvs.StepA.Edge.LemmaCFromCarlson.kcg_le_kc δD H hδ (by linarith)).trans hkc
  have hkcg0 : 0 ≤ kcg δD H := by
    unfold kcg; rw [Cvs.StepA.Edge.GapRectangleBlaschke.zg_re, Cvs.StepA.Edge.GapRectangleBlaschke.zg_im, Cvs.StepA.Edge.GapRectangleBlaschke.wg_re, Cvs.StepA.Edge.GapRectangleBlaschke.wg_im]
    refine div_nonneg (by nlinarith) ?_
    have := Real.pi_pos; have := Real.sqrt_nonneg (2 * (δD / 4)); positivity
  have hX2 : X ^ (bexp + 1) * X ^ (bexp + 1) * (x : ℝ) ^ (-(δD / 2)) ≤ y := by
    rw [hXdef, ← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, hy]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    have := mul_le_mul_of_nonneg_right hκ1 hε₂.le
    linarith [hαε]
  have hK2 : 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2)) ≤ 4 * Cvs.StepA.Edge.LemmaCFromCarlson.c0 δD ^ 2 * y := by
    have h1 : kcg δD H ^ 2 ≤ (Cvs.StepA.Edge.LemmaCFromCarlson.c0 δD * X ^ (bexp + 1)) ^ 2 := pow_le_pow_left₀ hkcg0 hkcg 2
    have h2 : (Cvs.StepA.Edge.LemmaCFromCarlson.c0 δD * X ^ (bexp + 1)) ^ 2 * (x : ℝ) ^ (-(δD / 2))
        = Cvs.StepA.Edge.LemmaCFromCarlson.c0 δD ^ 2 * (X ^ (bexp + 1) * X ^ (bexp + 1) * (x : ℝ) ^ (-(δD / 2))) := by ring
    have h3 : 0 ≤ (x : ℝ) ^ (-(δD / 2)) := by positivity
    have := mul_le_mul_of_nonneg_right h1 h3
    rw [h2] at this
    have h4 := mul_le_mul_of_nonneg_left hX2 (sq_nonneg (Cvs.StepA.Edge.LemmaCFromCarlson.c0 δD))
    nlinarith
  have hlog : Real.log (2 * H + 5) ≤ Real.log (4 * X + 5) := Real.log_le_log (by linarith) (by linarith)
  have hL : 0 ≤ 528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 2 * H + 5 by linarith)
    linarith [Cvs.StepA.Edge.LemmaCFromCarlson.invSqSum_nonneg]
  have hxT : (0 : ℝ) ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth := by positivity
  have hfin : (x : ℝ) ^ (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - κ * ε₂) = (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * y := by
    rw [hy, ← Real.rpow_add hx0]; ring_nf
  rw [hfin]
  calc 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * (phiNear δD H (4 * X) + 4 * (deepSet δD H).card
        * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * X)) / δD + 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2))
        * (528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum))
      ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * (Cvs.StepA.Edge.LemmaCFromCarlson.q1 Cc θ ε₂ x * y) / δD + 4 * Cvs.StepA.Edge.LemmaCFromCarlson.c0 δD ^ 2 * y
        * (528 * Real.log (4 * X + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hxT
        · exact div_le_div_of_nonneg_right (by linarith [hP2]) hδ.le
        · refine mul_le_mul hK2 (by linarith [hlog]) hL (mul_nonneg (by positivity) hy0)
    _ = Cvs.StepA.Edge.LemmaCFromCarlson.qC δD Cc θ ε₂ x * ((x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * y) := by unfold Cvs.StepA.Edge.LemmaCFromCarlson.qC; ring

/-- **`LemmaC` holds unconditionally**. -/
theorem lemmaC : Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC :=
  lemmaC_of_sublinear Cvs.Zeta.ZeroCounting.SublinearZeroDensity.sublinearZeroDensity

/-! ### Unconditional Case ∞ (`NoTop`) joint rates and visibility -/

/-- **Route SEP exterior data with saving `1`** holds unconditionally. -/
theorem sepData_one : Cvs.StepA.Edge.CaseInfinityJointRates.SEPData 1 := by
  obtain ⟨η₀, -, hη₀, hδ⟩ := Cvs.Route.Visibility.VisibilityFromCarlsonAlone.exists_isCellFloor
  obtain ⟨_, _, hBx, hs⟩ := Cvs.Route.Visibility.PerRungBoxBound.rungBox_cellFloor hη₀ Cvs.Route.Visibility.VisibilityFromCarlsonAlone.rungBox_one
  exact Cvs.Route.Visibility.PerRungBoxBound.sepData_of_floor_box hδ hBx hs

/-- **`M1Prime 1` holds unconditionally off `RiemannHypothesis`**. -/
theorem m1Prime_one_of_not_rh (hRH : ¬ RiemannHypothesis) : Cvs.StepA.Edge.CaseInfinityJointRates.M1Prime 1 := by
  obtain ⟨η₀, -, hη₀, hδ⟩ := Cvs.Route.Visibility.VisibilityFromCarlsonAlone.exists_isCellFloor
  rcases lt_or_eq_of_le (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_le_half hRH) with hlt | heq
  · obtain ⟨A, hA, hB⟩ := Cvs.Route.Visibility.SummableBesselDisc.exists_besselDiscS
    have hη0 : (0 : ℝ) < 1 / 4 := by norm_num
    have hη1 : (1 / 4 : ℝ) < 1 / 2 := by norm_num
    have hTun := Cvs.Route.Visibility.VisibilityFromCarlsonAlone.extTunnelSum hη0.le
    have h0 := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_pos hRH
    set σ := 1 / 2 + (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth + (1 / 2 - Cvs.StepA.Edge.CaseInfinityJointRates.topDepth) / 2)
    set α := 1 / 2 - (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth + (1 / 2 - Cvs.StepA.Edge.CaseInfinityJointRates.topDepth) / 2)
    have hσ : σ < 1 := by dsimp only [σ]; linarith [hlt]
    have hα : 0 < α := by dsimp only [α]; linarith [h0, hlt]
    have hEx : Cvs.Route.Visibility.CaseFiniteCellFloorRates.ExtFloorSum (fun x => Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) σ :=
      Cvs.Route.Visibility.CaseFiniteFromWindowChain.extFloorSum_of_tunnel hσ hη0 hη1 hη₀ hTun
    obtain ⟨μ, hμ, hμ0, hμs⟩ := hEx
    have hT : Cvs.Route.Visibility.CaseFiniteCellFloorRates.LogTailRate α σ :=
      Cvs.Route.Visibility.LogTailRateCellFloor.logTailRate_of_profile hη₀ hδ hTun (Cvs.Route.Visibility.PerRungLogTailLaw.logTailProfile hη0 hη1) hα hσ
    exact Cvs.Route.Visibility.PerRungBoxBound.m1Prime_of_besselDiscS hA hB hRH hlt (Cvs.Route.Visibility.CaseFiniteCellFloorRates.psiRate_of_extRate hσ
      (Cvs.Route.Visibility.CaseFiniteCellFloorRates.extRate_of_floorSum hσ hδ hμ hμ0 hμs) hT) one_pos
  · rcases Cvs.Route.Visibility.VisibilityLandauBandCarlson.winInput with ⟨ν, hν, hWR⟩ | ⟨η', hη', hWT⟩
    · exact Cvs.Route.Visibility.WindowBesselDiscBound.m1PrimeHalf_of_winLogReg hWR hν heq
    · exact Cvs.Route.Visibility.WindowBesselDiscBound.m1PrimeHalf_of_winLogReg
        (Cvs.Route.Visibility.WindowLogEnergyCellFloor.winLogReg_of_profile hη₀ hδ (Cvs.Route.Visibility.VisibilityFromCarlsonAlone.extTunnelSum hη') hWT) one_pos heq

/-- **Case ∞ (`NoTop`) joint rates hold unconditionally**: under `Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop`, some off-line zero `σ` and deep
family `D` satisfy `FreeShare`, `ExtPairingRate`, `AngleBound` and `ShallowRate` with `η < r`. -/
theorem jointRates_of_noTop :
    Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop → ∃ σ : nonTrivialZeroSet, Cvs.GaussKernel.del σ ≠ 0 ∧
      ∃ (D : ℕ → Finset nonTrivialZeroSet) (r η : ℝ) (K : ℕ → ℝ), η < r ∧ Cvs.StepA.Edge.DeepJointShare.FreeShare σ D r
        ∧ Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate {σ} |Cvs.GaussKernel.del σ| K ∧ Cvs.StepA.Edge.DeepJointShare.AngleBound D η ∧ Cvs.StepA.Edge.DeepJointShare.ShallowRate σ D :=
  fun hN => Cvs.StepA.Edge.CaseInfinityJointRates.jointRates_of_caseInf one_pos sepData_one (m1Prime_one_of_not_rh hN.1)
    Cvs.StepA.Edge.DbarTransplantHolds.dbarTransplant Cvs.StepA.Edge.FreeInterpHolds.freeInterp lemmaC hN

/-- **Case ∞ (`NoTop`) closes unconditionally**: under `Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop`, the zero even bulk floor fails at all large
`x`. -/
theorem hV_of_noTop (hN : Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop) : ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  Cvs.Route.Visibility.EvenBulkFloorFailsOffRh.eventually_not_evenBulkFloor_of_jointRates (jointRates_of_noTop hN)

/-! ### Unconditional `hV` and `RiemannHypothesis` reductions -/

/-- **`hV` holds unconditionally**: off `RiemannHypothesis`, the zero even bulk floor fails at all large `x`. -/
theorem hV : ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  Cvs.Route.Visibility.VisibilityFromCarlsonAlone.hV_of_lemmaC lemmaC

/-- **`hV` in `Cvs.WeilForm.EvenBulkVisibility`'s visibility form holds unconditionally**: off `RiemannHypothesis`, at all large `x` some even
`b` and minorant `M` have `Qx ≤ M − 4⟪·, b⟫²` on the even subspace and `M(b − P_{R₁}b) < 4‖b − P_{R₁}b‖⁴`. -/
theorem hV_visible :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Cvs.Route.L1FloorFromBulkD0.Dom x → ℝ) (b : Cvs.Route.L1FloorFromBulkD0.Dom x), b ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x ∧
      (∀ u ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, Cvs.Route.WindowPositivityBulkCoupling.Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b) < 4 * ‖b - (Cvs.L2a.EvenSectorReflectionBound.R1 x).starProjection b‖ ^ 4 :=
  Cvs.Route.Visibility.VisibilityFromCarlsonAlone.hV_visible_of_lemmaC lemmaC

/-- **`RiemannHypothesis` from the eventual even bulk floor alone**. -/
theorem rh_of_evenBulkFloor (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) : RiemannHypothesis :=
  Cvs.Route.Visibility.VisibilityFromCarlsonAlone.rh_of_evenBulkFloor_lemmaC hF lemmaC

/-- **`RiemannHypothesis` via `Cvs.WeilForm.EvenBulkVisibility`** from the eventual even bulk floor alone. -/
theorem rh_of_visible (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) : RiemannHypothesis :=
  Cvs.WeilForm.EvenBulkVisibility.rh_of_eventually_evenBulkFloor_of_visible hV_visible hF

/-! ### Exact closed-form identities, explicit exponents, and structural equivalences -/

/-- **Exact closed-form `(1 - λ_t)` cancellation on the top prolate rung**: for `80 ≤ 2πx`,
`2(1 - λ_t) a_t = 4 / (λ_t (1 + √λ_t)³)`. -/
theorem two_mul_one_sub_mul_aTop_eq {x : ℕ} (hx : 80 ≤ 2 * Real.pi * x) :
    2 * (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Prolate.Gram.CentralResolventTrace.aTop x
      = 4 / (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x * (1 + √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x)) ^ 3) := by
  have hl1 : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x < 1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have h1l : 1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x ≠ 0 := by linarith [hl1]
  unfold Cvs.Prolate.Gram.CentralResolventTrace.aTop
  change 2 * (1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x)
    * (2 / ((1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x) * Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x * (1 + √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x)) ^ 3)) = _
  field_simp
  ring

/-- **Exact closed-form zero-density exponent**: for `σ ∈ (1/2, 1)`,
`N(σ, T) = O_σ(T^{1 - (σ - 1/2)² / 16})` as `T → ∞`. -/
theorem N_zero_isBigO_rpow {σ : ℝ} (hσ_lo : 1 / 2 < σ) (hσ_hi : σ < 1) :
    (fun T : ℝ => (Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.N_zero σ T : ℝ))
      =O[atTop] (fun T : ℝ => T ^ (1 - (σ - 1 / 2) ^ 2 / 16)) := by
  set θ : ℝ := 1 - ((σ - 1 / 2) / 2) ^ 2 / 4
  have hθ_eq : θ = 1 - (σ - 1 / 2) ^ 2 / 16 := by dsimp only [θ]; ring
  have hθ0 : 0 < θ := by rw [hθ_eq]; nlinarith [hσ_lo, hσ_hi]
  have hθ1 : θ < 1 := by rw [hθ_eq]; nlinarith [sq_pos_of_pos (sub_pos.mpr hσ_lo)]
  obtain ⟨C_d, T_d, hCd0, hTd32, hdyad⟩ := Cvs.Zeta.ZeroCounting.SublinearZeroDensity.dyadicUpperBox_ncard_le hσ_lo hσ_hi
  obtain ⟨C_u, _, hup⟩ := Cvs.Zeta.ZeroCounting.SublinearZeroDensity.upperCount_le_of_dyadic (by linarith [hσ_lo]) hθ0 hθ1 hCd0
    (by linarith [hTd32] : 1 ≤ T_d) hdyad
  rw [← hθ_eq]
  refine IsBigO.of_bound (2 * C_u) ?_
  filter_upwards [eventually_ge_atTop T_d] with T hT
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) (hTd32.trans hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hT0.le _)]
  have h2 : (Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.N_zero σ T : ℝ) ≤ 2 * (Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.upperCount σ T : ℝ) := by
    exact_mod_cast Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.N_zero_le_two_mul_upperCount (by linarith [hσ_lo]) T
  calc (Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.N_zero σ T : ℝ) ≤ 2 * (Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf.upperCount σ T : ℝ) := h2
    _ ≤ 2 * (C_u * T ^ θ) := mul_le_mul_of_nonneg_left (hup hT) (by norm_num)
    _ = (2 * C_u) * T ^ θ := by ring

/-- **Exact closed-form deep-set zero bound**: for `0 < δ_D < 1/2`, `#deepSet δ_D T ≤ C · T^{1 - δ_D² / 16}` for
all `T ≥ T₀`. -/
theorem deepSet_card_le_explicit {δD : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ((deepSet δD T).card : ℝ) ≤ C * T ^ (1 - δD ^ 2 / 16) := by
  have hO := N_zero_isBigO_rpow (σ := 1 / 2 + δD) (by linarith [hδ]) (by linarith [hδ'])
  have hexp : 1 - (1 / 2 + δD - 1 / 2) ^ 2 / 16 = 1 - δD ^ 2 / 16 := by ring
  rw [hexp] at hO
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hc
  refine ⟨4 * max c 0, max T₁ 1, by positivity, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith [le_max_right T₁ 1, hT]
  have h1 := hT₁ T ((le_max_left T₁ 1).trans hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hT0 _)] at h1
  have h2 : ((deepSet δD T).card : ℝ) ≤ 4 * (Cvs.GaussKernel.carlsonCount (1 / 2 + δD) T : ℝ) := by
    rw [Cvs.StepA.Edge.DeepZerosAboveCutoff.deepSet_eq_offLineWindow]
    exact_mod_cast Cvs.GaussKernel.offLineCount_le_four_mul_carlsonCount hδ T
  have h3 : (Cvs.GaussKernel.carlsonCount (1 / 2 + δD) T : ℝ)
      ≤ Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.N_zero (1 / 2 + δD) T := by
    exact_mod_cast Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.carlsonCount_le_N_zero (by linarith [hδ]) hT0
  have h4 : c * T ^ (1 - δD ^ 2 / 16) ≤ max c 0 * T ^ (1 - δD ^ 2 / 16) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hT0 _)
  linarith

/-- **`Cvs.Zeta.GaussKernel.AdmissibleKernel.WindowRecordStalls` holds unconditionally** via `Cvs.Zeta.ZeroCounting.SublinearZeroDensity.zeroDensity`. -/
theorem windowRecordStalls : Cvs.Zeta.GaussKernel.AdmissibleKernel.WindowRecordStalls :=
  Cvs.Zeta.GaussKernel.AdmissibleKernel.windowRecordStalls_of_zeroDensity Cvs.Zeta.ZeroCounting.SublinearZeroDensity.zeroDensity

/-- **Asymptotic zero-one dichotomy for `EvenBulkFloor x 0`**: it either holds at every `x ≥ 2`
or fails at all sufficiently large `x`. -/
theorem forall_evenBulkFloor_or_eventually_not :
    (∀ x : ℕ, 2 ≤ x → Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) ∨ (∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl fun _ hx => (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx).2.1
  · exact Or.inr (hV hRH)

/-- **`RiemannHypothesis` from the even bulk floor along any infinite subsequence** (`∃ᶠ` replaces `∀ᶠ`,
and neither `EvenRungPos` nor `EvenFormCoupling` is needed). -/
theorem rh_of_frequently_evenBulkFloor
    (hF : ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) : RiemannHypothesis := by
  by_contra hRH
  exact hF (hV hRH)

/-- **`RiemannHypothesis` ↔ `EvenBulkFloor x 0` for all `x ≥ 2`**. -/
theorem rh_iff_forall_evenBulkFloor :
    RiemannHypothesis ↔ ∀ x : ℕ, 2 ≤ x → Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  ⟨fun hRH _ hx => (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx).2.1,
    fun h => rh_of_evenBulkFloor ((eventually_ge_atTop 2).mono h)⟩

/-- **`RiemannHypothesis` ↔ `EvenBulkFloor x 0` eventually as `x → ∞`**. -/
theorem rh_iff_eventually_evenBulkFloor :
    RiemannHypothesis ↔ ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  ⟨fun hRH => (eventually_ge_atTop 2).mono fun _ hx =>
    (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx).2.1, rh_of_evenBulkFloor⟩

/-- **`RiemannHypothesis` ↔ `EvenBulkFloor x 0` at infinitely many `x`**. -/
theorem rh_iff_frequently_evenBulkFloor :
    RiemannHypothesis ↔ ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  ⟨fun hRH => ((eventually_ge_atTop 2).mono fun _ hx =>
    (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx).2.1).frequently, rh_of_frequently_evenBulkFloor⟩

/-- **Scale zero-one collapse**: `EvenBulkFloor x 0` holds for all large `x` iff it holds for infinitely
many `x`. -/
theorem eventually_evenBulkFloor_iff_frequently :
    (∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) ↔ (∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) :=
  rh_iff_eventually_evenBulkFloor.symm.trans rh_iff_frequently_evenBulkFloor

/-- **Single-vector spine reduction under coupling**: `EvenFormCoupling x δ` (`δ < 1`) and a single
`r₀ ∈ R₁(x)` with `Qx x r₀ > 0` at infinitely many `x` imply `RiemannHypothesis`. -/
theorem rh_of_frequently_coupling_exists_pos_R1
    (h : ∃ᶠ x : ℕ in atTop, ∃ δ : ℝ, δ < 1 ∧ Cvs.Route.EvenWindowBulkCoupling.EvenFormCoupling x δ ∧
      ∃ r₀ ∈ Cvs.L2a.EvenSectorReflectionBound.R1 x, 0 < Cvs.Route.WindowPositivityBulkCoupling.Qx x r₀) :
    RiemannHypothesis :=
  rh_of_frequently_evenBulkFloor
    (h.mono fun _ ⟨_, hδ, hC, hr⟩ => Cvs.Route.EvenWindowBulkCoupling.evenBulkFloor_zero_of_coupling hδ hC hr)

end Cvs.Route.Visibility.VisibilityUnconditional

end
