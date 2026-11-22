import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.DeepZerosAboveCutoff
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FreeInterpHolds
import Cvs.StepA.Edge.GapRectangleBlaschke
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.GappedCutoffPairMass
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
# `LemmaC` from Carlson's density theorem, and route SEP without the Case ∞ interpolation inputs

With `H₀ = x^{ε₂}`, Lemma P (Cvs.Zeta.ZeroCounting.GappedCutoffPairMass) picks a gapped cutoff in `[H₀, 2H₀]`; Carlson bounds the deep count by
`C(4H₀)^{1 − 2δ_D²}`, so the pair mass is `x^{−2δ_D²ε₂}` times a polylog, and Cvs.StepA.Edge.DeepZerosAboveCutoff gives `CaseInfinityJointRates`'s `LemmaC` with
`α = 2(bexp + 1) + 1`, `κ = δ_D²`. With Cvs.StepA.Edge.DbarTransplantHolds and Cvs.StepA.Edge.FreeInterpHolds, route SEP's RH theorem holds with `CarlsonBound` in
place of `DbarTransplant`, `FreeInterp` and `LemmaC`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (bexp)
open Cvs.StepA.Edge.GapRectangleBlaschke (phi Gap kcg qg)
open Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff (phiNear Above)
open Cvs.Zeta.ZeroCounting.GappedCutoffPairMass (nJ)

namespace Cvs.StepA.Edge.LemmaCFromCarlson
open Cvs.ZeroCounting

/-- The gap rectangle's constants are below the transplant rectangle's. -/
theorem kcg_le_kc (δD H : ℝ) (hδ : 0 < δD) (hH : 0 ≤ H) : kcg δD H ≤ Cvs.StepA.Edge.DbarTransplantHolds.kc δD H := by
  unfold kcg Cvs.StepA.Edge.DbarTransplantHolds.kc
  rw [Cvs.StepA.Edge.GapRectangleBlaschke.zg_re, Cvs.StepA.Edge.GapRectangleBlaschke.zg_im, Cvs.StepA.Edge.GapRectangleBlaschke.wg_re, Cvs.StepA.Edge.GapRectangleBlaschke.wg_im, Cvs.StepA.Edge.DbarTransplantHolds.zc_re, Cvs.StepA.Edge.DbarTransplantHolds.zc_im, Cvs.StepA.Edge.DbarTransplantHolds.wc_re, Cvs.StepA.Edge.DbarTransplantHolds.wc_im]
  have hpi := Real.pi_pos
  have hs : 0 < √(2 * (δD / 4)) := Real.sqrt_pos.2 (by positivity)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem qg_le_qq (x : ℕ) (δD H : ℝ) (hδ : 0 < δD) (hH : 0 ≤ H) : qg x δD H ≤ Cvs.StepA.Edge.DbarTransplantHolds.qq x δD H := by
  unfold qg Cvs.StepA.Edge.DbarTransplantHolds.qq
  rw [Cvs.StepA.Edge.GapRectangleBlaschke.zg_re, Cvs.StepA.Edge.DbarTransplantHolds.zc_re]
  exact mul_le_mul_of_nonneg_right (kcg_le_kc δD H hδ hH) (by positivity)

/-- `log(a x^{ε} + b)` is subpolynomial and eventually nonnegative, `a, b ≥ 0`, `a + b ≥ 1`, `ε > 0`. -/
theorem subPoly_log_rpow {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 1 ≤ a + b) (hε : 0 < ε) :
    Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly (fun x : ℕ => Real.log (a * (x : ℝ) ^ ε + b))
      ∧ ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log (a * (x : ℝ) ^ ε + b) := by
  have hg : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => Real.log (a + b) + ε * Real.log x :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add (Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log
      ((eventually_ge_atTop 1).mono fun x hx => Real.log_nonneg (by exact_mod_cast hx)) hε.le)
  have hpt : ∀ᶠ x : ℕ in atTop, 1 ≤ a * (x : ℝ) ^ ε + b ∧
      Real.log (a * (x : ℝ) ^ ε + b) ≤ Real.log (a + b) + ε * Real.log x := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hX : 1 ≤ (x : ℝ) ^ ε := Real.one_le_rpow hx1 hε.le
    have h1 : 1 ≤ a * (x : ℝ) ^ ε + b := by nlinarith
    refine ⟨h1, ?_⟩
    have h2 : a * (x : ℝ) ^ ε + b ≤ (a + b) * (x : ℝ) ^ ε := by nlinarith
    calc Real.log (a * (x : ℝ) ^ ε + b) ≤ Real.log ((a + b) * (x : ℝ) ^ ε) :=
          Real.log_le_log (by linarith) h2
      _ = Real.log (a + b) + ε * Real.log x := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow (by linarith)]
  exact ⟨hg.mono (hpt.mono fun _ h => h.2), hpt.mono fun _ h => Real.log_nonneg h.1⟩

/-- `(4X)^θ = 4^θ X·X^{θ − 1}` with `X^{θ − 1} = x^{ε(θ − 1)}` for `X = x^ε`, `x > 0`. -/
theorem four_mul_rpow {x : ℕ} (hx : (0 : ℝ) < x) (ε θ : ℝ) :
    (4 * (x : ℝ) ^ ε) ^ θ = 4 ^ θ * ((x : ℝ) ^ ε * (x : ℝ) ^ (ε * (θ - 1))) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 2; ring

/-- **The cutoff conditions hold eventually**: `X = x^{ε₂} ≥ 12`, `4X ≥ T₀` and `12C·4^θx^{−2δ_D²ε₂} ≤ 1`. -/
theorem eventually_big {ε₂ δD C T₀ : ℝ} (hε₂ : 0 < ε₂) (hδ : 0 < δD) :
    ∀ᶠ x : ℕ in atTop, 1 ≤ x ∧ 12 ≤ (x : ℝ) ^ ε₂ ∧ T₀ ≤ 4 * (x : ℝ) ^ ε₂
      ∧ 12 * C * 4 ^ (1 - 2 * δD ^ 2) * (x : ℝ) ^ (ε₂ * ((1 - 2 * δD ^ 2) - 1)) ≤ 1 := by
  have h1 := Cvs.Route.Visibility.ExtPairingRatesSubpoly.tendsto_natCast_rpow hε₂
  have h2 : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε₂ * ((1 - 2 * δD ^ 2) - 1))) atTop (𝓝 0) := by
    have : ε₂ * ((1 - 2 * δD ^ 2) - 1) = -(2 * δD ^ 2 * ε₂) := by ring
    rw [this]
    exact (tendsto_rpow_neg_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have h3 := h2.const_mul (12 * C * 4 ^ (1 - 2 * δD ^ 2))
  rw [mul_zero] at h3
  filter_upwards [eventually_ge_atTop 1, h1.eventually_ge_atTop 12, h1.eventually_ge_atTop (T₀ / 4),
    h3.eventually (ge_mem_nhds one_pos)] with x hx a1 a2 a3
  exact ⟨hx, a1, by linarith, a3⟩

/-- The candidate count: `X ≥ 12` and `12N ≤ X` give `2N ≤ J`, `J ≥ 1` and `J ≥ X/6`. -/
theorem nJ_facts {X : ℝ} (hX : 12 ≤ X) {N : ℕ} (hN : 12 * (N : ℝ) ≤ X) :
    2 * N ≤ nJ X ∧ 1 ≤ nJ X ∧ X / 6 ≤ nJ X := by
  have h := Nat.lt_floor_add_one ((X - 1) / 3)
  have hJ : X / 6 ≤ (nJ X : ℝ) := by unfold nJ; linarith
  refine ⟨?_, ?_, hJ⟩
  · have : (2 * N : ℝ) < nJ X + 1 := by linarith
    have : 2 * N < nJ X + 1 := by exact_mod_cast this
    omega
  · have : (1 : ℝ) < nJ X + 1 := by linarith
    have : 1 < nJ X + 1 := by exact_mod_cast this
    omega

/-- Lemma P's bound `B(Y) = 264 log(8Y + 5)(1 + log(4Y + 1))`. -/
def bP (Y : ℝ) : ℝ := 264 * Real.log (8 * Y + 5) * (1 + Real.log (4 * Y + 1))

/-- A Lemma-P cutoff at `x`: `H ∈ [X, 2X]`, gapped, with near pair mass at most `2N(4X)B(X)/J`, `X = x^{ε₂}`. -/
def GoodCut (δD ε₂ : ℝ) (x : ℕ) (H : ℝ) : Prop :=
  (x : ℝ) ^ ε₂ ≤ H ∧ H ≤ 2 * (x : ℝ) ^ ε₂ ∧ Gap δD H
    ∧ phiNear δD H (4 * (x : ℝ) ^ ε₂)
      ≤ 2 * (deepSet δD (4 * (x : ℝ) ^ ε₂)).card * bP ((x : ℝ) ^ ε₂) / nJ ((x : ℝ) ^ ε₂)

open Classical in
/-- The chosen cutoff: a Lemma-P cutoff where one exists, else `x^{ε₂}`. -/
def cutH (δD ε₂ : ℝ) (x : ℕ) : ℝ :=
  if h : ∃ H, GoodCut δD ε₂ x H then h.choose else (x : ℝ) ^ ε₂

theorem goodCut_cutH {δD ε₂ : ℝ} {x : ℕ} (h : ∃ H, GoodCut δD ε₂ x H) : GoodCut δD ε₂ x (cutH δD ε₂ x) := by
  unfold cutH; rw [dif_pos h]; exact h.choose_spec

/-- The polylog factor of the pair mass, `Q₁ = C4^θ(12B(X) + 16 log(16X))`. -/
def q1 (C θ ε₂ : ℝ) (x : ℕ) : ℝ :=
  C * 4 ^ θ * (12 * bP ((x : ℝ) ^ ε₂) + 16 * Real.log (16 * (x : ℝ) ^ ε₂))

theorem subPoly_q1 {C θ ε₂ : ℝ} (hC : 0 ≤ C) (hε₂ : 0 < ε₂) :
    Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly (q1 C θ ε₂) ∧ ∀ᶠ x : ℕ in atTop, 0 ≤ q1 C θ ε₂ x := by
  obtain ⟨s1, n1⟩ := subPoly_log_rpow (a := 8) (b := 5) (by norm_num) (by norm_num) (by norm_num) hε₂
  obtain ⟨s2, n2⟩ := subPoly_log_rpow (a := 4) (b := 1) (by norm_num) (by norm_num) (by norm_num) hε₂
  obtain ⟨s3, n3⟩ := subPoly_log_rpow (a := 16) (b := 0) (by norm_num) (by norm_num) (by norm_num) hε₂
  simp only [add_zero] at s3 n3
  have s2' : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => 1 + Real.log (4 * (x : ℝ) ^ ε₂ + 1) := (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 1).add s2
  have n2' : ∀ᶠ x : ℕ in atTop, 0 ≤ 1 + Real.log (4 * (x : ℝ) ^ ε₂ + 1) := n2.mono fun _ h => by linarith
  have sB : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => bP ((x : ℝ) ^ ε₂) := by
    have := Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul (s1.mul s2' n1 n2') (n1.and n2' |>.mono fun _ h => mul_nonneg h.1 h.2)
      (by norm_num : (0 : ℝ) ≤ 264)
    refine this.mono (Eventually.of_forall fun x => le_of_eq ?_)
    unfold bP; ring
  have nB : ∀ᶠ x : ℕ in atTop, 0 ≤ bP ((x : ℝ) ^ ε₂) :=
    (n1.and n2').mono fun _ h => by unfold bP; exact mul_nonneg (mul_nonneg (by norm_num) h.1) h.2
  have s4 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => 12 * bP ((x : ℝ) ^ ε₂) + 16 * Real.log (16 * (x : ℝ) ^ ε₂) :=
    (Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul sB nB (by norm_num)).add (Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul s3 n3 (by norm_num))
  have n4 : ∀ᶠ x : ℕ in atTop, 0 ≤ 12 * bP ((x : ℝ) ^ ε₂) + 16 * Real.log (16 * (x : ℝ) ^ ε₂) :=
    (nB.and n3).mono fun _ h => by nlinarith [h.1, h.2]
  refine ⟨(Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul s4 n4 (c := C * 4 ^ θ) (by positivity)).mono
    (Eventually.of_forall fun x => le_of_eq ?_), ?_⟩
  · unfold q1; ring
  · exact n4.mono fun _ h => by unfold q1; positivity

theorem deepSet_mono {δD H H' : ℝ} (h : H ≤ H') : deepSet δD H ⊆ deepSet δD H' := fun ρ hρ => by
  rw [mem_deepSet] at hρ ⊢; exact ⟨hρ.1.trans h, hρ.2⟩

/-- **The pair mass at a Lemma-P cutoff**: `phiNear + 4#D·tailBound(4X) ≤ Q₁(x)x^{ε₂(θ − 1)}`. -/
theorem pairMass_le {δD ε₂ C θ : ℝ} {x : ℕ} (hx : 1 ≤ x) (hX : 12 ≤ (x : ℝ) ^ ε₂)
    (hcount : ((deepSet δD (4 * (x : ℝ) ^ ε₂)).card : ℝ) ≤ C * (4 * (x : ℝ) ^ ε₂) ^ θ)
    (hsmall : 12 * ((deepSet δD (4 * (x : ℝ) ^ ε₂)).card : ℝ) ≤ (x : ℝ) ^ ε₂) {H : ℝ}
    (hH : GoodCut δD ε₂ x H) :
    phiNear δD H (4 * (x : ℝ) ^ ε₂) + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * (x : ℝ) ^ ε₂)
      ≤ q1 C θ ε₂ x * (x : ℝ) ^ (ε₂ * (θ - 1)) := by
  set X := (x : ℝ) ^ ε₂ with hXdef
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  set N := (deepSet δD (4 * X)).card
  obtain ⟨_, _, hJ⟩ := nJ_facts hX hsmall
  obtain ⟨hH1, hH2, _, hP⟩ := hH
  have hX0 : 0 < X := by linarith
  have hbP : 0 ≤ bP X := by
    unfold bP
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 * X + 1 by linarith)])
  have hl16 : 0 ≤ Real.log (16 * X) := Real.log_nonneg (by linarith)
  have hJ0 : (0 : ℝ) < nJ X := by linarith
  have h1 : phiNear δD H (4 * X) ≤ 12 * N * bP X / X := by
    refine hP.trans ?_
    rw [div_le_div_iff₀ hJ0 hX0]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [mul_nonneg hN0 hbP]
  have hNH : ((deepSet δD H).card : ℝ) ≤ N := by
    exact_mod_cast Finset.card_le_card (deepSet_mono (by linarith))
  have h2 : 4 * ((deepSet δD H).card : ℝ) * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * X) ≤ 16 * N * Real.log (16 * X) / X := by
    unfold Cvs.Zeta.ZeroTailInverseSquare.tailBound
    rw [show 4 * (4 * X) = 16 * X by ring]
    have : 4 * ((deepSet δD H).card : ℝ) * (16 * Real.log (16 * X) / (4 * X)) = 16 * (deepSet δD H).card
        * Real.log (16 * X) / X := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNH (by norm_num)) hl16) hX0.le
  have h3 : (N : ℝ) / X ≤ C * 4 ^ θ * (x : ℝ) ^ (ε₂ * (θ - 1)) := by
    rw [div_le_iff₀ hX0]
    have := four_mul_rpow hx0 ε₂ θ
    rw [← hXdef] at this
    rw [this] at hcount
    linarith
  calc phiNear δD H (4 * X) + 4 * ((deepSet δD H).card : ℝ) * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * X)
      ≤ 12 * N * bP X / X + 16 * N * Real.log (16 * X) / X := add_le_add h1 h2
    _ = (N / X) * (12 * bP X + 16 * Real.log (16 * X)) := by field_simp
    _ ≤ (C * 4 ^ θ * (x : ℝ) ^ (ε₂ * (θ - 1))) * (12 * bP X + 16 * Real.log (16 * X)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = q1 C θ ε₂ x * (x : ℝ) ^ (ε₂ * (θ - 1)) := by unfold q1; ring

/-- The constant of `K_c`'s growth, `C₀ = 24·17^{bexp}/(2π(δ_D/2)^{1/2})`. -/
def c0 (δD : ℝ) : ℝ := 24 * 17 ^ bexp / (2 * Real.pi * √(δD / 2))

/-- Lemma C's subpolynomial factor `Q = 16((3/δ_D)Q₁ + 4C₀²(528 log(4X + 5) + 4Z))`. -/
def qC (δD C θ ε₂ : ℝ) (x : ℕ) : ℝ :=
  16 * (3 / δD * q1 C θ ε₂ x + 4 * c0 δD ^ 2 * (528 * Real.log (4 * (x : ℝ) ^ ε₂ + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum))

theorem invSqSum_nonneg : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.invSqSum :=
  tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by positivity)

theorem subPoly_qC {δD C θ ε₂ : ℝ} (hδ : 0 < δD) (hC : 0 ≤ C) (hε₂ : 0 < ε₂) : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly (qC δD C θ ε₂) := by
  obtain ⟨s1, n1⟩ := subPoly_q1 (θ := θ) hC hε₂
  obtain ⟨s2, n2⟩ := subPoly_log_rpow (a := 4) (b := 5) (by norm_num) (by norm_num) (by norm_num) hε₂
  have hZ := invSqSum_nonneg
  have sA := Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul s1 n1 (c := 3 / δD) (by positivity)
  have sB : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => 528 * Real.log (4 * (x : ℝ) ^ ε₂ + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum :=
    (Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul s2 n2 (by norm_num)).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _)
  have nB : ∀ᶠ x : ℕ in atTop, 0 ≤ 528 * Real.log (4 * (x : ℝ) ^ ε₂ + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum :=
    n2.mono fun _ h => by positivity
  have sC := Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul sB nB (c := 4 * c0 δD ^ 2) (by positivity)
  have nA : ∀ᶠ x : ℕ in atTop, 0 ≤ 3 / δD * q1 C θ ε₂ x := n1.mono fun _ h => by positivity
  have nC : ∀ᶠ x : ℕ in atTop, 0 ≤ 4 * c0 δD ^ 2 * (528 * Real.log (4 * (x : ℝ) ^ ε₂ + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum) :=
    nB.mono fun _ h => by positivity
  refine (Cvs.StepA.Edge.CaseInfinityJointRates.subPoly_const_mul (sA.add sC) (nA.and nC |>.mono fun _ h => add_nonneg h.1 h.2) (c := 16)
    (by norm_num)).mono (Eventually.of_forall fun x => le_of_eq ?_)
  unfold qC; ring

set_option maxHeartbeats 4000000 in
/-- **`LemmaC` holds given Carlson's density theorem** (caseinf-W Lemma P and Theorem C), with
`α = 2(bexp + 1) + 1` and `κ = δ_D²`. -/
theorem lemmaC_of_carlson (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) : Cvs.StepA.Edge.CaseInfinityJointRates.LemmaC := by
  refine ⟨2 * ((bexp : ℝ) + 1) + 1, by positivity, fun δD hδ hδ' => ⟨δD ^ 2, by positivity,
    fun ε₂ hε₂ hαε => ?_⟩⟩
  obtain ⟨Cc, T₀, hCc, hcount⟩ := Cvs.StepA.Edge.DeepZerosAboveCutoff.deepSet_card_le_of_carlson hCarl hδ hδ'
  set θ := 1 - 2 * δD ^ 2 with hθ
  have hbig := eventually_big (C := Cc) (T₀ := T₀) hε₂ hδ
  -- the count at a large `x`
  have hcnt : ∀ x : ℕ, 1 ≤ x → 12 ≤ (x : ℝ) ^ ε₂ → T₀ ≤ 4 * (x : ℝ) ^ ε₂ →
      12 * Cc * 4 ^ θ * (x : ℝ) ^ (ε₂ * (θ - 1)) ≤ 1 →
      ((deepSet δD (4 * (x : ℝ) ^ ε₂)).card : ℝ) ≤ Cc * (4 * (x : ℝ) ^ ε₂) ^ θ
        ∧ 12 * ((deepSet δD (4 * (x : ℝ) ^ ε₂)).card : ℝ) ≤ (x : ℝ) ^ ε₂ := by
    intro x hx hX hT hs
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    have hc := hcount _ hT
    refine ⟨hc, ?_⟩
    rw [four_mul_rpow hx0] at hc
    have hX0 : 0 ≤ (x : ℝ) ^ ε₂ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs hX0]
  have hex : ∀ᶠ x : ℕ in atTop, ∃ H, GoodCut δD ε₂ x H := by
    filter_upwards [hbig] with x hxb
    obtain ⟨hx, hX, hT, hs⟩ := hxb
    obtain ⟨_, hsmall⟩ := hcnt x hx hX hT hs
    obtain ⟨h2N, hJ1, _⟩ := nJ_facts hX hsmall
    exact Cvs.Zeta.ZeroCounting.GappedCutoffPairMass.lemmaP (by linarith) hJ1 h2N
  have hcut : Cvs.StepA.Edge.CaseInfinityJointRates.Cutoff ε₂ (cutH δD ε₂) :=
    hex.mono fun x h => ⟨(goodCut_cutH h).1, (goodCut_cutH h).2.1⟩
  refine ⟨cutH δD ε₂, hcut, qC δD Cc θ ε₂, subPoly_qC hδ hCc hε₂, ?_⟩
  have hαε' : ((bexp : ℝ) + 1) * ε₂ < δD / 8 := by nlinarith
  have hq := Cvs.StepA.Edge.FreeInterpHolds.eventually_good hδ hδ' hε₂ hαε' hcut 0
  have hm : 0 < 2 * δD ^ 2 * ε₂ := by positivity
  have hq1 := Cvs.Route.Visibility.ExtPairingRatesSubpoly.eventually_mul_rpow_le (subPoly_q1 (θ := θ) hCc hε₂).1 hm 0 one_pos
  filter_upwards [hbig, hex, hq, hq1, (subPoly_q1 (θ := θ) hCc hε₂).2] with x hxb hgood hqx hq1x hq1n
  intro hx0
  obtain ⟨hx, hX, hT, hs⟩ := hxb
  obtain ⟨_, _, _, hqq, _⟩ := hqx
  set X := (x : ℝ) ^ ε₂ with hXdef
  set H := cutH δD ε₂ x with hHdef
  have hG := goodCut_cutH hgood
  obtain ⟨hc, hsmall⟩ := hcnt x hx hX hT hs
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hexp : ε₂ * (θ - 1) = 0 - 2 * δD ^ 2 * ε₂ := by rw [hθ]; ring
  have hPm := pairMass_le hx hX hc hsmall hG
  rw [hexp] at hPm
  rw [Real.rpow_zero, mul_one] at hq1x
  have hP1 := hPm.trans hq1x
  have hqg : qg x δD H ≤ 1 / 2 := (qg_le_qq x δD H hδ (by linarith [hG.1])).trans hqq
  obtain ⟨hH1, hH2, hgap, _⟩ := hG
  have hsum := Cvs.StepA.Edge.DeepZerosAboveCutoff.sum_above_proj_le hx0 hδ hδ' (by linarith) hgap hqg (M := 4 * X) (by linarith)
    (by have := Real.exp_one_lt_d9; linarith) hP1
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  -- the final arithmetic
  set y := (x : ℝ) ^ (-(δD ^ 2 * ε₂)) with hy
  have hy0 : 0 ≤ y := by positivity
  have hP2 : phiNear δD H (4 * X) + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * X) ≤ q1 Cc θ ε₂ x * y := by
    refine hPm.trans (mul_le_mul_of_nonneg_left ?_ hq1n)
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have hkc := Cvs.StepA.Edge.DbarTransplantHolds.kc_le hδ hδ' (by linarith : (1 : ℝ) ≤ X) hH1 hH2
  have hkcg := (kcg_le_kc δD H hδ (by linarith)).trans hkc
  have hkcg0 : 0 ≤ kcg δD H := by
    unfold kcg; rw [Cvs.StepA.Edge.GapRectangleBlaschke.zg_re, Cvs.StepA.Edge.GapRectangleBlaschke.zg_im, Cvs.StepA.Edge.GapRectangleBlaschke.wg_re, Cvs.StepA.Edge.GapRectangleBlaschke.wg_im]
    refine div_nonneg (by nlinarith) ?_
    have := Real.pi_pos; have := Real.sqrt_nonneg (2 * (δD / 4)); positivity
  have hX2 : X ^ (bexp + 1) * X ^ (bexp + 1) * (x : ℝ) ^ (-(δD / 2)) ≤ y := by
    have hx0' : (0 : ℝ) < x := hx0
    rw [hXdef, ← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hx0'.le, ← Real.rpow_add hx0', hy]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    have hd : δD ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right hd hε₂.le
    linarith
  have hK2 : 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2)) ≤ 4 * c0 δD ^ 2 * y := by
    have h1 : kcg δD H ^ 2 ≤ (c0 δD * X ^ (bexp + 1)) ^ 2 := pow_le_pow_left₀ hkcg0 hkcg 2
    have h2 : (c0 δD * X ^ (bexp + 1)) ^ 2 * (x : ℝ) ^ (-(δD / 2))
        = c0 δD ^ 2 * (X ^ (bexp + 1) * X ^ (bexp + 1) * (x : ℝ) ^ (-(δD / 2))) := by ring
    have h3 : 0 ≤ (x : ℝ) ^ (-(δD / 2)) := by positivity
    have := mul_le_mul_of_nonneg_right h1 h3
    rw [h2] at this
    have h4 := mul_le_mul_of_nonneg_left hX2 (sq_nonneg (c0 δD))
    nlinarith
  have hlog : Real.log (2 * H + 5) ≤ Real.log (4 * X + 5) := Real.log_le_log (by linarith) (by linarith)
  have hZ := invSqSum_nonneg
  have hL : 0 ≤ 528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * H + 5 by linarith); positivity
  have hxT : (0 : ℝ) ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth := by positivity
  have hfin : (x : ℝ) ^ (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - δD ^ 2 * ε₂) = (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * y := by
    rw [hy, ← Real.rpow_add hx0]; ring_nf
  rw [hfin]
  calc 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * (phiNear δD H (4 * X) + 4 * (deepSet δD H).card
        * Cvs.Zeta.ZeroTailInverseSquare.tailBound (4 * X)) / δD + 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2))
        * (528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum))
      ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * (q1 Cc θ ε₂ x * y) / δD + 4 * c0 δD ^ 2 * y
        * (528 * Real.log (4 * X + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hxT
        · exact div_le_div_of_nonneg_right (by linarith) hδ.le
        · refine mul_le_mul hK2 (by linarith) hL (by positivity)
    _ = qC δD Cc θ ε₂ x * ((x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * y) := by unfold qC; ring

end Cvs.StepA.Edge.LemmaCFromCarlson

end
