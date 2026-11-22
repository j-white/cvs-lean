import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FiniteSpanRateHighMass
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.L1ConnesFactorPolynomial
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.LowRungHighSpectralMass
import Cvs.L2a.LowRungTruncationRate
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.QSideConnesEndpointUnits
import Cvs.L2a.QSideConnesRelative
import Cvs.L2a.QSideRungConstants
import Cvs.L2a.RungSpanProfilePowers
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1GapNonnegRH
import Cvs.Route.L1GapParametricRH
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes' relative q-bound is nonnegative

At `c = 2πx ≥ c₀^W` the pole term of `connesLrel` is at least `−2(P + N)` with `P ≤ 4M` (Cvs.Prolate.RungTailIntegralMass, Cvs.L2a.FullTailBilinearChannels), while
`Khigh(c) ≥ 4` and `archSymbol(2c) ≥ 2`; so `connesLrel x ≥ 0`, and frequent `L1GapL connesLrel` gives RH through Cvs.Route.L1GapNonnegRH.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.ConnesRelativeQBoundNonneg
open Cvs.ZeroCounting

open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)
open Cvs.Route.JointGapConnesFromL1 (one₁)
open Cvs.L2a.FullTailConvergence (fullTail)

/-- `Khigh(c) ≥ 4` for `c > 0`. -/
theorem four_le_Khigh {c : ℝ} (hc : 0 < c) : 4 ≤ Cvs.L2a.LowRungHighSpectralMass.Khigh c := by
  unfold Cvs.L2a.LowRungHighSpectralMass.Khigh
  have ha : (1 / 2 : ℝ) ≤ 2 ^ (-(3 / 4) : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) (show (-1 : ℝ) ≤ -(3 / 4) by norm_num)
    rwa [Real.rpow_neg_one, ← one_div] at h
  have hs := Real.sq_sqrt (show 0 ≤ 96 * exp 1 * c by positivity)
  have hs0 := Real.sqrt_nonneg (96 * exp 1 * c)
  have he := Real.add_one_le_exp (1 : ℝ)
  set X := 4 * (4 * (2 ^ (-(3 / 4) : ℝ) * √(96 * exp 1 * c)))
  have hX : 8 * √(96 * exp 1 * c) ≤ X := by simp only [X]; nlinarith
  have hX2 : 64 * (96 * exp 1 * c) ≤ (6 + X) ^ 2 := by nlinarith
  rw [le_div_iff₀ hc]
  have : 0 ≤ (74 : ℝ) ^ 2 * (48 * exp 1 / c) * 25 := by positivity
  nlinarith

/-- **Connes' relative q-bound is nonnegative** at every `x` with `c₀^W ≤ 2πx`. -/
theorem connesLrel_nonneg {x : ℕ} (hx : c0W ≤ 2 * π * x) : 0 ≤ Cvs.L2a.QSideConnesRelative.connesLrel x := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hc100 : 100 ≤ c := Cvs.L2a.QSideConnesRelative.hundred_le hx
  have hc0 : 0 < c := by linarith
  have hχ := fun i => (Cvs.L2a.QSideConnesEndpointUnits.connes_levels hx i).2
  set M := Cvs.L2a.QSideConnesRelative.connesM x with hMd
  set N := Cvs.L2a.QSideConnesRelative.connesN x with hNd
  set P := ∑ i, bOf c one₁ i ^ 2 * (∫ t in Ioi 1, psi c (rung c (kOf i)) t ^ 2) with hPd
  have hM0 : 0 ≤ M := by rw [hMd]; unfold Cvs.L2a.QSideConnesRelative.connesM; positivity
  have hN0 : 0 ≤ N := by
    rw [hNd]; unfold Cvs.L2a.QSideConnesRelative.connesN Cvs.L2a.L1WindowFromFloor.tailN
    exact setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hPM : P ≤ 4 * M := Cvs.L2a.QSideConnesEndpointUnits.tailMass_le _ H.hg H.hg₁ H.hg₂c H.hang hc100 H.hχ0 hχ
  -- the pole term from below
  have hdist : Function.Injective fun i : Option ({1} : Finset ℕ) => lev c (kOf i) := by
    intro i i' he
    simp only at he
    rcases i with _ | j <;> rcases i' with _ | j'
    · rfl
    · have hj : (j' : ℕ) = 1 := Finset.mem_singleton.mp j'.2
      have hk : kOf (some j') = 2 := by simp only [kOf, Option.elim, hj]
      have := lev_lt (Cvs.L2a.QSideConnesEndpointUnits.connes_levels hx (some j')).1 (show 0 < kOf (some j') by rw [hk]; norm_num)
      simp only [kOf, Option.elim] at he this ⊢; linarith
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      have hk : kOf (some j) = 2 := by simp only [kOf, Option.elim, hj]
      have := lev_lt (Cvs.L2a.QSideConnesEndpointUnits.connes_levels hx (some j)).1 (show 0 < kOf (some j) by rw [hk]; norm_num)
      simp only [kOf, Option.elim] at he this ⊢; linarith
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      have hj' : (j' : ℕ) = 1 := Finset.mem_singleton.mp j'.2
      exact congrArg some (Subtype.ext (by rw [hj, hj']))
  have hPi := Cvs.Prolate.RungTailIntegralMass.abs_piPlus_span_le (bOf c one₁) H.hg H.hg₁ H.hg₂c H.hang H.hc H.hχ0 H.hχc hdist
  have hcard : (Fintype.card (Option ({1} : Finset ℕ)) : ℝ) = 2 := by simp [Fintype.card_option]
  rw [hcard] at hPi
  have hπC := Cvs.L2a.QSideRungConstants.piConst_two_le hc100
  have hspan := Cvs.L2a.FullTailFloorLimit.span_eq (bOf c one₁) H.hg c
  have hF : |∫ θ in Ioi 1, fullTail (Cvs.L2a.QSideConnesRelative.connesPhi x) θ / θ| ≤ √N := by
    have h := Cvs.L2a.FullTailBilinearChannels.abs_integral_fullTail_div_le
      (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span (bOf c one₁) H.hg)
      (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span (bOf c one₁) H.hg₁)
      (Cvs.L2a.FullTailFloorLimit.continuousOn_span (bOf c one₁) H.hg₂c) hc0
    rw [← hspan] at h
    exact h
  have hpole : -(2 * (P + N)) ≤ 2 * Cvs.L2a.FullTailPoleChannel.piPlus (Cvs.L2a.QSideConnesRelative.connesPhi x)
      * (∫ θ in Ioi 1, fullTail (Cvs.L2a.QSideConnesRelative.connesPhi x) θ / θ) := by
    set A := Cvs.L2a.FullTailPoleChannel.piPlus (Cvs.L2a.QSideConnesRelative.connesPhi x)
    set B := ∫ θ in Ioi 1, fullTail (Cvs.L2a.QSideConnesRelative.connesPhi x) θ / θ
    have hA : |A| ≤ 2 * √P := hPi.trans (mul_le_mul_of_nonneg_right hπC (Real.sqrt_nonneg _))
    have hAB : -(2 * (|A| * |B|)) ≤ 2 * A * B := by
      have := neg_abs_le (A * B); rw [abs_mul] at this; linarith
    have h2 : |A| * |B| ≤ 2 * √P * √N := mul_le_mul hA hF (abs_nonneg _) (by positivity)
    have h3 : 2 * √P * √N ≤ P + N := by
      nlinarith [sq_nonneg (√P - √N), Real.sq_sqrt hP0, Real.sq_sqrt hN0]
    linarith
  -- the constants from below
  have ha : 2 ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c) + 114 / (2 * c) := by
    have h1 := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge (t := 2 * c) (by linarith)
    have h2 : 2 * c / 2 = c := by ring
    rw [h2] at h1
    have hl : Real.log 100 ≤ Real.log c := Real.log_le_log (by norm_num) hc100
    have hl100 : 4 < Real.log 100 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 2.7182818286 ^ 4 := by gcongr
        _ < 100 := by norm_num
    have hlp : Real.log π < 6 / 5 := by
      have he0 := Real.exp_pos 1
      have h := Real.log_le_sub_one_of_pos (div_pos Real.pi_pos he0)
      rw [Real.log_div Real.pi_pos.ne' he0.ne', Real.log_exp] at h
      have hpe : π / Real.exp 1 < 6 / 5 := by
        rw [div_lt_iff₀ he0]; linarith [Real.pi_lt_d2, Real.exp_one_gt_d9]
      linarith
    have h57 : 57 / (2 * c) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    have h114 : 0 ≤ 114 / (2 * c) := by positivity
    linarith
  have hKh := four_le_Khigh hc0
  have hKr0 := Cvs.L2a.FiniteSpanRateHighMass.Krate_nonneg hc0
  have hKp0 := Cvs.L2a.WindowChainFromInputs.KpolL_nonneg (1 / 2) (kapFX x)
  unfold Cvs.L2a.QSideConnesRelative.connesLrel
  rw [← hcdef, ← hNd, ← hMd]
  have t1 : 2 * N ≤ (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c) + 114 / (2 * c)) * N :=
    mul_le_mul_of_nonneg_right ha hN0
  have t2 : 8 * M ≤ 2 * Cvs.L2a.LowRungHighSpectralMass.Khigh c * M := by nlinarith
  have t3 : 0 ≤ 4 * √(Cvs.L2a.LowRungTruncationRate.Krate c) * (M + N) := by positivity
  have t4 : 0 ≤ 4 * Cvs.L2a.LowRungTruncationRate.Krate c * M := by positivity
  have t5 : 0 ≤ Cvs.L2a.WindowChainFromInputs.KpolL (1 / 2) (kapFX x) * N := mul_nonneg hKp0 hN0
  linarith

/-- `connesLrel x ≥ 0` for all large `x`. -/
theorem eventually_connesLrel_nonneg : ∀ᶠ x : ℕ in atTop, 0 ≤ Cvs.L2a.QSideConnesRelative.connesLrel x := by
  have h : ∀ᶠ x : ℕ in atTop, c0W ≤ 2 * π * x :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π)).eventually
      (eventually_ge_atTop c0W)
  exact h.mono fun x hx => connesLrel_nonneg hx

/-- **RH from `L1GapL connesLrel` at infinitely many `x`**, through approximate window positivity (Cvs.Route.L1GapNonnegRH). -/
theorem riemannHypothesis_of_L1GapRel_nearPos (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.L1GapParametricRH.L1GapL Cvs.L2a.QSideConnesRelative.connesLrel x) :
    RiemannHypothesis :=
  Cvs.Route.L1GapNonnegRH.riemannHypothesis_of_L1GapL_nearPos eventually_connesLrel_nonneg h

end Cvs.L2a.ConnesRelativeQBoundNonneg
