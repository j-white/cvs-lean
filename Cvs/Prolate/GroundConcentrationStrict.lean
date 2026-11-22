import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformAnalytic
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CellGramTraceComparison
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.FiniteFourierSplitCells
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Upstream.CosineKernelContraction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground concentration is strict: `λ₀ < 1`

For `c > 0` the even prolates have norm one in `E2`, and the scaled cosine transform `p = √(c/2π)ψ_c h₀` is real
analytic with `p = σ₀h₀` on `[−1, 1]`. Plancherel bounds `∫_S p² ≤ 1` on every set `S`; if `λ₀ = 1` then `p`
vanishes on an interval beyond `1`, hence everywhere, contradicting `p(1) = σ₀h₀(1) ≠ 0`. So every `λ_k < 1`.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace Cvs.Prolate.GroundConcentrationStrict
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung muR lamR rung_spec)
open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2)
open Cvs.Prolate.Gram.FiniteFourierSplitCells (zf cosInt evenExt)
open Cvs.Prolate.Gram.CellGramTraceComparison (prolE)
open Cvs.Prolate.Gram.CentralResolventTrace (sigma)

variable {c : ℝ}

/-- `‖h_{2k}‖ = 1` in `E2`. -/
theorem norm_sq_prolE (k : LevelIdx c) : ‖prolE k‖ ^ 2 = 1 := by
  have hk := k.2
  rw [Cvs.Prolate.Gram.FiniteFourierSplitCells.norm_sq_eq_integral]
  have e : (fun u => zf (prolE k) u ^ 2) =ᵐ[volume]
      (Ioc (0 : ℝ) 1).indicator fun u => 2 * rung c k u ^ 2 := by
    filter_upwards [Cvs.Prolate.Gram.CellGramTraceComparison.zf_prolE k] with u hu
    rw [hu]
    by_cases h : u ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_pow, Real.sq_sqrt (by norm_num)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  have hc2 : ContinuousOn (fun s => rung c k s ^ 2) (Icc (-1) 1) := (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hk).pow 2
  have hfold := Cvs.Prolate.SlepianEvenOrdering.integral_even_fold hc2 (fun s hs => by
    rw [(rung_spec hk).2.2.2.2.1 s ⟨by linarith [hs.1], hs.2⟩])
  rw [integral_congr_ae e, integral_indicator measurableSet_Ioc, integral_const_mul,
    ← intervalIntegral.integral_of_le (by norm_num), ← hfold]
  exact (rung_spec hk).2.2.2.2.2

/-- The scaled transform of the even extension is `√(c/2π)ψ_c h_{2k}`. -/
theorem cosIntegral_evenExt_prolE (k : LevelIdx c) (s : ℝ) :
    √(c / (2 * π)) * ∫ t, Real.cos (c * s * t) * evenExt (prolE k) t
      = √(c / (2 * π)) * Cvs.L2a.AngularProlateTailPositive.psi c (rung c k) s := by
  rw [Cvs.Prolate.Gram.FiniteFourierSplitCells.integral_cos_evenExt, Cvs.Prolate.Gram.CellGramTraceComparison.cosInt_prolE]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination √(c / (2 * π)) * Cvs.L2a.AngularProlateTailPositive.psi c (rung c k) s / 2 * h2

/-- **The ground concentration is strict**: `λ₀ < 1` for `c > 0`. -/
theorem lamR_zero_lt_one (hc : 0 < c) : lamR c 0 < 1 := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  set k : LevelIdx c := ⟨0, h0⟩
  set h := rung c 0
  set p : ℝ → ℝ := fun s => √(c / (2 * π)) * Cvs.L2a.AngularProlateTailPositive.psi c h s
  have hint : IntervalIntegrable h volume (-1) 1 :=
    (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h0).intervalIntegrable_of_Icc (by norm_num)
  have hpa : ∀ s, AnalyticAt ℝ p s := fun s => (analyticAt_const).mul (Cvs.Prolate.CosineTransformAnalytic.analyticAt_psi c hint s)
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun s => (hpa s).continuousAt
  have hpe : ∀ s ∈ Icc (-1 : ℝ) 1, p s = sigma c 0 * h s := fun s hs => by
    show √(c / (2 * π)) * Cvs.L2a.AngularProlateTailPositive.psi c (rung c 0) s = sigma c 0 * rung c 0 s
    rw [Cvs.Prolate.EvenRungsByIndex.psi_rung h0 s hs, sigma]; ring
  have hS : ∀ S : Set ℝ, ∫ s in S, p s ^ 2 ≤ 1 := by
    intro S
    have hb := Cvs.Upstream.CosineKernelContraction.setIntegral_sq_cosIntegral_le hc (Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_evenExt (prolE k))
      (Cvs.Prolate.Gram.FiniteFourierSplitCells.integrable_evenExt (prolE k)) S
    rw [Cvs.Prolate.Gram.FiniteFourierSplitCells.integral_evenExt_sq, norm_sq_prolE] at hb
    simpa only [cosIntegral_evenExt_prolE k] using hb
  have hion : ∀ a b : ℝ, IntegrableOn (fun s => p s ^ 2) (Ioc a b) :=
    fun a b => ((hpc.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcore : ∫ s in Ioc (-1 : ℝ) 1, p s ^ 2 = lamR c 0 := by
    have e : ∫ s in Ioc (-1 : ℝ) 1, p s ^ 2 = ∫ s in Ioc (-1 : ℝ) 1, lamR c 0 * h s ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hpe s ⟨hs.1.le, hs.2⟩, mul_pow, Cvs.Prolate.Gram.CentralResolventTrace.sigma_sq]
    rw [e, integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num), (rung_spec h0).2.2.2.2.2,
      mul_one]
  rcases (Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- `∫_{(a, b]} p² ≤ 0` on every interval beyond `1`
  have hnul : ∀ a b : ℝ, 1 ≤ a → ∫ s in Ioc a b, p s ^ 2 ≤ 0 := by
    intro a b ha
    have hdis : Disjoint (Ioc (-1 : ℝ) 1) (Ioc a b) :=
      Set.disjoint_left.mpr fun s hs hs' => by linarith [hs.2, hs'.1]
    have hu := hS (Ioc (-1 : ℝ) 1 ∪ Ioc a b)
    rw [setIntegral_union hdis measurableSet_Ioc (hion _ _) (hion _ _), hcore, heq] at hu
    linarith
  have hp1 : p 1 ≠ 0 := by
    rw [hpe 1 ⟨by norm_num, le_rfl⟩]
    have hσ : 0 < sigma c 0 := mul_pos (Real.sqrt_pos.mpr (by positivity))
      (Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 ⟨0, rfl⟩)
    exact mul_ne_zero hσ.ne' (Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero h0)
  rcases (hpa (3 / 2)).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · have hon : AnalyticOnNhd ℝ p univ := fun s _ => hpa s
    have := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ (3 / 2)) hz
      (mem_univ 1)
    exact hp1 this
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnz)
    set b := 3 / 2 + min ε (1 / 2) with hb
    have hmin : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
    have hpos : 0 < ∫ s in (3 / 2 : ℝ)..b, p s ^ 2 := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ((hpc.pow 2).intervalIntegrable _ _)
        (fun s hs => ?_) (by rw [hb]; linarith)
      have hne : s ≠ 3 / 2 := ne_of_gt hs.1
      have hd : dist s (3 / 2) < ε := by
        rw [Real.dist_eq, abs_of_pos (by linarith [hs.1])]
        have := hs.2; rw [hb] at this; linarith [min_le_left ε (1 / 2)]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hball hd hne)))
    rw [intervalIntegral.integral_of_le (by rw [hb]; linarith)] at hpos
    linarith [hnul (3 / 2) b (by norm_num)]

/-- **Every even concentration is strict**: `λ_k < 1` for `c > 0`. -/
theorem lamR_lt_one (hc : 0 < c) {k : ℕ} (hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) : lamR c k < 1 :=
  ((Cvs.Prolate.EvenRungsByIndex.lamR_anti hc hk (Nat.zero_le k))).trans_lt (lamR_zero_lt_one hc)

end Cvs.Prolate.GroundConcentrationStrict

end
