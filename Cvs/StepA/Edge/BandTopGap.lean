import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.FiniteTopDiscriminant
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.Edge.TwoEdgeSplit
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OddTrialErrorBudget
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.QuadrupleParitySectors
import Cvs.StepA.RestZerosEnvelope
import Cvs.StepA.SectorBottomsLowerBound
import Cvs.StepA.SineModeOddTrial
import Cvs.StepA.TopQuadruple
import Cvs.Upstream.OscillationBeatsError
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band top gap from a finite head and a far tail

A top set whose finite head `S₀` beats its projection error and the far tail,
`2∑_{S₀} m_ρ projRate(z_ρ, Ω) + (16Ω/π)∑'_{S ∖ S₀} m_ρ/γ_ρ² < edgeDisc(S₀, L₀)` with the tail above
some `T > 2Ω`, has a band top gap at bandwidth `Ω`, and so refutes step (a).
-/

noncomputable section

open Real Matrix Filter Topology Asymptotics

namespace Cvs.StepA.Edge.BandTopGap
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI mode_injective mode_negI)
open Cvs.StepA.OneZeroSectorBottoms (lamO)
open Cvs.StepA.OddBottomGapCriterion (OddBottomBelow)
open Cvs.StepA.TopQuadruple (offLine pairE pairO)
open Cvs.StepA.SineModeOddTrial (trialBound)
open Cvs.StepA.ModePolynomialFarEnvelope (envE envO)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg FiniteTop topBotE topBotO blockE blockO)
open Cvs.StepA.Edge.TwoEdgeSplit (edgeForm oddEdge oddEdge_neg continuous_oddEdge oddConst integral_oddEdge_sq re_ctr_sq_of_even neg_re_ctr_sq_of_odd phaseDist abs_edgeForm_sub_le even_block_ge odd_block_le)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeRay edgeDisc sInf_mul_le_edgeForm edgeLower_shift exists_vanishing_gt_of_lt_sSup frequently_phaseDist_log_le)
open Cvs.StepA.Edge.FiniteTopDiscriminant (ord ctr_zPoint_sq EdgePositive)
open Cvs.StepA.Edge.TopSetCriterion (TopSet subset_offLine_of_depth topSet_of_finiteTop bandBotE bandBotO bandRayE_nonempty bddBelow_bandRayO bandBotE_mul_le exists_odd_lt_band mul_dot_pos tsum_split_two BandTopGap)

/-! ### A finite set with a top gap has a band gap -/

/-- The even top bottom of a finite set of zeros is at most its even band bottom. -/
theorem topBotE_le_bandBotE {L : ℝ} (hL : 0 < L) (N : ℕ) (S : Finset nonTrivialZeroSet) :
    topBotE L S ≤ bandBotE L N (S : Set nonTrivialZeroSet) := by
  refine le_csInf (bandRayE_nonempty hL N _) ?_
  rintro r ⟨ξ, hξ, hne, rfl⟩
  have hp := mul_dot_pos hL hne
  have hg : Continuous fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) :=
    (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L (mode N) ξ).comp (continuous_add_const _)
  have heven : ∀ t, Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (-t + L / 2)
      = Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) :=
    Cvs.StepA.OneZeroParitySectors.cosPoly_centred_neg hL.ne' (mode N) ξ
  have hI : ∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) ^ 2
      = L * (ξ ⬝ᵥ ξ) :=
    Cvs.StepA.SectorBottomsLowerBound.integral_cosPoly_centred_sq hL.ne' (mode_injective N) (mode_negI N) hξ
  have hblock : blockE L S mult Cvs.ZeroCounting.zPoint
      (fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2))
      = ∑' ρ : (S : Set nonTrivialZeroSet), mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
    rw [Finset.tsum_subtype' S (fun ρ => mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ))]
    rfl
  have hmem : blockE L S mult Cvs.ZeroCounting.zPoint
      (fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2))
        / (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) ^ 2)
      ∈ Cvs.StepA.Edge.FiniteTopGap.rayE L S mult Cvs.ZeroCounting.zPoint :=
    ⟨_, hg, heven, by rw [hI]; exact hp, rfl⟩
  have h := csInf_le (Cvs.StepA.Edge.FiniteTopGap.bddBelow_rayE (L := L) (s := S)
    (z := Cvs.ZeroCounting.zPoint) fun ρ _ => mult_nonneg ρ) hmem
  rw [hblock, hI] at h
  exact h

/-- For a finite set of zeros off the line and
`topBotO + ∑_S m_ρ (trialBound − lamO)(z_ρ) < Y < 0`, the odd band bottom is at most `Y`. -/
theorem bandBotO_le_of_topBotO {L : ℝ} (hL : 0 < L) {N : ℕ}
    {S : Finset nonTrivialZeroSet} (hS : (S : Set nonTrivialZeroSet) ⊆ offLine) {Y : ℝ}
    (hY : topBotO L S + ∑ ρ ∈ S, mult ρ * (trialBound L N (Cvs.ZeroCounting.zPoint ρ)
      - lamO L (Cvs.ZeroCounting.zPoint ρ)) < Y) (hY0 : Y < 0) :
    bandBotO L N (S : Set nonTrivialZeroSet) ≤ Y := by
  set E := ∑ ρ ∈ S, mult ρ * (trialBound L N (Cvs.ZeroCounting.zPoint ρ)
    - lamO L (Cvs.ZeroCounting.zPoint ρ)) with hEdef
  obtain ⟨φ, hφ, -, hpos, hlt⟩ := Cvs.StepA.Edge.FiniteTopGap.exists_odd_lt (s := S) (w := mult)
    (z := Cvs.ZeroCounting.zPoint) hL (b := Y - E) (by unfold topBotO at hY; linarith)
  obtain ⟨o, ho, hn1, hle⟩ :=
    Cvs.StepA.Edge.FiniteTopGap.exists_odd_trial_block hL.le N (fun ρ _ => mult_nonneg ρ) hφ hpos hlt.le
  have hblock : blockO L S mult Cvs.ZeroCounting.zPoint
      (fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2))
      = ∑' ρ : (S : Set nonTrivialZeroSet), mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ) := by
    rw [Finset.tsum_subtype' S (fun ρ => mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ))]
    rfl
  rw [hblock, ← hEdef] at hle
  have hle' : ∑' ρ : (S : Set nonTrivialZeroSet), mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
      ≤ Y := by linarith
  have hne : o ≠ 0 := by
    rintro rfl
    have h0 : ∑' ρ : (S : Set nonTrivialZeroSet), mult ρ * pairO L N 0 (Cvs.ZeroCounting.zPoint ρ)
        = 0 := by simp [pairO, Cvs.Finite.OddSectorZeroSide.sinePoly]
    linarith
  have hp := mul_dot_pos hL hne
  have hq : ∑' ρ : (S : Set nonTrivialZeroSet), mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
      ≤ Y * (L * (o ⬝ᵥ o)) := by nlinarith
  refine (csInf_le (bddBelow_bandRayO hL N hS) ⟨o, ho, hne, rfl⟩).trans ?_
  rw [div_le_iff₀ hp]
  exact hq

/-- **A top gap of a finite set at a common depth gives a band gap at bandwidth `Ω`**: from
`topBotO + c n^δ ≤ topBotE` frequently and `∑_S m_ρ projRate(z_ρ, Ω) + c' < c`, `c' > 0`, the band
bottoms at `N = ⌈Ω log n/2π⌉₊` satisfy `bandBotO + c' n^δ ≤ bandBotE` frequently. -/
theorem frequently_bandGap_of_topGap {S : Finset nonTrivialZeroSet} {δ Ω c c' : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) (hΩ : 0 < Ω) (hc' : 0 < c')
    (hP : ∑ ρ ∈ S, mult ρ * Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω + c' < c)
    (hG : ∃ᶠ n : ℕ in atTop,
      topBotO (Real.log n) S + c * Real.exp (δ * Real.log n) ≤ topBotE (Real.log n) S) :
    ∃ᶠ n : ℕ in atTop,
      bandBotO (Real.log n) ⌈Ω * Real.log n / (2 * π)⌉₊ (S : Set nonTrivialZeroSet)
          + c' * Real.exp (δ * Real.log n)
        ≤ bandBotE (Real.log n) ⌈Ω * Real.log n / (2 * π)⌉₊ (S : Set nonTrivialZeroSet) := by
  have hsub : (S : Set nonTrivialZeroSet) ⊆ offLine := subset_offLine_of_depth hδ hSδ
  set P := ∑ ρ ∈ S, mult ρ * Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω
    with hPdef
  have hpe : ∀ L, 0 ≤ L → ∑ ρ ∈ S, mult ρ * (trialBound L ⌈Ω * L / (2 * π)⌉₊
      (Cvs.ZeroCounting.zPoint ρ) - lamO L (Cvs.ZeroCounting.zPoint ρ)) ≤ P * Real.exp (δ * L) := by
    intro L hL
    rw [hPdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have habs : |(Cvs.ZeroCounting.zPoint ρ).im| = δ := by
      rw [Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del, abs_neg, hSδ ρ hρ]
    have hy : (Cvs.ZeroCounting.zPoint ρ).im ≠ 0 := fun h0 => by
      rw [h0, abs_zero] at habs; linarith
    have h := Cvs.StepA.OddTrialErrorBudget.trialBound_sub_lamO_le_projRate hL hy hΩ
    rw [habs] at h
    calc mult ρ * (trialBound L ⌈Ω * L / (2 * π)⌉₊
          (Cvs.ZeroCounting.zPoint ρ) - lamO L (Cvs.ZeroCounting.zPoint ρ))
        ≤ mult ρ * (Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω
          * Real.exp (δ * L)) := mul_le_mul_of_nonneg_left h (mult_nonneg ρ)
      _ = mult ρ * Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω
          * Real.exp (δ * L) := by ring
  refine (hG.and_eventually (eventually_gt_atTop 1)).mono fun n ⟨hgap, hn⟩ => ?_
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hE := Real.exp_pos (δ * Real.log n)
  have hTE := Cvs.StepA.Edge.FiniteTopGap.topBotE_nonpos hL S
  have herr := hpe (Real.log n) hL.le
  have h1 : P * Real.exp (δ * Real.log n) < (c - c') * Real.exp (δ * Real.log n) :=
    mul_lt_mul_of_pos_right (by linarith) hE
  have h2 : 0 < c' * Real.exp (δ * Real.log n) := mul_pos hc' hE
  have e1 : (c - c') * Real.exp (δ * Real.log n)
      = c * Real.exp (δ * Real.log n) - c' * Real.exp (δ * Real.log n) := by ring
  have hO := bandBotO_le_of_topBotO (N := ⌈Ω * Real.log n / (2 * π)⌉₊) hL hsub
    (Y := topBotO (Real.log n) S + (c - c') * Real.exp (δ * Real.log n)) (by linarith)
    (by linarith)
  have hEb := topBotE_le_bandBotE hL ⌈Ω * Real.log n / (2 * π)⌉₊ S
  linarith

/-- `∑_S m_ρ projRate(z_ρ, Ω) → 0` as `Ω → ∞`, for a finite set `S`. -/
theorem tendsto_sum_projRate (S : Finset nonTrivialZeroSet) :
    Tendsto (fun Ω => ∑ ρ ∈ S, mult ρ *
      Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω) atTop (𝓝 0) := by
  have h := tendsto_finsetSum S fun ρ _ =>
    (Cvs.StepA.OddTrialErrorBudget.tendsto_projRate (Cvs.ZeroCounting.zPoint ρ)).const_mul (mult ρ)
  simpa only [mul_zero, Finset.sum_const_zero] using h

/-! ### A finite head and a far tail at the top distance -/

/-- The even band bottom of `S` is at least the even band bottom of a subset `S₀` minus the even
envelope of `S ∖ S₀`. -/
theorem bandBotE_ge_head {L : ℝ} (hL : 0 < L) (N : ℕ) {S₀ S : Set nonTrivialZeroSet}
    (h₀ : S₀ ⊆ S) :
    bandBotE L N S₀ - ∑' ρ : ↥(S \ S₀), mult ρ * envE L N (Cvs.ZeroCounting.zPoint ρ)
      ≤ bandBotE L N S := by
  refine le_csInf (bandRayE_nonempty hL N S) ?_
  rintro r ⟨ξ, hξ, hne, rfl⟩
  have hp := mul_dot_pos hL hne
  rw [le_div_iff₀ hp,
    tsum_split_two (f := fun ρ => mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ))
      (Cvs.StepA.QuadrupleParitySectors.summable_pairE hL N ξ) h₀]
  have h1 := bandBotE_mul_le hL N S₀ hξ hne
  have h2 := Cvs.StepA.RestZerosEnvelope.neg_tsum_envE_mul_le hL N ξ (S \ S₀)
  nlinarith

/-- For `S` off the line and a mode pair, the odd band bottom of `S` is at most the odd band bottom
of a subset `S₀` plus the odd envelope of `S ∖ S₀`. -/
theorem bandBotO_le_head {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N)
    {S₀ S : Set nonTrivialZeroSet} (h₀ : S₀ ⊆ S) (hS : S ⊆ offLine) :
    bandBotO L N S
      ≤ bandBotO L N S₀ + ∑' ρ : ↥(S \ S₀), mult ρ * envO L N (Cvs.ZeroCounting.zPoint ρ) := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨o, ho, hne, hlt⟩ :=
    exists_odd_lt_band hL hN S₀ (b := bandBotO L N S₀ + ε) (by linarith)
  have hp := mul_dot_pos hL hne
  have hsplit := tsum_split_two (f := fun ρ => mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ))
    (Cvs.StepA.QuadrupleParitySectors.summable_pairO hL N o) h₀
  have hrest := Cvs.StepA.RestZerosEnvelope.tsum_pairO_le_tsum_envO_mul hL N o (S \ S₀)
  have hq : (∑' ρ : S, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)) / (L * (o ⬝ᵥ o))
      < bandBotO L N S₀ + (∑' ρ : ↥(S \ S₀), mult ρ * envO L N (Cvs.ZeroCounting.zPoint ρ))
        + ε := by
    rw [div_lt_iff₀ hp, hsplit]
    nlinarith
  exact lt_of_le_of_lt (csInf_le (bddBelow_bandRayO hL N hS) ⟨o, ho, hne, rfl⟩) hq

/-- `cosh(z.im·L/2) = cosh(δL/2)` when `|z.im| = δ` and `L > 0`. -/
theorem cosh_half_eq {L δ : ℝ} (hL : 0 < L) {z : ℂ} (hz : |z.im| = δ) :
    cosh (z.im * L / 2) = cosh (δ * L / 2) := by
  rw [← Real.cosh_abs, abs_div, abs_mul, hz, abs_of_pos hL, abs_two]

/-- **The far envelope at the top distance**: a zero at distance `δ` with `|γ| ≥ 2·(2πN/L)` has
`envE = envO = 16(2N+1)cosh²(δL/2)/(Lγ²)`. -/
theorem env_far_eq {L : ℝ} (hL : 0 < L) {N : ℕ} {ρ : nonTrivialZeroSet} {δ : ℝ}
    (hρ : |Cvs.GaussKernel.del ρ| = δ) (hfar : 2 * (2 * π * N / L) ≤ |(ρ : ℂ).im|) :
    envE L N (Cvs.ZeroCounting.zPoint ρ)
        = 16 * (2 * N + 1) * cosh (δ * L / 2) ^ 2 / (L * ((ρ : ℂ).im) ^ 2) ∧
      envO L N (Cvs.ZeroCounting.zPoint ρ)
        = 16 * (2 * N + 1) * cosh (δ * L / 2) ^ 2 / (L * ((ρ : ℂ).im) ^ 2) := by
  have hre : (Cvs.ZeroCounting.zPoint ρ).re = (ρ : ℂ).im := Cvs.ZeroCounting.zPoint_re ρ
  have him : |(Cvs.ZeroCounting.zPoint ρ).im| = δ := by
    rw [Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del, abs_neg, hρ]
  have hf : 2 * (2 * π * N / L) ≤ |(Cvs.ZeroCounting.zPoint ρ).re| := by rw [hre]; exact hfar
  constructor
  · rw [envE, if_pos hf, hre, cosh_half_eq hL him]
  · rw [envO, if_pos hf, hre, cosh_half_eq hL him]

/-- **The tail envelope at the top distance**: if every zero of `T` lies at distance `δ` with
`|γ| ≥ 2·(2πN/L)`, both envelope sums over `T` equal `16(2N+1)cosh²(δL/2)/L · ∑'_T m_ρ/γ_ρ²`. -/
theorem tsum_tail_env {L : ℝ} (hL : 0 < L) {N : ℕ} {T : Set nonTrivialZeroSet} {δ : ℝ}
    (hT : ∀ ρ ∈ T, |Cvs.GaussKernel.del ρ| = δ)
    (hfar : ∀ ρ ∈ T, 2 * (2 * π * N / L) ≤ |(ρ : ℂ).im|) :
    ∑' ρ : T, mult ρ * envE L N (Cvs.ZeroCounting.zPoint ρ)
        = 16 * (2 * N + 1) * cosh (δ * L / 2) ^ 2 / L
          * ∑' ρ : T, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) ∧
      ∑' ρ : T, mult ρ * envO L N (Cvs.ZeroCounting.zPoint ρ)
        = 16 * (2 * N + 1) * cosh (δ * L / 2) ^ 2 / L
          * ∑' ρ : T, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) := by
  constructor
  · rw [← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    rw [(env_far_eq hL (hT ρ ρ.2) (hfar ρ ρ.2)).1]
    ring
  · rw [← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    rw [(env_far_eq hL (hT ρ ρ.2) (hfar ρ ρ.2)).2]
    ring

/-- `cosh²(x/2) = eˣ(1 + e⁻ˣ)²/4`. -/
theorem cosh_half_sq_eq (x : ℝ) :
    cosh (x / 2) ^ 2 = Real.exp x * (1 + Real.exp (-x)) ^ 2 / 4 := by
  rw [Real.cosh_eq]
  have ha : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]; congr 1; ring
  have hb : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hc : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; simp
  have hd : Real.exp (-(x / 2)) * Real.exp (-(x / 2)) = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination (1 / 4 : ℝ) * ha + (1 / 2 : ℝ) * hb + (1 / 4 : ℝ) * hd - (1 / 2 : ℝ) * hc
    - (1 / 4 : ℝ) * Real.exp (-x) * hc

/-- `⌈ΩL/2π⌉₊/L → Ω/2π` as `L → ∞`, for `Ω ≥ 0`. -/
theorem tendsto_natCeil_div {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    Tendsto (fun L : ℝ => (⌈Ω * L / (2 * π)⌉₊ : ℝ) / L) atTop (𝓝 (Ω / (2 * π))) := by
  simpa only [div_mul_eq_mul_div] using
    tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := Ω / (2 * π)) (by positivity)

/-- **The band edge**: at `N = ⌈ΩL/2π⌉₊`, `2·(2πN/L) → 2Ω` as `L → ∞`, for `Ω ≥ 0`. -/
theorem tendsto_far {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    Tendsto (fun L : ℝ => 2 * (2 * π * (⌈Ω * L / (2 * π)⌉₊ : ℝ) / L)) atTop (𝓝 (2 * Ω)) := by
  have h := (tendsto_natCeil_div hΩ).const_mul (4 * π)
  have e : 4 * π * (Ω / (2 * π)) = 2 * Ω := by field_simp; ring
  rw [e] at h
  exact h.congr fun L => by ring

/-- **The tail coefficient**: at `N = ⌈ΩL/2π⌉₊`, `δ > 0` and `Ω ≥ 0`,
`16(2N+1)cosh²(δL/2)/L · e^{−δL} → 4Ω/π` as `L → ∞`. -/
theorem tendsto_tail_coef {Ω δ : ℝ} (hΩ : 0 ≤ Ω) (hδ : 0 < δ) :
    Tendsto (fun L : ℝ => 16 * (2 * (⌈Ω * L / (2 * π)⌉₊ : ℝ) + 1) * cosh (δ * L / 2) ^ 2 / L
      / Real.exp (δ * L)) atTop (𝓝 (4 * Ω / π)) := by
  have h1 : Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hexp : Tendsto (fun L : ℝ => Real.exp (-(δ * L))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hδ)
  have h := ((((tendsto_natCeil_div hΩ).const_mul 2).add h1).const_mul 16).mul
    (((tendsto_const_nhds (x := (1 : ℝ))).add hexp).pow 2) |>.div_const 4
  have e : 16 * (2 * (Ω / (2 * π)) + 0) * (1 + 0) ^ 2 / 4 = 4 * Ω / π := by field_simp; ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with L hL
  have hE := Real.exp_pos (δ * L)
  rw [cosh_half_sq_eq (δ * L)]
  field_simp

/-- **A head with a band gap beating the far tail gives a band top gap**: for a top set `S`,
`S₀ ⊆ S`, `S ∖ S₀` above `T > 2Ω`, and a head band gap `c > (8Ω/π)·∑'_{S ∖ S₀} m_ρ/γ_ρ²` along
`N = ⌈Ω log n/2π⌉₊`, the top set `S` has a band top gap at bandwidth `Ω`. -/
theorem bandTopGap_of_head {S S₀ : Set nonTrivialZeroSet} {δ Ω T c : ℝ} (hS : TopSet S δ)
    (h₀ : S₀ ⊆ S) (hΩ : 0 < Ω) (hT : 2 * Ω < T) (hfar : ∀ ρ ∈ S \ S₀, T ≤ |(ρ : ℂ).im|)
    (hc : 8 * Ω / π * ∑' ρ : ↥(S \ S₀), mult ρ * (1 / ((ρ : ℂ).im) ^ 2) < c)
    (hG : ∃ᶠ n : ℕ in atTop,
      bandBotO (Real.log n) ⌈Ω * Real.log n / (2 * π)⌉₊ S₀ + c * Real.exp (δ * Real.log n)
        ≤ bandBotE (Real.log n) ⌈Ω * Real.log n / (2 * π)⌉₊ S₀) :
    BandTopGap S δ Ω := by
  have hδ : 0 < δ := hS.1
  set τ := ∑' ρ : ↥(S \ S₀), mult ρ * (1 / ((ρ : ℂ).im) ^ 2) with hτ
  have hτ0 : 0 ≤ τ := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg _) (by positivity)
  set M := (c + 8 * Ω / π * τ) / 2 with hM
  have hcM : 0 < c - M := by rw [hM]; linarith
  have hK := (tendsto_tail_coef hΩ.le hδ).const_mul (2 * τ)
  have hKM : 2 * τ * (4 * Ω / π) < M := by
    have e : 2 * τ * (4 * Ω / π) = 8 * Ω / π * τ := by ring
    rw [e, hM]; linarith
  have hev : ∀ᶠ L in atTop, 0 < L ∧ 2 * (2 * π * (⌈Ω * L / (2 * π)⌉₊ : ℝ) / L) < T ∧
      2 * τ * (16 * (2 * (⌈Ω * L / (2 * π)⌉₊ : ℝ) + 1) * cosh (δ * L / 2) ^ 2 / L
        / Real.exp (δ * L)) < M :=
    (eventually_gt_atTop 0).and (((tendsto_far hΩ.le).eventually (gt_mem_nhds hT)).and
      (hK.eventually (gt_mem_nhds hKM)))
  have hφ : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨c - M, hcM, (hG.and_eventually (hφ.eventually hev)).mono
    fun n ⟨hgap, hL, hfarL, hg⟩ => ?_⟩
  show bandBotO (Real.log n) ⌈Ω * Real.log n / (2 * π)⌉₊ S + (c - M) * Real.exp (δ * Real.log n)
    ≤ bandBotE (Real.log n) ⌈Ω * Real.log n / (2 * π)⌉₊ S
  set L := Real.log n with hLdef
  set N := ⌈Ω * L / (2 * π)⌉₊ with hNdef
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hfarN : ∀ ρ ∈ S \ S₀, 2 * (2 * π * N / L) ≤ |(ρ : ℂ).im| :=
    fun ρ hρ => hfarL.le.trans (hfar ρ hρ)
  have hTδ : ∀ ρ ∈ S \ S₀, |Cvs.GaussKernel.del ρ| = δ := fun ρ hρ => hS.2.2.1 ρ hρ.1
  obtain ⟨hTE, hTO⟩ := tsum_tail_env hL hTδ hfarN
  have hE := bandBotE_ge_head hL N h₀
  have hO := bandBotO_le_head hL hN h₀ hS.subset_offLine
  rw [hTE] at hE
  rw [hTO] at hO
  have hexp := Real.exp_pos (δ * L)
  set K := 16 * (2 * (N : ℝ) + 1) * cosh (δ * L / 2) ^ 2 / L with hKdef
  have hKτ : 2 * (K * τ) ≤ M * Real.exp (δ * L) := by
    rw [← mul_div_assoc] at hg
    have h := (div_lt_iff₀ hexp).mp hg
    linarith
  have hcm : (c - M) * Real.exp (δ * L) = c * Real.exp (δ * L) - M * Real.exp (δ * L) := by ring
  nlinarith

/-! ### The edge bounds at a common depth -/

/-- The even top bottom from an edge lower bound, for a finite set at a common depth `δ > 0`:
it is at least `e^{δL}λ/2 − (∑_S m_ρ)(2e^{δL/2} + 1)/(4δ)`. -/
theorem le_topBotE_of_edge_of_depth {S : Finset nonTrivialZeroSet} {δ : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) {L : ℝ} (hL : 0 < L) {lam : ℝ}
    (hlam : ∀ F : ℝ → ℝ, ∀ a : ℝ, Continuous F → 0 ≤ a →
      lam * ∫ u in (0 : ℝ)..a, F u ^ 2 ≤ edgeForm S mult ord δ L F a) :
    Real.exp (δ * L) * lam / 2 - (∑ ρ ∈ S, mult ρ) * (2 * Real.exp (δ * L / 2) + 1) / (4 * δ)
      ≤ topBotE L S := by
  unfold topBotE Cvs.StepA.Edge.FiniteTopGap.botE
  refine le_csInf (Cvs.StepA.Edge.FiniteTopGap.nonempty_rayE hL) ?_
  rintro r ⟨g, hg, heven, hpos, rfl⟩
  rw [le_div_iff₀ hpos]
  refine (even_block_ge S (fun ρ _ => mult_nonneg ρ) ord hδ hL.le hlam hg heven).trans
    (le_of_eq ?_)
  unfold blockE
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  congr 1
  rw [← ctr_zPoint_sq L (hg.intervalIntegrable _ _) (Or.inl heven) hδ (hSδ ρ hρ),
    re_ctr_sq_of_even L (hg.intervalIntegrable _ _) heven]

/-- The odd top bottom from an edge profile, for a finite set at a common depth `δ > 0`: it is at
most `(−e^{δL} edgeForm(L, F, a) + ∑_S m_ρ oddConst(F, a))/(2∫₀^a F²)`. -/
theorem topBotO_le_of_edge_of_depth {S : Finset nonTrivialZeroSet} {δ : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) {L : ℝ}
    {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) (haL : 2 * a ≤ L)
    (hsupp : ∀ u, a ≤ u → F u = 0) (hn : 0 < ∫ u in (0 : ℝ)..a, F u ^ 2) :
    topBotO L S ≤ (-(Real.exp (δ * L) * edgeForm S mult ord δ L F a)
        + ∑ ρ ∈ S, mult ρ * oddConst δ (ord ρ) F a) / (2 * ∫ u in (0 : ℝ)..a, F u ^ 2) := by
  have hgc := continuous_oddEdge L hF
  have hgo := oddEdge_neg L F
  have hint := hgc.intervalIntegrable (μ := MeasureTheory.volume) (-(L / 2)) (L / 2)
  have hI := integral_oddEdge_sq hF ha haL hsupp
  have hpos : 0 < ∫ t in -(L / 2)..L / 2, oddEdge L F t ^ 2 := by rw [hI]; linarith
  have hblock : blockO L S mult Cvs.ZeroCounting.zPoint (oddEdge L F)
      ≤ -(Real.exp (δ * L) * edgeForm S mult ord δ L F a)
        + ∑ ρ ∈ S, mult ρ * oddConst δ (ord ρ) F a := by
    refine le_trans (le_of_eq ?_)
      (odd_block_le S (fun ρ _ => mult_nonneg ρ) ord hδ.le hF ha haL hsupp)
    unfold blockO
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    congr 1
    rw [← ctr_zPoint_sq L hint (Or.inr hgo) hδ (hSδ ρ hρ), neg_re_ctr_sq_of_odd L hint hgo]
  unfold topBotO Cvs.StepA.Edge.FiniteTopGap.botO
  refine (csInf_le (Cvs.StepA.Edge.FiniteTopGap.bddBelow_rayO fun ρ _ => mult_nonneg ρ)
    ⟨oddEdge L F, hgc, hgo, hpos, rfl⟩).trans ?_
  rw [hI]
  exact div_le_div_of_nonneg_right hblock (by linarith)

/-- The top gap at `L` from an edge witness at `L₀`, for a finite set at a common depth `δ > 0`:
`topBotE − topBotO ≥ e^{δL}((λ + E₀/n₀)/2 − phaseDist/(2δ)) − M(2e^{δL/2} + 1)/(4δ) − K/(2n₀)`. -/
theorem sub_topBot_ge_of_edge_of_depth {S : Finset nonTrivialZeroSet} {δ : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) {L₀ lam : ℝ}
    (hlam : ∀ F : ℝ → ℝ, ∀ a : ℝ, Continuous F → 0 ≤ a →
      lam * ∫ u in (0 : ℝ)..a, F u ^ 2 ≤ edgeForm S mult ord δ L₀ F a)
    {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (hsupp : ∀ u, a₀ ≤ u → F₀ u = 0)
    (hn : 0 < ∫ u in (0 : ℝ)..a₀, F₀ u ^ 2) {L : ℝ} (hL : 0 < L) (h2a : 2 * a₀ ≤ L) :
    Real.exp (δ * L) * ((lam + edgeForm S mult ord δ L₀ F₀ a₀ / ∫ u in (0 : ℝ)..a₀, F₀ u ^ 2) / 2
        - phaseDist S mult ord L L₀ / (2 * δ))
      - (∑ ρ ∈ S, mult ρ) * (2 * Real.exp (δ * L / 2) + 1) / (4 * δ)
      - (∑ ρ ∈ S, mult ρ * oddConst δ (ord ρ) F₀ a₀) / (2 * ∫ u in (0 : ℝ)..a₀, F₀ u ^ 2)
      ≤ topBotE L S - topBotO L S := by
  have hE := le_topBotE_of_edge_of_depth hδ hSδ hL
    (edgeLower_shift S (fun ρ _ => mult_nonneg ρ) ord hδ hlam L)
  have hO := topBotO_le_of_edge_of_depth hδ hSδ hF₀ ha₀ h2a hsupp hn
  have hEL :=
    (abs_le.mp (abs_edgeForm_sub_le S (fun ρ _ => mult_nonneg ρ) ord hδ L L₀ hF₀ ha₀)).1
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℝ, n₀ = ∫ u in (0 : ℝ)..a₀, F₀ u ^ 2 := ⟨_, rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = edgeForm S mult ord δ L₀ F₀ a₀ := ⟨_, rfl⟩
  obtain ⟨EL, hEL₀⟩ : ∃ EL : ℝ, EL = edgeForm S mult ord δ L F₀ a₀ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = phaseDist S mult ord L L₀ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ ρ ∈ S, mult ρ * oddConst δ (ord ρ) F₀ a₀ := ⟨_, rfl⟩
  rw [← hn₀, ← hE₀, ← hD, ← hK]
  rw [← hn₀, ← hEL₀, ← hK] at hO
  rw [← hn₀, ← hEL₀, ← hE₀, ← hD] at hEL
  rw [← hD] at hE
  have hn' : 0 < n₀ := hn₀ ▸ hn
  have he : 0 < Real.exp (δ * L) := Real.exp_pos _
  have h1 : -(Real.exp (δ * L) * EL) + K
      ≤ -(Real.exp (δ * L) * (E₀ - D * n₀ / (2 * δ))) + K := by
    have : E₀ - D * n₀ / (2 * δ) ≤ EL := by linarith
    nlinarith
  have h2 : (-(Real.exp (δ * L) * (E₀ - D * n₀ / (2 * δ))) + K) / (2 * n₀)
      = -(Real.exp (δ * L) * (E₀ / n₀ - D / (2 * δ))) / 2 + K / (2 * n₀) := by
    field_simp
  have hO2 : topBotO L S
      ≤ -(Real.exp (δ * L) * (E₀ / n₀ - D / (2 * δ))) / 2 + K / (2 * n₀) := by
    rw [← h2]
    exact hO.trans (div_le_div_of_nonneg_right h1 (by linarith))
  have h3 : Real.exp (δ * L) * ((lam + E₀ / n₀) / 2 - D / (2 * δ))
      = Real.exp (δ * L) * (lam - D / (2 * δ)) / 2
        + Real.exp (δ * L) * (E₀ / n₀ - D / (2 * δ)) / 2 := by ring
  linarith

/-- **The top gap from the edge discriminant at a common depth**: for a finite set at a common
depth `δ > 0` and every `c < edgeDisc(L₀)/2`, `topBotO + c n^δ ≤ topBotE` at `L = log n`
frequently. -/
theorem frequently_topGap_of_lt_of_depth {S : Finset nonTrivialZeroSet} {δ : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) {L₀ c : ℝ}
    (hc : c < edgeDisc S mult ord δ L₀ / 2) :
    ∃ᶠ n : ℕ in atTop,
      topBotO (Real.log n) S + c * Real.exp (δ * Real.log n) ≤ topBotE (Real.log n) S := by
  have hm : ∀ ρ ∈ S, 0 ≤ mult ρ := fun ρ _ => mult_nonneg ρ
  have ht : 2 * c - sInf (edgeRay S mult ord δ L₀) < sSup (edgeRay S mult ord δ L₀) := by
    unfold edgeDisc at hc; linarith
  obtain ⟨F₀, a₀, hF₀, ha₀, hsupp, hn, hw⟩ := exists_vanishing_gt_of_lt_sSup S mult ord hδ.le ht
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = (sInf (edgeRay S mult ord δ L₀)
      + edgeForm S mult ord δ L₀ F₀ a₀ / ∫ u in (0 : ℝ)..a₀, F₀ u ^ 2) / 2 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = c₀ - c := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη, hc₀]; linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ ρ ∈ S, mult ρ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∑ ρ ∈ S, mult ρ * oddConst δ (ord ρ) F₀ a₀)
      / (2 * ∫ u in (0 : ℝ)..a₀, F₀ u ^ 2) := ⟨_, rfl⟩
  have hone : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun L => Real.exp (δ * L) := by
    have h := Cvs.Upstream.OscillationBeatsError.isLittleO_exp_exp (a := 0) (b := δ) hδ
    simpa only [zero_mul, Real.exp_zero] using h
  have hhalf : (fun L : ℝ => Real.exp (δ * L / 2)) =o[atTop] fun L => Real.exp (δ * L) := by
    have h := Cvs.Upstream.OscillationBeatsError.isLittleO_exp_exp (a := δ / 2) (b := δ) (by linarith)
    refine h.congr_left fun L => ?_
    congr 1
    ring
  have hR : (fun L : ℝ => M * (2 * Real.exp (δ * L / 2) + 1) / (4 * δ) + K)
      =o[atTop] fun L => Real.exp (δ * L) := by
    have h := ((hhalf.const_mul_left (M / (2 * δ))).add
      (hone.const_mul_left (M / (4 * δ)))).add (hone.const_mul_left K)
    refine h.congr_left fun L => ?_
    ring
  have hev : ∀ᶠ L in atTop, 0 < L ∧ 2 * a₀ ≤ L ∧
      M * (2 * Real.exp (δ * L / 2) + 1) / (4 * δ) + K ≤ η / 2 * Real.exp (δ * L) := by
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (2 * a₀),
      hR.bound (by positivity : (0 : ℝ) < η / 2)] with L h0 h1 h2
    refine ⟨h0, h1, ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h2
    exact (le_abs_self _).trans h2
  have hφ : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := frequently_phaseDist_log_le S hm ord L₀ (ε := δ * η) (by positivity)
  refine (hs.and_eventually (hφ.eventually hev)).mono fun n ⟨hD, hL, h2a, hrem⟩ => ?_
  have h := sub_topBot_ge_of_edge_of_depth hδ hSδ
    (fun F a hF ha => sInf_mul_le_edgeForm S hm ord hδ L₀ hF ha) hF₀ ha₀ hsupp hn hL h2a
  rw [← hc₀, ← hM, ← hK] at h
  have hD' : phaseDist S mult ord (Real.log n) L₀ / (2 * δ) ≤ η / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have he := Real.exp_pos (δ * Real.log n)
  have h4 : Real.exp (δ * Real.log n) * (c₀ - η / 2)
      ≤ Real.exp (δ * Real.log n) * (c₀ - phaseDist S mult ord (Real.log n) L₀ / (2 * δ)) :=
    mul_le_mul_of_nonneg_left (by linarith) he.le
  have h5 : c * Real.exp (δ * Real.log n)
      = Real.exp (δ * Real.log n) * (c₀ - η / 2) - η / 2 * Real.exp (δ * Real.log n) := by
    rw [hη]; ring
  linarith

/-! ### The head margin -/

/-- **The head margin**: `S` is a top set at `δ`, `S₀ ⊆ S` is finite, `S ∖ S₀` lies above some
`T > 2Ω > 0`, and `2∑_{S₀} m_ρ projRate(z_ρ, Ω) + (16Ω/π)∑'_{S ∖ S₀} m_ρ/γ_ρ²` is below
`edgeDisc(S₀, L₀)`. -/
def HeadMargin (S : Set nonTrivialZeroSet) (δ : ℝ) (S₀ : Finset nonTrivialZeroSet) (Ω L₀ : ℝ) :
    Prop :=
  TopSet S δ ∧ (S₀ : Set nonTrivialZeroSet) ⊆ S ∧ 0 < Ω ∧
    (∃ T : ℝ, 2 * Ω < T ∧ ∀ ρ ∈ S \ (S₀ : Set nonTrivialZeroSet), T ≤ |(ρ : ℂ).im|) ∧
    2 * ∑ ρ ∈ S₀, mult ρ * Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω
        + 16 * Ω / π
          * ∑' ρ : ↥(S \ (S₀ : Set nonTrivialZeroSet)), mult ρ * (1 / ((ρ : ℂ).im) ^ 2)
      < edgeDisc S₀ mult ord δ L₀

/-- **A head margin gives a band top gap at bandwidth `Ω`.** -/
theorem bandTopGap_of_margin {S : Set nonTrivialZeroSet} {δ : ℝ} {S₀ : Finset nonTrivialZeroSet}
    {Ω L₀ : ℝ} (h : HeadMargin S δ S₀ Ω L₀) : BandTopGap S δ Ω := by
  obtain ⟨hS, h₀, hΩ, ⟨T, hT, hfar⟩, hmargin⟩ := h
  have hδ : 0 < δ := hS.1
  have hSδ : ∀ ρ ∈ S₀, |Cvs.GaussKernel.del ρ| = δ := fun ρ hρ => hS.2.2.1 ρ (h₀ hρ)
  set P := ∑ ρ ∈ S₀, mult ρ * Cvs.StepA.OddTrialErrorBudget.projRate (Cvs.ZeroCounting.zPoint ρ) Ω
  set τ := ∑' ρ : ↥(S \ (S₀ : Set nonTrivialZeroSet)), mult ρ * (1 / ((ρ : ℂ).im) ^ 2)
  have hτ0 : 0 ≤ τ := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg _) (by positivity)
  have hτΩ : 0 ≤ 8 * Ω / π * τ := by positivity
  set D := edgeDisc S₀ mult ord δ L₀
  have e : 16 * Ω / π * τ = 2 * (8 * Ω / π * τ) := by ring
  set c := (P + 8 * Ω / π * τ + D / 2) / 2 with hcdef
  set c' := (c - P + 8 * Ω / π * τ) / 2 with hc'def
  have hG := frequently_topGap_of_lt_of_depth hδ hSδ (L₀ := L₀) (c := c)
    (by rw [hcdef]; linarith)
  have hB := frequently_bandGap_of_topGap hδ hSδ hΩ (c' := c')
    (by rw [hc'def, hcdef]; linarith) (by rw [hc'def, hcdef]; linarith) hG
  exact bandTopGap_of_head hS h₀ hΩ hT hfar (by rw [hc'def, hcdef]; linarith) hB

/-- **A finite top set with positive edge discriminant at `L₀` has a head margin at `L₀` with head
`S₀ = S` and empty tail at every large bandwidth.** -/
theorem eventually_headMargin_of_finiteTop {S : Finset nonTrivialZeroSet} {δ L₀ : ℝ}
    (hS : FiniteTop S δ) (hpos : 0 < edgeDisc S mult ord δ L₀) :
    ∀ᶠ Ω in atTop, HeadMargin (S : Set nonTrivialZeroSet) δ S Ω L₀ := by
  have : IsEmpty ↥((S : Set nonTrivialZeroSet) \ (S : Set nonTrivialZeroSet)) :=
    ⟨fun ⟨_, hx⟩ => hx.2 hx.1⟩
  filter_upwards [eventually_gt_atTop 0, (tendsto_sum_projRate S).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < edgeDisc S mult ord δ L₀ / 2))] with Ω hΩ hp
  refine ⟨topSet_of_finiteTop hS, subset_rfl, hΩ,
    ⟨2 * Ω + 1, by linarith, fun ρ hρ => absurd hρ.1 hρ.2⟩, ?_⟩
  rw [tsum_empty, mul_zero, add_zero]
  linarith

end Cvs.StepA.Edge.BandTopGap
