import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.RungSpanTailHighMass
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.WkbEndpointAmplitude
import Cvs.Prolate.SepticLevelComparison
import Cvs.Route.JointGapRayleighExplicit
import Cvs.Route.ProlateFloorNearPositivity
import Cvs.WeilForm.ApproxWindowPositivityRH
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Near-positivity at the prolate-scale `s` alone gives RH

With `h₈(1)² ≤ 2c/π`, the `s`-clause of `Cvs.Route.ProlateFloorNearPositivity.ProlateFloor` forces `s ≤ ε/(2πK) → 0`, so near-positivity at those
`x` is approximate window positivity and `Cvs.WeilForm.ApproxWindowPositivityRH.rh_of_approx_windowPos` applies; `Q ≥ 0` at infinitely many `x`
suffices on its own.
-/

noncomputable section
open Real Filter Topology

namespace Cvs.Route.NearPositivityProlateScale
open Cvs.ZeroCounting
open Cvs.ZeroCounting
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR psi_rung rung_spec)

/-- `h₈(1)² ≤ 2c/π` at `c = 2πx ≥ 80`. -/
theorem rung4_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx3 : 3 ≤ x) :
    rung (2 * π * x) 4 1 ^ 2 ≤ 2 * (2 * π * x) / π := by
  set c := 2 * π * (x : ℝ) with hcd
  have hpi := Real.pi_gt_three
  have hc0 : 0 < c := by linarith
  have h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c 4 χ :=
    Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by nlinarith [Real.pi_lt_d2]) le_rfl
  have hl : 1 / 2 ≤ lamR c 4 := Cvs.L2a.WindowChainInputsProlate.half_le_lamR (j := 2) hx (by omega)
  have e : lamR c 4 = muR c 4 ^ 2 * (c / (2 * π)) := by
    unfold lamR; rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hmu : π / c ≤ muR c 4 ^ 2 := by
    rw [e] at hl
    rw [div_le_iff₀ hc0]
    have : muR c 4 ^ 2 * (c / (2 * π)) * (2 * π) = muR c 4 ^ 2 * c := by field_simp
    nlinarith
  obtain ⟨hg, -, -, -, -, hnorm⟩ := rung_spec h
  have hgc : ContinuousOn (rung c 4) (Set.uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hpsi := Cvs.L2a.RungSpanTailHighMass.abs_psi_le_L1 (c := c) (ξ := 1) hgc
  have hI := Cvs.Prolate.LiouvilleGreen.WkbEndpointAmplitude.integral_abs_le_sqrt_two hgc hnorm
  rw [psi_rung h 1 ⟨by norm_num, le_rfl⟩] at hpsi
  have hab : |muR c 4 * rung c 4 1| ≤ √2 := by linarith
  have hsq : (muR c 4 * rung c 4 1) ^ 2 ≤ 2 := by
    have := sq_le_sq' (abs_le.1 hab).1 (abs_le.1 hab).2
    rwa [Real.sq_sqrt (by norm_num)] at this
  have hr0 : 0 ≤ rung c 4 1 ^ 2 := sq_nonneg _
  have h1 : π / c * rung c 4 1 ^ 2 ≤ 2 := by
    calc π / c * rung c 4 1 ^ 2 ≤ muR c 4 ^ 2 * rung c 4 1 ^ 2 := mul_le_mul_of_nonneg_right hmu hr0
      _ = (muR c 4 * rung c 4 1) ^ 2 := by ring
      _ ≤ 2 := hsq
  rw [div_mul_eq_mul_div, div_le_iff₀ hc0] at h1
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **RH from near-positivity at the prolate-scale `s`**, through `Cvs.WeilForm.ApproxWindowPositivityRH.rh_of_approx_windowPos`. -/
theorem rh_of_prolateFloor_nearPos_only {ε : ℝ} (hε : 0 < ε)
    (h : ∃ᶠ x : ℕ in atTop, ∃ (s : ℝ),
      (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
      s * (√(x : ℝ) * Real.log x * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x)) ≤ ε / 4 * rung (2 * π * x) 4 1 ^ 2 / (2 * π * x)) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ApproxWindowPositivityRH.rh_of_approx_windowPos fun ε' hε' x₀ => ?_
  have hK : Tendsto (fun x : ℕ => √(x : ℝ) * Real.log x) atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ ?_ ?_
    · exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ x : ℕ in atTop, x₀ ≤ x ∧ 3 ≤ x ∧ (80 : ℝ) ≤ 2 * π * x ∧
      ε / (2 * π) / ε' ≤ √(x : ℝ) * Real.log x := by
    have h80 : ∀ᶠ x : ℕ in atTop, (80 : ℝ) ≤ 2 * π * x :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0:ℝ) < 2 * π)).eventually
        (eventually_ge_atTop 80)
    filter_upwards [eventually_ge_atTop x₀, eventually_ge_atTop 3, h80, hK.eventually (eventually_ge_atTop _)]
      with x a b c d using ⟨a, b, c, d⟩
  obtain ⟨x, ⟨s, hneg, hs⟩, hx₀, hx3, hx80, hKx⟩ := (h.and_eventually hev).exists
  refine ⟨x, hx₀, fun φ => ?_⟩
  have hpi := Real.pi_gt_three
  have hx3' : (3 : ℝ) ≤ x := by exact_mod_cast hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hc0 : (0 : ℝ) < 2 * π * x := by positivity
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hR : 0 ≤ Cvs.Route.JointGapRayleighExplicit.Rx x := by unfold Cvs.Route.JointGapRayleighExplicit.Rx; positivity
  set K := √(x : ℝ) * Real.log x with hKd
  have hK0 : 0 < K := by positivity
  have hr := rung4_sq_le hx80 hx3
  -- s ≤ ε'
  have hsle : s ≤ ε' := by
    by_contra hcon
    push Not at hcon
    have hb : ε / 4 * rung (2 * π * x) 4 1 ^ 2 / (2 * π * x) ≤ ε / (2 * π) := by
      rw [div_le_iff₀ hc0]
      have : ε / 4 * rung (2 * π * x) 4 1 ^ 2 ≤ ε / 4 * (2 * (2 * π * x) / π) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      have e : ε / 4 * (2 * (2 * π * x) / π) = ε / (2 * π) * (2 * π * x) := by field_simp; ring
      linarith
    have hKe : ε / (2 * π) ≤ ε' * K := by
      rw [div_le_iff₀ hε'] at hKx; linarith
    have hstrict : ε' * K < s * (K * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x)) := by
      have h1 : ε' * K < s * K := mul_lt_mul_of_pos_right hcon hK0
      have h2 : s * K ≤ s * (K * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x)) := by
        have : K ≤ K * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x) := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    linarith
  have := hneg φ
  have hn : 0 ≤ ‖φ‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **RH from frequent `ProlateFloor`**, using only its near-positivity and `s` clauses. -/
theorem rh_of_prolateFloor {ε : ℝ} (hε : 0 < ε) (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.ProlateFloorNearPositivity.ProlateFloor ε x) :
    RiemannHypothesis :=
  rh_of_prolateFloor_nearPos_only hε (h.mono fun _ ⟨s, _, _, hneg, _, _, hs⟩ => ⟨s, hneg, hs⟩)

/-- **RH from `Q ≥ 0` at infinitely many `x`**. -/
theorem rh_of_frequent_nonneg
    (h : ∃ᶠ x : ℕ in atTop, ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) : RiemannHypothesis :=
  Cvs.WeilForm.ApproxWindowPositivityRH.rh_of_approx_windowPos fun ε hε x₀ => by
    obtain ⟨x, hx, hx₀⟩ := (h.and_eventually (eventually_ge_atTop x₀)).exists
    exact ⟨x, hx₀, fun φ => le_trans (by nlinarith [sq_nonneg ‖φ‖]) (hx φ)⟩

end Cvs.Route.NearPositivityProlateScale
