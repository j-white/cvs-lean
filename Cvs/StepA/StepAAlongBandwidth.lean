import Mathlib
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.InfinitelyManyOffLattice
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.StepACriterion
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step (a) along one small bandwidth is an RH criterion with no condition under RH

Along the mode count `N = ⌈ΩL/2π⌉₊` with `0 < Ω < c`, `c` at most every zero ordinate, RH gives step
(a) at every large integer scale outright, and a top set with a band top gap at `Ω` refutes it. So RH
holds iff step (a) holds along that curve, given only that a failure of RH leaves a top set with a band
top gap there; with `DepthToZero` on the right, a band top gap for every finite top set suffices.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.StepA.StepAAlongBandwidth
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.OddAboveDisplacement (OddAbove)
open Cvs.StepA.Edge.TopSetCriterion (TopSet BandTopGap frequently_not_oddAbove_of_bandGap tendsto_natCeil)

/-- Step (a) along the mode count `M`: `OddAbove` at `(x, M(log x))` for every integer `x ≥ x₀`. -/
def StepAAlong (M : ℝ → ℕ) (x₀ : ℕ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∀ hx : 0 < Real.log x,
    OddAbove ⌈Real.exp (Real.log x)⌉₊ ⌈Real.log x / Real.log 2⌉₊ (Real.log x) hx (M (Real.log x))

/-- The bandwidth of `⌈ΩL/2π⌉₊` modes is below `Ω + 2π/L`, for `Ω ≥ 0` and `L > 0`. -/
theorem bandwidth_natCeil_lt {Ω L : ℝ} (hΩ : 0 ≤ Ω) (hL : 0 < L) :
    2 * π * (⌈Ω * L / (2 * π)⌉₊ : ℕ) / L < Ω + 2 * π / L := by
  have h2π : 0 < 2 * π := by positivity
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Ω * L / (2 * π) by positivity)
  rw [div_lt_iff₀ hL]
  calc 2 * π * (⌈Ω * L / (2 * π)⌉₊ : ℕ) < 2 * π * (Ω * L / (2 * π) + 1) :=
        mul_lt_mul_of_pos_left hc h2π
    _ = (Ω + 2 * π / L) * L := by field_simp

/-- **RH gives step (a) along a small bandwidth**: for `0 ≤ Ω < c` with `c` at most every zero
ordinate, RH gives `OddAbove` at `(x, ⌈Ω log x/2π⌉₊)` for every large integer `x`. -/
theorem exists_stepAAlong_of_RH (hRH : RiemannHypothesis) {Ω c : ℝ} (hΩ0 : 0 ≤ Ω) (hΩc : Ω < c)
    (hgap : ∀ ρ : nonTrivialZeroSet, c ≤ |(ρ : ℂ).im|) :
    ∃ x₀ : ℕ, StepAAlong (fun L => ⌈Ω * L / (2 * π)⌉₊) x₀ := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (hlog.eventually (eventually_gt_atTop (2 * π / (c - Ω))))
  refine ⟨x₀, fun x hx hlx => ?_⟩
  have hL := hx₀ x hx
  have hgap' : 0 < c - Ω := by linarith
  have hπL : 2 * π / Real.log x < c - Ω := by
    rw [div_lt_iff₀ hlx]
    rw [div_lt_iff₀ hgap'] at hL
    linarith
  exact Cvs.StepA.StepACriterion.oddAbove_of_RH_of_bandwidth hRH hlx hgap
    ((bandwidth_natCeil_lt hΩ0 hlx).trans (by linarith))
    (Cvs.StepA.InfinitelyManyOffLattice.natCast_lt_encard_of_RH hRH hlx _)

/-- **A top set with a band top gap at `Ω > 0` refutes step (a) along `⌈ΩL/2π⌉₊`.** -/
theorem not_stepAAlong_of_bandTopGap {S : Set nonTrivialZeroSet} {δ Ω : ℝ}
    (hS : TopSet S δ) (hΩ : 0 < Ω) (hG : BandTopGap S δ Ω) (x₀ : ℕ) :
    ¬ StepAAlong (fun L => ⌈Ω * L / (2 * π)⌉₊) x₀ := by
  intro hA
  obtain ⟨c, hc, hfreq⟩ := hG
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hM0 : ∀ᶠ L in atTop, 0 < ⌈Ω * L / (2 * π)⌉₊ :=
    (tendsto_natCeil hΩ).eventually (eventually_gt_atTop 0)
  have hbad := frequently_not_oddAbove_of_bandGap hS (Cvs.StepA.RestEnvelopeSmall.natCeil_isBigO Ω) hM0
    hc hlog hfreq
  obtain ⟨x, hxbad, hx, hpos⟩ := (hbad.and_eventually ((eventually_ge_atTop x₀).and
    (hlog.eventually (eventually_gt_atTop 0)))).exists
  exact hxbad hpos (hA x hx hpos)

end Cvs.StepA.StepAAlongBandwidth
