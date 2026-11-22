import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.RungWindowCouplingTail
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The coupling for a general even profile, through the regularised profile

The window of `G` equals the window of `regProfile c G = G − (2π/c)G(0)·β(·/a)`, which vanishes at
`0`; so for every `C²` even mean-zero `G` and `c ≥ 2π`, `weilθ(k_G, v) = −weilθ(τ_reg, v)` with
`τ_reg` the tail of the regularised profile.
-/

namespace Cvs.L2a.CouplingRegularisedProfile

open Real Set Filter Topology MeasureTheory
open Cvs.WeilForm.ThetaSpaceParseval (weilθ)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.WindowFormTailLimit (Tame regProfile)

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **The coupling identity for a general even profile.** -/
theorem coupling_eq_neg_tail_reg (hc : 2 * π ≤ c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hGi : ∫ s in (-1 : ℝ)..1, G s = 0)
    {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) :
    weilθ (window (2 * π / c) G) v = -weilθ (fullTail (psi c (regProfile c G))) v := by
  have hc0 : 0 < c := by linarith [pi_pos]
  have ha : 0 < 2 * π / c := by positivity
  have ha1 : 2 * π / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  set t := -(2 * π / c * G 0) with ht
  have hgt : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (regProfile c G)
      (G₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s) s := fun s hs =>
    (hg s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA c s).const_mul t)
  have hgt₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => G₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s)
      (G₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s) s := fun s hs =>
    (hg₁ s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA1 c s).const_mul t)
  have hgt₂c : ContinuousOn (fun s => G₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s) (uIcc (-1) 1) :=
    hg₂c.add (continuous_const.mul (Cvs.L2a.FullTailBilinearChannels.continuous_betaA2 c)).continuousOn
  have hevent : ∀ s ∈ Icc (-1 : ℝ) 1, regProfile c G (-s) = regProfile c G s := fun s hs => by
    simp only [regProfile, heven s hs, Cvs.L2a.WindowFormTailLimit.betaA_neg]
  have hGt0 : regProfile c G 0 = 0 := by
    rw [Cvs.L2a.WindowFormTailLimit.regProfile_eq hc0]; simp [Cvs.L2a.BetaProfilePoissonTail.beta_zero]
  have hGti : ∫ s in (-1 : ℝ)..1, regProfile c G s = 0 := by
    have hGc : Continuous fun s => t * Cvs.L2a.FullTailBilinearChannels.betaA c s := by
      unfold Cvs.L2a.FullTailBilinearChannels.betaA
      exact continuous_const.mul (continuous_const.mul
        (Cvs.L2a.BetaProfilePoissonTail.contDiff_beta.continuous.comp (continuous_id.div_const _)))
    have hGii : IntervalIntegrable G volume (-1) 1 :=
      ContinuousOn.intervalIntegrable fun s hs => (hg s hs).continuousAt.continuousWithinAt
    simp only [regProfile]
    rw [intervalIntegral.integral_add hGii (hGc.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hGi, Cvs.L2a.WindowFormTailLimit.integral_betaA hc]
    ring
  have hwin : window (2 * π / c) (regProfile c G) = window (2 * π / c) G := by
    rw [Cvs.L2a.WindowFormTailLimit.regProfile_eq hc0]
    exact Cvs.Xi.EImageWindowPoisson.window_sub_rescale ha ha1 G (G 0) fun y hy =>
      Cvs.L2a.BetaProfilePoissonTail.beta_of_one_le_abs (by rw [abs_of_pos (by linarith)]; exact hy)
  rw [← hwin]
  exact Cvs.L2a.RungWindowCouplingTail.coupling_eq_neg_tail hgt hgt₁ hgt₂c hevent hc0 hGt0 hGti hv

end Cvs.L2a.CouplingRegularisedProfile
