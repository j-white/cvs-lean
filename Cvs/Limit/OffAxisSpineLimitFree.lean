import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.Hurwitz

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-axis spine with the limit left free

Approximants that are zero-free off the coordinate axes and converge there to a limit which is
nowhere locally zero and which vanishes at every off-axis zero of `Ξ` give RH. On the recentred
ground transforms this is the same statement with the family named.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.OffAxisSpineLimitFree
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit Cvs.Limit.ZeroFreeApproximantsRH

/-- **RH from off-axis convergence to a limit that sees `Ξ`'s off-axis zeros.** `offAxes` has four
components, so the limit is asked to be nowhere locally zero rather than non-zero at one point. -/
theorem riemannHypothesis_of_limit_offAxes_sees (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hFd : ∀ n, DifferentiableOn ℂ (F n) offAxes)
    (hFne : ∀ n, ∀ z ∈ offAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop offAxes)
    (hfnot : ∀ z ∈ offAxes, ¬ (∀ᶠ w in 𝓝 z, f w = 0))
    (hsees : ∀ z ∈ offAxes, Xi z = 0 → f z = 0) :
    RiemannHypothesis := by
  have hXi : ∀ z ∈ offAxes, Xi z ≠ 0 := by
    intro z hz hXz
    exact Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn
      isOpen_offAxes hz hFd hFne hconv (hfnot z hz) (hsees z hz hXz)
  intro s hs hnt hs1
  by_cases hstrip : 0 < s.re ∧ s.re < 1
  · exact re_eq_half_of_offAxes hXi hs hstrip.1 hstrip.2
  · exact absurd (trivial_of_zero_off_strip hs hstrip hs1) hnt

/-- **The recentred ground spine off the axes, with the limit left free.** -/
theorem riemannHypothesis_of_ground_centred_offAxes_sees {L : ℕ → ℝ} (hL : ∀ n, 0 < L n)
    (P R N : ℕ → ℕ) (c : ℕ → ℂ) (hc : ∀ n, c n ≠ 0) (f : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z)
      f atTop offAxes)
    (hfnot : ∀ z ∈ offAxes, ¬ (∀ᶠ w in 𝓝 z, f w = 0))
    (hsees : ∀ z ∈ offAxes, Xi z = 0 → f z = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_limit_offAxes_sees _ f
    (fun n => ((differentiable_const (c n)).mul
      (Cvs.Finite.RecentredTransform.differentiable_cgtransform (P n) (R n) (hL n) (N n))).differentiableOn)
    (fun n _z hz => mul_ne_zero (hc n)
      (Cvs.Finite.RecentredTransform.cgtransform_ne_zero (P n) (R n) (hL n) (N n) hz))
    hconv hfnot hsees

end Cvs.Limit.OffAxisSpineLimitFree
