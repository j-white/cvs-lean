import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.Hurwitz
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ZeroFreeHeightFive

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The spine needs the limit only on the critical strip, off the axes

A zero of `ζ` with `0 < Re s < 1` sits at `z = −i(s − 1/2)` with `|Im z| < 1/2`, so Hurwitz is needed
only on `criticalOffAxes = {z | Re z ≠ 0, Im z ≠ 0, |Im z| < 1/2}`. Uniform convergence on a closed
strip `|Im z| ≤ a` with `a ≥ 1/2` gives the locally uniform convergence the route asks for there.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.CriticalStripOffAxes
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit Cvs.Limit.ZeroFreeApproximantsRH

/-- The open critical strip of `z = -i(s - 1/2)`, with both coordinate axes removed. -/
def criticalOffAxes : Set ℂ := {z : ℂ | z.re ≠ 0 ∧ z.im ≠ 0 ∧ |z.im| < 1 / 2}

theorem criticalOffAxes_subset : criticalOffAxes ⊆ offAxes := fun _ hz => ⟨hz.1, hz.2.1⟩

theorem isOpen_criticalOffAxes : IsOpen criticalOffAxes := by
  have h3 : IsOpen {z : ℂ | |z.im| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have : criticalOffAxes = offAxes ∩ {z : ℂ | |z.im| < 1 / 2} := by
    ext z; simp [criticalOffAxes, offAxes, and_assoc]
  rw [this]; exact isOpen_offAxes.inter h3

/-- A strip zero of `ζ` lies on the line once `Ξ` is zero-free on `criticalOffAxes`. -/
theorem re_eq_half_of_criticalOffAxes (hXi : ∀ z ∈ criticalOffAxes, Xi z ≠ 0)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hξ : Cvs.Zeta.riemannXi ρ = 0 :=
    (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hρ1).mpr hρ
  have hXz : Xi (zOf ρ) = 0 := by
    unfold Xi; rw [half_add_I_mul_zOf]; exact hξ
  have hre : (zOf ρ).re ≠ 0 := by
    rw [zOf_re]; intro h
    have := Cvs.ZeroFree.abs_im_gt_five_of_riemannXi_eq_zero hξ
    rw [h] at this; simp at this; linarith
  have hstrip : |(zOf ρ).im| < 1 / 2 := by
    rw [zOf_im, abs_lt]; constructor <;> linarith
  by_contra hne
  have him : (zOf ρ).im ≠ 0 := by
    rw [zOf_im]; intro h; apply hne; linarith
  exact hXi _ ⟨hre, him, hstrip⟩ hXz

/-- **`Ξ` is zero-free on the critical strip off the axes** when approximants zero-free there converge
to it there. -/
theorem Xi_ne_zero_of_limit_criticalOffAxes (F : ℕ → ℂ → ℂ)
    (hFd : ∀ n, DifferentiableOn ℂ (F n) criticalOffAxes)
    (hFne : ∀ n, ∀ z ∈ criticalOffAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F Xi atTop criticalOffAxes) :
    ∀ z ∈ criticalOffAxes, Xi z ≠ 0 := fun z hz =>
  Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn
    isOpen_criticalOffAxes hz hFd hFne hconv (not_eventually_zero z)

/-- **The ground route, asking for convergence only on the critical strip off the axes.** -/
theorem riemannHypothesis_of_ground_centred_strip {L : ℕ → ℝ} (hL : ∀ n, 0 < L n)
    (P R N : ℕ → ℕ) (c : ℕ → ℂ) (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z)
      Xi atTop criticalOffAxes) :
    RiemannHypothesis := by
  have hXi := Xi_ne_zero_of_limit_criticalOffAxes _
    (fun n => ((differentiable_const (c n)).mul
      (Cvs.Finite.RecentredTransform.differentiable_cgtransform (P n) (R n) (hL n) (N n))).differentiableOn)
    (fun n _z hz => mul_ne_zero (hc n)
      (Cvs.Finite.RecentredTransform.cgtransform_ne_zero (P n) (R n) (hL n) (N n)
        (criticalOffAxes_subset hz)))
    hconv
  intro s hs hnt hs1
  by_cases hstrip : 0 < s.re ∧ s.re < 1
  · exact re_eq_half_of_criticalOffAxes hXi hs hstrip.1 hstrip.2
  · exact absurd (trivial_of_zero_off_strip hs hstrip hs1) hnt

end Cvs.Limit.CriticalStripOffAxes
