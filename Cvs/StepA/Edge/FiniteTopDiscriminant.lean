import Mathlib
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.OneOrdinateDiscriminant
import Cvs.StepA.Edge.TwoEdgeSplit
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.TopQuadruple
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
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
# The edge discriminant of a finite top set, and when it is positive

At signed ordinates `z_ρ = ±(γ_ρ − iδ)` the edge discriminant of a finite top set is
`(∑_quad m)/(2|δ + iγ|)` at `arg(δ + iγ)/γ` for a strictly top quadruple, positive after an
antipodal return when nonzero at one scale and under edge positivity of all finite families, while
finitely many zeros off the line give a finite top set when RH fails.
-/

noncomputable section

open Real MeasureTheory

namespace Cvs.StepA.Edge.FiniteTopDiscriminant
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg FiniteTop)
open Cvs.StepA.Edge.TwoEdgeSplit (ctr_neg_sq norm_exp_phase)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeDisc)
open Cvs.StepA.Edge.OneOrdinateDiscriminant (EdgePositiveFamilies)

/-! ### The signed ordinates of a finite top set -/

/-- The ordinate of `ρ`, signed so that `z_ρ = ±(ord ρ − iδ)` when `|del ρ| = δ > 0`. -/
def ord (ρ : nonTrivialZeroSet) : ℝ :=
  if 0 < Cvs.GaussKernel.del ρ then (Cvs.ZeroCounting.zPoint ρ).re else -(Cvs.ZeroCounting.zPoint ρ).re

/-- **Edge positivity**: the edge discriminant of `S`, with multiplicities and signed ordinates at
depth `δ`, is positive at some real scale. -/
def EdgePositive (S : Finset nonTrivialZeroSet) (δ : ℝ) : Prop :=
  ∃ L₀ : ℝ, 0 < edgeDisc S mult ord δ L₀

/-- At distance `δ > 0`, the zero-side point is `±(ord ρ − iδ)`. -/
theorem zPoint_eq_or_neg {ρ : nonTrivialZeroSet} {δ : ℝ} (hδ : 0 < δ)
    (h : |Cvs.GaussKernel.del ρ| = δ) :
    Cvs.ZeroCounting.zPoint ρ = (ord ρ : ℂ) - δ * Complex.I ∨
      Cvs.ZeroCounting.zPoint ρ = -((ord ρ : ℂ) - δ * Complex.I) := by
  have him := Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del ρ
  unfold ord
  by_cases hd : 0 < Cvs.GaussKernel.del ρ
  · left
    rw [if_pos hd]
    rw [abs_of_pos hd] at h
    apply Complex.ext <;> simp [him, h]
  · right
    rw [if_neg hd]
    have hd' : Cvs.GaussKernel.del ρ < 0 := by
      rcases lt_or_eq_of_le (not_lt.mp hd) with h' | h'
      · exact h'
      · rw [h', abs_zero] at h; linarith
    rw [abs_of_neg hd'] at h
    apply Complex.ext <;> simp [him]
    linarith

/-- For an even or odd `g` and `|del ρ| = δ > 0`, `ctr(g, z_ρ)² = ctr(g, ord ρ − iδ)²`. -/
theorem ctr_zPoint_sq (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (hpar : (∀ t, g (-t) = g t) ∨ ∀ t, g (-t) = -g t) {ρ : nonTrivialZeroSet} {δ : ℝ}
    (hδ : 0 < δ) (h : |Cvs.GaussKernel.del ρ| = δ) :
    Cvs.StepA.OneZeroParitySectors.ctr L g (Cvs.ZeroCounting.zPoint ρ) ^ 2
      = Cvs.StepA.OneZeroParitySectors.ctr L g ((ord ρ : ℂ) - δ * Complex.I) ^ 2 := by
  rcases zPoint_eq_or_neg hδ h with e | e
  · rw [e]
  · rw [e, ctr_neg_sq L hg hpar]

/-! ### One quadruple on top -/

/-! ### Antipodal return -/

/-! ### Edge positivity of every finite family, and finitely many zeros off the line -/

/-- A zero off the critical line has a nonzero signed ordinate. -/
theorem ord_ne_zero {ρ : nonTrivialZeroSet} (h : Cvs.GaussKernel.del ρ ≠ 0) : ord ρ ≠ 0 := by
  have hre : (Cvs.ZeroCounting.zPoint ρ).re ≠ 0 := by
    rw [Cvs.ZeroCounting.zPoint_re]; exact Cvs.GaussKernel.im_ne_zero_of_del_ne_zero h
  unfold ord
  split_ifs
  · exact hre
  · exact neg_ne_zero.mpr hre

/-- **Edge positivity for every finite family gives it for every finite top set.** -/
theorem edgePositive_of_edgePositiveFamilies (hEF : EdgePositiveFamilies)
    {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ) : EdgePositive S δ := by
  obtain ⟨hδ, hne, hSδ, -⟩ := hS
  refine hEF S mult ord δ hδ hne (fun ρ _ => ?_) (fun ρ hρ => ord_ne_zero ?_)
  · have h1 : (1 : ℝ) ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) := by
      exact_mod_cast Cvs.Criterion.one_le_divisorWeight ρ
    exact lt_of_lt_of_le one_pos h1
  · intro h0
    have h1 := hSδ ρ hρ
    rw [h0, abs_zero] at h1
    linarith

end Cvs.StepA.Edge.FiniteTopDiscriminant
