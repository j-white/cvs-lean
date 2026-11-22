import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.ExponentialSumTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The division vector: `sq_o(ξ) = ξ²·sq_x(ξ)` at every `ξ ∈ ℂ`

A test vanishing at both ends of the window has `sq_{f'}(ξ) = ξ²·sq_f(ξ)` at every `ξ`. The cosine
polynomial of the division vector `x = xdiv o` of an odd `o` is such a test, with derivative minus the
sine polynomial of `o`; so `sq_o = ξ²·sq_x`, and in the dilated variable `G_o(Lz) = z²·F_x(Lz)`.
-/

noncomputable section

open Real Matrix Cvs.Finite.SymmetricModeSet Cvs.Finite.OddEigenvectorResolvent Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.DivisionVector
open Cvs.ZeroCounting

/-! ### The square transform of a derivative -/

/-- The window transform of a derivative at `0` is the increment of the test. -/
theorem windowTransform_zero_of_hasDerivAt {L : ℝ} {f g : ℝ → ℂ}
    (hf : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f (g s) s) (hg : Continuous g) :
    Cvs.Detection.windowTransform L g 0 = f L - f 0 := by
  unfold Cvs.Detection.windowTransform
  simp only [mul_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hf (hg.intervalIntegrable 0 L)

/-- **The square transform of a derivative**: for `f` vanishing at `0` and `L` with continuous
derivative `g`, `sq_g(ξ) = ξ²·sq_f(ξ)` at every `ξ ∈ ℂ`. -/
theorem sqTransform_deriv {L : ℝ} {f g : ℝ → ℂ}
    (hf : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f (g s) s) (hg : Continuous g)
    (h0 : f 0 = 0) (hLz : f L = 0) (ξ : ℂ) :
    Cvs.Detection.sqTransform L g ξ = ξ ^ 2 * Cvs.Detection.sqTransform L f ξ := by
  unfold Cvs.Detection.sqTransform
  by_cases hξ : ξ = 0
  · subst hξ
    rw [neg_zero, windowTransform_zero_of_hasDerivAt hf hg, h0, hLz]
    ring
  · have hI : ∀ η : ℂ, η ≠ 0 → Cvs.Detection.windowTransform L g η
        = η * Complex.I * Cvs.Detection.windowTransform L f η := by
      intro η hη
      rw [Cvs.Detection.windowTransform_ibp hf hg h0 hLz hη]
      have : η * Complex.I ≠ 0 := mul_ne_zero hη Complex.I_ne_zero
      field_simp
    rw [hI ξ hξ, hI (-ξ) (neg_ne_zero.mpr hξ)]
    linear_combination (-(ξ ^ 2 * Cvs.Detection.windowTransform L f ξ
      * Cvs.Detection.windowTransform L f (-ξ))) * Complex.I_sq

/-- The square transform does not see the sign of the test. -/
theorem sqTransform_neg (L : ℝ) (f : ℝ → ℂ) (ξ : ℂ) :
    Cvs.Detection.sqTransform L (fun s => -f s) ξ = Cvs.Detection.sqTransform L f ξ := by
  unfold Cvs.Detection.sqTransform
  have h : ∀ η, Cvs.Detection.windowTransform L (fun s => -f s) η
      = -Cvs.Detection.windowTransform L f η := by
    intro η
    have := Cvs.Detection.windowTransform_const_mul L (-1) f η
    simpa using this
  rw [h, h]
  ring

/-! ### The division vector's cosine polynomial -/

variable {L : ℝ} {N : ℕ}

/-- The derivative of the division vector's cosine polynomial is minus `o`'s sine polynomial. -/
theorem cosPoly'_xdiv (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (y : ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly' L (mode N) (xdiv L N o) y
      = -Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o y := by
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly' Cvs.Finite.OddSectorZeroSide.sinePoly
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← om_mul_xdiv hL N hodd i]
  ring

theorem cosPoly_xdiv_zero (L : ℝ) (o : Idx N → ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o) 0 = 0 := by
  rw [Cvs.Finite.EvenSectorZeroSide.cosPoly_zero, sum_xdiv]

theorem cosPoly_xdiv_L (hL : 0 < L) (o : Idx N → ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o) L = 0 := by
  rw [Cvs.Finite.EvenSectorZeroSide.cosPoly_L hL, sum_xdiv]

/-- The division vector's cosine polynomial is an antiderivative of minus `o`'s sine polynomial. -/
theorem hasDerivAt_cf_cosPoly_xdiv (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i)
    (s : ℝ) :
    HasDerivAt (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)))
      (-cf (Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o) s) s := by
  have h := (Cvs.Finite.EvenSectorZeroSide.hasDerivAt_cosPoly L (mode N) (xdiv L N o) s).ofReal_comp
  rw [cosPoly'_xdiv hL hodd s, Complex.ofReal_neg] at h
  exact h

/-! ### The division identity -/

/-- **The odd square transform is `ξ²` times the division vector's, at every `ξ ∈ ℂ`.** -/
theorem sqTransform_sinePoly_eq_sq_mul (hL : 0 < L) {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (ξ : ℂ) :
    Cvs.Detection.sqTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o)) ξ
      = ξ ^ 2 * Cvs.Detection.sqTransform L
          (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o))) ξ := by
  have hc : Continuous fun s => -cf (Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o) s :=
    (Complex.continuous_ofReal.comp (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly L (mode N) o)).neg
  have h := sqTransform_deriv (L := L) (fun s _ => hasDerivAt_cf_cosPoly_xdiv hL hodd s) hc
    (by simp [cf, cosPoly_xdiv_zero]) (by simp [cf, cosPoly_xdiv_L hL]) ξ
  rw [sqTransform_neg] at h
  exact h

end Cvs.Finite.DivisionVector
