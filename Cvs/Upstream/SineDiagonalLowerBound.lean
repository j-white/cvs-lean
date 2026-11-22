import Mathlib
import Cvs.Finite.ReducedSecularPolynomial

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sine from below on the diagonals, and the Euler factors in the window's variable

Where `u²` has non-positive real part every Euler factor has modulus at least one, so the first
`N` factors bound the sine from below.  With `u = z L / (2 π)` those factors are
`(z L / 2) ∏ (1 - z² / q_j)` over the squared frequencies `q_j` of the window.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset Filter Topology

namespace Cvs.Upstream.SineDiagonalLowerBound
open Cvs.ZeroCounting

open Cvs.Finite.ReducedSecularPolynomial

/-- **An Euler factor has modulus at least one where `u²` has non-positive real part.** -/
theorem one_le_norm_factor {u : ℂ} (hu : (u ^ 2).re ≤ 0) (j : ℕ) :
    1 ≤ ‖(1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2‖ := by
  have hden : ((j : ℂ) + 1) ^ 2 = ((((j : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hre : ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2).re = 1 - (u ^ 2).re / ((j : ℝ) + 1) ^ 2 := by
    rw [hden, Complex.sub_re, Complex.one_re, Complex.div_ofReal_re]
  have hpos : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
  have hle : (u ^ 2).re / ((j : ℝ) + 1) ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hpos.le
  calc (1 : ℝ) ≤ ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2).re := by rw [hre]; linarith
    _ ≤ |((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2).re| := le_abs_self _
    _ ≤ ‖(1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2‖ := Complex.abs_re_le_norm _

/-- **On the diagonals the first `N` Euler factors bound the sine from below.** -/
theorem le_norm_sin {u : ℂ} (hu : (u ^ 2).re ≤ 0) (N : ℕ) :
    ‖(π : ℂ) * u * ∏ j ∈ range N, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)‖
      ≤ ‖Complex.sin (π * u)‖ := by
  refine ge_of_tendsto (Complex.tendsto_euler_sin_prod u).norm
    (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  rw [← Finset.prod_range_mul_prod_Ico _ hn, ← mul_assoc]
  have htail : 1 ≤ ‖∏ j ∈ Ico N n, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)‖ := by
    rw [Complex.norm_prod]
    calc (1 : ℝ) = ∏ _j ∈ Ico N n, (1 : ℝ) := by rw [Finset.prod_const_one]
      _ ≤ ∏ j ∈ Ico N n, ‖(1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2‖ :=
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun j _ => one_le_norm_factor hu j
  set A : ℂ := (π : ℂ) * u * ∏ j ∈ range N, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)
  calc ‖A‖ = ‖A‖ * 1 := by ring
    _ ≤ ‖A‖ * ‖∏ j ∈ Ico N n, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)‖ :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = ‖A * ∏ j ∈ Ico N n, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)‖ := (norm_mul _ _).symm

/-- **The Euler factors in the window's variable.** -/
theorem euler_factors_eq {L : ℝ} (hL : L ≠ 0) (N : ℕ) (z : ℂ) :
    (π : ℂ) * (z * L / (2 * π))
        * ∏ j ∈ range N, ((1 : ℂ) - (z * L / (2 * π)) ^ 2 / ((j : ℂ) + 1) ^ 2)
      = z * L / 2 * ∏ j : Fin N, ((1 : ℂ) - z ^ 2 / qf L N j) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  rw [← Fin.prod_univ_eq_prod_range
    (fun j : ℕ => (1 : ℂ) - (z * L / (2 * π)) ^ 2 / ((j : ℂ) + 1) ^ 2) N]
  congr 1
  · field_simp
  · refine Finset.prod_congr rfl fun j _ => ?_
    have hj : ((j : ℕ) : ℂ) + 1 ≠ 0 := by
      have : (((j : ℕ) : ℝ) + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    unfold qf
    push_cast
    field_simp

end Cvs.Upstream.SineDiagonalLowerBound
