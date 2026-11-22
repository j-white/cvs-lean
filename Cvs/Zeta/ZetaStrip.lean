import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Cvs.Zeta.GammaDecay
import Cvs.Zeta.ZetaGrowth

/-!
# Polynomial growth of `ζ` on a left vertical line

The right edge of the critical strip is easy: `ζ` is bounded on `Re s ≥ σ₀ > 1` by its
Dirichlet series (`Cvs.Zeta.norm_riemannZeta_le_of_re_le`).
-/

open Complex Real

namespace Cvs.Zeta

/-- `|cos z| ≤ e^{|Im z|}`: the elementary bound on the complex cosine. -/
theorem norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  rw [norm_div, Complex.norm_ofNat]
  have h1 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have hb1 : Real.exp (-z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs _)
  have hb2 : Real.exp z.im ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self _)
  have hsum := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  rw [h1, h2] at hsum
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **Polynomial growth of `ζ` on a left vertical line** , with no Stirling. -/
theorem exists_norm_riemannZeta_left_edge (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) - (k : ℂ) + t * I)‖
        ≤ C * (1 + |t| + k) ^ k := by
  set Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3 / 2 : ℝ) : ℂ) n‖ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨2 * (2 * π) ^ (-(1 / 2 + (k : ℝ))) * (Real.sqrt (2 * π) * Z), by positivity, ?_⟩
  intro t
  set s : ℂ := (1 / 2 : ℂ) + (k : ℂ) + (-t : ℝ) * I with hsdef
  -- real and imaginary parts of `s`
  have hsre : s.re = 1 / 2 + (k : ℝ) := by simp [hsdef]
  have hsim : s.im = -t := by simp [hsdef]
  -- the reflected point is the one in the statement
  have hrefl : (1 : ℂ) - s = (1 / 2 : ℂ) - (k : ℂ) + t * I := by
    rw [hsdef]; push_cast; ring
  -- side conditions for the functional equation
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hspos : (0 : ℝ) < s.re := by rw [hsre]; linarith
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have : s.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) < -(n : ℝ) := this ▸ hspos
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hs' : s ≠ 1 := by
    intro hn
    have : s.re = 1 := by rw [hn]; simp
    rw [hsre] at this; linarith
  rw [← hrefl, riemannZeta_one_sub hs hs']
  -- expand the norm of the product
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  -- the power factor is exactly a real rpow
  have hbase : ((2 * π : ℝ) : ℂ) = (2 * π : ℂ) := by push_cast; ring
  have hpow : ‖(2 * (π : ℂ)) ^ (-s)‖ = (2 * π) ^ (-(1 / 2 + (k : ℝ))) := by
    rw [← hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hsre]
  -- the Gamma factor
  have hgam : ‖Complex.Gamma s‖
      ≤ Real.sqrt (2 * π) * Real.exp (-(π * |t|) / 2) * (1 + |t| + k) ^ k := by
    have h := norm_Gamma_half_add_nat_add_I_mul_le k (-t)
    rw [abs_neg] at h
    exact h
  -- the cosine factor
  have hcos : ‖Complex.cos (π * s / 2)‖ ≤ Real.exp (π * |t| / 2) := by
    refine (norm_cos_le_exp_abs_im _).trans_eq ?_
    congr 1
    have : ((π : ℂ) * s / 2).im = π * (-t) / 2 := by
      simp [Complex.mul_im, hsim, hsre]
    rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  -- the zeta factor on the reflected line
  have hzeta : ‖riemannZeta s‖ ≤ Z := by
    refine norm_riemannZeta_le_of_re_le (σ₀ := 3 / 2) (by norm_num) ?_
    rw [hsre]; linarith
  -- assemble
  have hexp : Real.exp (-(π * |t|) / 2) * Real.exp (π * |t| / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -(π * |t|) / 2 + π * |t| / 2 = 0 by ring, Real.exp_zero]
  rw [hpow]
  calc 2 * (2 * π) ^ (-(1 / 2 + (k : ℝ))) * ‖Complex.Gamma s‖
          * ‖Complex.cos (π * s / 2)‖ * ‖riemannZeta s‖
      ≤ 2 * (2 * π) ^ (-(1 / 2 + (k : ℝ)))
          * (Real.sqrt (2 * π) * Real.exp (-(π * |t|) / 2) * (1 + |t| + k) ^ k)
          * Real.exp (π * |t| / 2) * Z := by
        gcongr
    _ = 2 * (2 * π) ^ (-(1 / 2 + (k : ℝ))) * (Real.sqrt (2 * π) * Z)
          * (1 + |t| + k) ^ k := by
        linear_combination (2 * (2 * π) ^ (-(1 / 2 + (k : ℝ))) * Real.sqrt (2 * π)
          * (1 + |t| + (k : ℝ)) ^ k * Z) * hexp

end Cvs.Zeta
