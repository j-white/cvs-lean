import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-
The `Γ` decay on a vertical line, without Stirling.

`MATHLIB.md` §7 names Stirling on vertical lines as a missing ingredient for the
strip bound on `ζ`.  For an *upper* bound it is not needed: Euler's reflection
formula gives the modulus on the critical line **exactly**,

    `|Γ(½+it)|² = Γ(½+it)·Γ(½−it) = π / sin(π(½+it)) = π / cosh(πt)`,

using `Γ(z̄) = conj Γ(z)` to recognise the left side as a squared modulus.  Then
`cosh x ≥ e^{|x|}/2` turns it into the decay `|Γ(½+it)| ≤ √(2π)·e^{−π|t|/2}` —
which is what Stirling would have been invoked for, and is what cancels the
`e^{π|t|/2}` growth of `cos(πw/2)` in the functional equation.

Mathlib's `Γ` asymptotics are Bohr–Mollerup, so this route sidesteps the gap
rather than filling it.  What it does *not* give is the polynomial factor
`|t|^{σ−1/2}`, which needs the shift `Γ(z+1) = zΓ(z)` off the critical line.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- **`|Γ(½+it)|² = π/cosh(πt)`, exactly.** Euler's reflection at `z = ½+it` gives `Γ(½+it)Γ(½−it)
= π/sin(π(½+it))`, and `Γ(½−it)` is the conjugate of `Γ(½+it)`, so the left side is
`|Γ(½+it)|²`. -/
theorem normSq_Gamma_half_add_I_mul (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hconj : (starRingEnd ℂ) (1 / 2 + (t : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) := by
    simp [Complex.ext_iff]
    ring
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + (t : ℂ) * I)
  rw [← hconj, Complex.Gamma_conj] at hrefl
  -- the left side is the squared modulus
  have hleft : Complex.Gamma (1 / 2 + (t : ℂ) * I)
      * (starRingEnd ℂ) (Complex.Gamma (1 / 2 + (t : ℂ) * I))
      = ((‖Complex.Gamma (1 / 2 + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hleft] at hrefl
  -- the right side is `π / cosh(πt)`
  have hsin : Complex.sin (Real.pi * (1 / 2 + (t : ℂ) * I))
      = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    have h : (Real.pi : ℂ) * (1 / 2 + (t : ℂ) * I)
        = ((Real.pi * t : ℝ) : ℂ) * I + (Real.pi : ℂ) / 2 := by push_cast; ring
    rw [h, Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  rw [hsin] at hrefl
  exact_mod_cast hrefl

/-- **`|Γ(½+it)| ≤ √(2π)·e^{−π|t|/2}`.** The exponential decay Stirling is usually invoked for,
obtained instead from the exact reflection identity and `cosh x ≥ e^{|x|}/2`. -/
theorem norm_Gamma_half_add_I_mul_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2) := by
  have hπ := Real.pi_pos
  have heven : Real.cosh (Real.pi * t) = Real.cosh (Real.pi * |t|) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hlow : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * |t|) := by
    rw [Real.cosh_eq]
    have := (Real.exp_pos (-(Real.pi * |t|))).le
    linarith
  have hcpos : 0 < Real.cosh (Real.pi * t) := by
    rw [heven]; exact lt_of_lt_of_le (by positivity) hlow
  -- compare the squares
  have hsq : ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2
      ≤ (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)) ^ 2 := by
    rw [normSq_Gamma_half_add_I_mul, mul_pow, Real.sq_sqrt (by positivity),
      ← Real.exp_nat_mul]
    have hexp : Real.exp (2 * (-(Real.pi * |t|) / 2)) = Real.exp (-(Real.pi * |t|)) := by
      congr 1; ring
    rw [show ((2 : ℕ) : ℝ) * (-(Real.pi * |t|) / 2) = 2 * (-(Real.pi * |t|) / 2) by norm_num,
      hexp, Real.exp_neg, heven]
    have hE : (0 : ℝ) < Real.exp (Real.pi * |t|) := Real.exp_pos _
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hlow)]
    have hEinv : Real.exp (Real.pi * |t|) * (Real.exp (Real.pi * |t|))⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hE)
    nlinarith [mul_nonneg (le_of_lt (inv_pos.mpr hE)) (sub_nonneg.mpr hlow),
      hEinv, hπ, inv_pos.mpr hE, hlow]
  have h1 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2) := by
    positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h1 two_ne_zero).mp hsq

/-! ### Off the critical line -/

/-- **`Γ` off the critical line: decay times a polynomial.** `Γ(z+1) = zΓ(z)` moves the exact
critical-line bound to `σ = ½+k`, each step costing one factor `|½+j+it| ≤ ½+j+|t|`. -/
theorem norm_Gamma_half_add_nat_add_I_mul_le (k : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (k : ℂ) + t * I)‖
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)
        * (1 + |t| + k) ^ k := by
  induction k with
  | zero => simpa using norm_Gamma_half_add_I_mul_le t
  | succ n ih =>
      have hre : ((1 / 2 : ℂ) + (n : ℂ) + t * I).re = 1 / 2 + n := by simp
      have hne : ((1 / 2 : ℂ) + (n : ℂ) + t * I) ≠ 0 := by
        intro hcon
        rw [hcon] at hre
        simp at hre
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hstep : Complex.Gamma ((1 / 2 : ℂ) + ((n : ℂ) + 1) + t * I)
          = ((1 / 2 : ℂ) + (n : ℂ) + t * I)
            * Complex.Gamma ((1 / 2 : ℂ) + (n : ℂ) + t * I) := by
        rw [show (1 / 2 : ℂ) + ((n : ℂ) + 1) + t * I
            = ((1 / 2 : ℂ) + (n : ℂ) + t * I) + 1 by ring]
        exact Complex.Gamma_add_one _ hne
      have hfac : ‖(1 / 2 : ℂ) + (n : ℂ) + t * I‖ ≤ 1 + |t| + n := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have h1 : |((1 / 2 : ℂ) + (n : ℂ) + t * I).re| = 1 / 2 + n := by
          rw [hre]; rw [abs_of_nonneg (by positivity)]
        have h2 : |((1 / 2 : ℂ) + (n : ℂ) + t * I).im| = |t| := by simp
        rw [h1, h2]; linarith
      push_cast
      rw [hstep, norm_mul]
      have hbnn : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)
          * (1 + |t| + n) ^ n := by positivity
      calc ‖(1 / 2 : ℂ) + (n : ℂ) + t * I‖
              * ‖Complex.Gamma ((1 / 2 : ℂ) + (n : ℂ) + t * I)‖
          ≤ (1 + |t| + n)
              * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)
                 * (1 + |t| + n) ^ n) :=
            mul_le_mul hfac ih (norm_nonneg _) (by positivity)
        _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)
              * (1 + |t| + (n + 1)) ^ (n + 1) := by
            have hmono : (1 + |t| + (n : ℝ)) ^ (n + 1)
                ≤ (1 + |t| + ((n : ℝ) + 1)) ^ (n + 1) := by
              exact pow_le_pow_left₀ (by positivity) (by linarith) _
            calc (1 + |t| + (n : ℝ))
                  * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)
                     * (1 + |t| + (n : ℝ)) ^ n)
                = Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)
                    * (1 + |t| + (n : ℝ)) ^ (n + 1) := by ring
              _ ≤ _ := by
                  refine mul_le_mul_of_nonneg_left hmono (by positivity)

end Cvs.Zeta
