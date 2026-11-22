import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.GammaRLogDeriv

/-!
# Differentiating the two Gamma identities

`DigammaQuarterConstant` reduced `archScore 0` to `ψ(¼)` and `ψ(¼)` to two hypotheses: the logarithmic
derivatives of Mathlib's `Gamma_mul_Gamma_add_half` and `Gamma_mul_Gamma_one_sub`.
-/

namespace Cvs.Moments

open Complex
open scoped Real

/-- `Γ` at a point of positive real part. -/
theorem gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero fun m => Cvs.Zeta.ne_neg_nat_of_re_pos hs m

/-- **The shift.**  `logDeriv (Γ(·+c)) = ψ(·+c)`. -/
theorem logDeriv_gamma_shift {c s : ℂ} (hs : ∀ m : ℕ, s + c ≠ -m) :
    logDeriv (fun z : ℂ => Complex.Gamma (z + c)) s = Complex.digamma (s + c) := by
  have hΓ : Complex.Gamma (s + c) ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : DifferentiableAt ℂ Complex.Gamma (s + c) := Complex.differentiableAt_Gamma _ hs
  have h1 : HasDerivAt (fun z : ℂ => z + c) 1 s := by simpa using (hasDerivAt_id s).add_const c
  have hchain : HasDerivAt (fun z : ℂ => Complex.Gamma (z + c))
      (deriv Complex.Gamma (s + c) * 1) s := hd.hasDerivAt.comp s h1
  rw [logDeriv_apply, hchain.deriv, Complex.digamma, logDeriv_apply]
  field_simp

/-- **The doubling.**  `logDeriv (Γ(2·)) = 2ψ(2·)`. -/
theorem logDeriv_gamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -m) :
    logDeriv (fun z : ℂ => Complex.Gamma (2 * z)) s = 2 * Complex.digamma (2 * s) := by
  have hΓ : Complex.Gamma (2 * s) ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : DifferentiableAt ℂ Complex.Gamma (2 * s) := Complex.differentiableAt_Gamma _ hs
  have h1 : HasDerivAt (fun z : ℂ => 2 * z) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℂ)
  have hchain : HasDerivAt (fun z : ℂ => Complex.Gamma (2 * z))
      (deriv Complex.Gamma (2 * s) * 2) s := hd.hasDerivAt.comp s h1
  rw [logDeriv_apply, hchain.deriv, Complex.digamma, logDeriv_apply]
  field_simp

/-- **The reflection map.**  `logDeriv (Γ(1−·)) = −ψ(1−·)`. -/
theorem logDeriv_gamma_one_sub {s : ℂ} (hs : ∀ m : ℕ, 1 - s ≠ -m) :
    logDeriv (fun z : ℂ => Complex.Gamma (1 - z)) s = -Complex.digamma (1 - s) := by
  have hΓ : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : DifferentiableAt ℂ Complex.Gamma (1 - s) := Complex.differentiableAt_Gamma _ hs
  have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using ((hasDerivAt_id s).const_sub (1 : ℂ))
  have hchain : HasDerivAt (fun z : ℂ => Complex.Gamma (1 - z))
      (deriv Complex.Gamma (1 - s) * (-1)) s := hd.hasDerivAt.comp s h1
  rw [logDeriv_apply, hchain.deriv, Complex.digamma, logDeriv_apply]
  field_simp

/-- **The exponential factor.**  A constant base contributes `−2log 2`. -/
theorem logDeriv_two_cpow (s : ℂ) :
    logDeriv (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) s = -2 * Complex.log 2 := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hfun : (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z))
      = fun z : ℂ => Complex.exp (Complex.log 2 * (1 - 2 * z)) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero h2]
  have hlin : HasDerivAt (fun z : ℂ => Complex.log 2 * (1 - 2 * z))
      (Complex.log 2 * (-2)) s := by
    have := ((hasDerivAt_id s).const_mul (2 : ℂ)).const_sub (1 : ℂ)
    simpa using this.const_mul (Complex.log 2)
  have hexp := hlin.cexp
  rw [hfun, logDeriv_apply, hexp.deriv]
  have hne : Complex.exp (Complex.log 2 * (1 - 2 * s)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- **The duplication formula, differentiated.** -/
theorem digamma_duplication {s : ℂ} (h1 : 0 < s.re) (h2 : 0 < (s + 1 / 2).re)
    (h3 : 0 < (2 * s).re) :
    Complex.digamma s + Complex.digamma (s + 1 / 2)
      = 2 * Complex.digamma (2 * s) - 2 * Complex.log 2 := by
  have hn1 : ∀ m : ℕ, s ≠ -m := fun m => Cvs.Zeta.ne_neg_nat_of_re_pos h1 m
  have hn2 : ∀ m : ℕ, s + 1 / 2 ≠ -m := fun m => Cvs.Zeta.ne_neg_nat_of_re_pos h2 m
  have hn3 : ∀ m : ℕ, 2 * s ≠ -m := fun m => Cvs.Zeta.ne_neg_nat_of_re_pos h3 m
  have hfun : (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2))
      = fun z : ℂ => Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ) :=
    funext Complex.Gamma_mul_Gamma_add_half
  have hcong := congrArg (fun F : ℂ → ℂ => logDeriv F s) hfun
  -- left side
  have hdL1 : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma _ hn1
  have hdL2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1 / 2)) s := by
    have hstep : HasDerivAt (fun z : ℂ => z + (1 / 2 : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).add_const ((1 : ℂ) / 2)
    exact (((Complex.differentiableAt_Gamma _ hn2).hasDerivAt).comp s hstep).differentiableAt
  have hL : logDeriv (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) s
      = Complex.digamma s + Complex.digamma (s + 1 / 2) := by
    rw [logDeriv_fun_mul s (gamma_ne_zero_of_re_pos h1)
        (show Complex.Gamma (s + 1 / 2) ≠ 0 from Complex.Gamma_ne_zero hn2) hdL1 hdL2,
      logDeriv_gamma_shift hn2]
    rfl
  -- right side
  have hdR1 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (2 * z)) s := by
    have hstep : HasDerivAt (fun z : ℂ => 2 * z) 2 s := by
      simpa using (hasDerivAt_id s).const_mul (2 : ℂ)
    exact (((Complex.differentiableAt_Gamma _ hn3).hasDerivAt).comp s hstep).differentiableAt
  have hdR2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) s := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hfun2 : (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z))
        = fun z : ℂ => Complex.exp (Complex.log 2 * (1 - 2 * z)) := by
      funext z; rw [Complex.cpow_def_of_ne_zero h2]
    rw [hfun2]
    have hlin : HasDerivAt (fun z : ℂ => Complex.log 2 * (1 - 2 * z))
        (Complex.log 2 * (-2)) s := by
      have := ((hasDerivAt_id s).const_mul (2 : ℂ)).const_sub (1 : ℂ)
      simpa using this.const_mul (Complex.log 2)
    exact hlin.cexp.differentiableAt
  have hcpow_ne : ((2 : ℂ) ^ (1 - 2 * s)) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr ?_
    exact Or.inl two_ne_zero
  have hsqrt_ne : ((√π : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr ?_
    positivity
  have hR : logDeriv (fun z : ℂ =>
        Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ)) s
      = 2 * Complex.digamma (2 * s) - 2 * Complex.log 2 := by
    rw [logDeriv_mul_const s _ hsqrt_ne,
      logDeriv_fun_mul s (show Complex.Gamma (2 * s) ≠ 0 from Complex.Gamma_ne_zero hn3)
        hcpow_ne hdR1 hdR2,
      logDeriv_gamma_two_mul hn3, logDeriv_two_cpow]
    ring
  rw [hL, hR] at hcong
  exact hcong

/-- `logDeriv sin(π·) = π·cot(π·)`. -/
theorem logDeriv_sin_pi_mul {s : ℂ} (hs : Complex.sin ((π : ℂ) * s) ≠ 0) :
    logDeriv (fun z : ℂ => Complex.sin ((π : ℂ) * z)) s
      = (π : ℂ) * Complex.cos ((π : ℂ) * s) / Complex.sin ((π : ℂ) * s) := by
  have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) * z) ((π : ℂ)) s := by
    simpa using (hasDerivAt_id s).const_mul ((π : ℂ))
  have hchain : HasDerivAt (fun z : ℂ => Complex.sin ((π : ℂ) * z))
      (Complex.cos ((π : ℂ) * s) * (π : ℂ)) s := (Complex.hasDerivAt_sin _).comp s h1
  rw [logDeriv_apply, hchain.deriv]
  field_simp

/-- **The reflection formula, differentiated.** -/
theorem digamma_reflection {s : ℂ} (h1 : 0 < s.re) (h2 : 0 < (1 - s).re)
    (hsin : Complex.sin ((π : ℂ) * s) ≠ 0) :
    Complex.digamma s - Complex.digamma (1 - s)
      = -((π : ℂ) * Complex.cos ((π : ℂ) * s) / Complex.sin ((π : ℂ) * s)) := by
  have hn1 : ∀ m : ℕ, s ≠ -m := fun m => Cvs.Zeta.ne_neg_nat_of_re_pos h1 m
  have hn2 : ∀ m : ℕ, 1 - s ≠ -m := fun m => Cvs.Zeta.ne_neg_nat_of_re_pos h2 m
  have hfun : (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z))
      = fun z : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * z) :=
    funext Complex.Gamma_mul_Gamma_one_sub
  have hcong := congrArg (fun F : ℂ → ℂ => logDeriv F s) hfun
  have hdL1 : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma _ hn1
  have hdL2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (1 - z)) s := by
    have hstep : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub (1 : ℂ))
    exact (((Complex.differentiableAt_Gamma _ hn2).hasDerivAt).comp s hstep).differentiableAt
  have hL : logDeriv (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) s
      = Complex.digamma s - Complex.digamma (1 - s) := by
    rw [logDeriv_fun_mul s (gamma_ne_zero_of_re_pos h1)
        (show Complex.Gamma (1 - s) ≠ 0 from Complex.Gamma_ne_zero hn2) hdL1 hdL2,
      logDeriv_gamma_one_sub hn2]
    rfl
  have hdsin : DifferentiableAt ℂ (fun z : ℂ => Complex.sin ((π : ℂ) * z)) s := by
    have hstep : HasDerivAt (fun z : ℂ => (π : ℂ) * z) ((π : ℂ)) s := by
      simpa using (hasDerivAt_id s).const_mul ((π : ℂ))
    exact ((Complex.hasDerivAt_sin _).comp s hstep).differentiableAt
  have hpi : ((π : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hR : logDeriv (fun z : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * z)) s
      = -((π : ℂ) * Complex.cos ((π : ℂ) * s) / Complex.sin ((π : ℂ) * s)) := by
    rw [logDeriv_fun_div s hpi hsin (differentiableAt_const _) hdsin,
      logDeriv_sin_pi_mul hsin]
    simp [logDeriv_const]
  rw [hL, hR] at hcong
  exact hcong

/-- `sin(π/4) = cos(π/4) ≠ 0`, as complex numbers. -/
theorem sin_eq_cos_quarter :
    Complex.sin ((π : ℂ) * (1 / 4)) = Complex.cos ((π : ℂ) * (1 / 4))
      ∧ Complex.sin ((π : ℂ) * (1 / 4)) ≠ 0 := by
  have harg : (π : ℂ) * (1 / 4) = ((Real.pi / 4 : ℝ) : ℂ) := by push_cast; ring
  have hs : Complex.sin ((π : ℂ) * (1 / 4)) = ((Real.sin (Real.pi / 4) : ℝ) : ℂ) := by
    rw [harg, ← Complex.ofReal_sin]
  have hc : Complex.cos ((π : ℂ) * (1 / 4)) = ((Real.cos (Real.pi / 4) : ℝ) : ℂ) := by
    rw [harg, ← Complex.ofReal_cos]
  refine ⟨?_, ?_⟩
  · rw [hs, hc, Real.sin_pi_div_four, Real.cos_pi_div_four]
  · rw [hs, Real.sin_pi_div_four]
    refine Complex.ofReal_ne_zero.mpr ?_
    positivity

/-- **The two identities at `s = ¼`**, in the form `DigammaQuarterConstant` asks for. -/
theorem reflection_at_quarter :
    Complex.digamma (1 / 4) - Complex.digamma (3 / 4) = -(π : ℂ) := by
  obtain ⟨heq, hne⟩ := sin_eq_cos_quarter
  have h := digamma_reflection (s := (1 / 4 : ℂ)) (by norm_num) (by norm_num) hne
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by ring] at h
  rw [h, ← heq, mul_div_assoc, div_self hne, mul_one]

theorem duplication_at_quarter :
    2 * Complex.digamma (1 / 2)
      = 2 * Complex.log 2 + Complex.digamma (1 / 4) + Complex.digamma (3 / 4) := by
  have h := digamma_duplication (s := (1 / 4 : ℂ)) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 : ℂ) / 4 + 1 / 2 = 3 / 4 by ring, show (2 : ℂ) * (1 / 4) = 1 / 2 by ring] at h
  linear_combination -h

end Cvs.Moments
