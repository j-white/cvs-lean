import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Digamma.WeierstrassFactorsConverge
import Cvs.Zeta.Digamma.WeierstrassGammaSeq

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Complex Set Filter Topology Cvs.Digamma Cvs.Digamma

namespace Cvs.Digamma

/-!
# Differentiating the product

`B93` gives locally uniform convergence and `B94` identifies the limit.
-/

/-- The logarithmic derivative of one Weierstrass factor. -/
theorem logDeriv_wFactor (n : ℕ) {z : ℂ} (hz : (1 + z / ((n : ℂ) + 1)) ≠ 0) :
    logDeriv (fun w => 1 + wTerm n w) z = 1 / (z + (n : ℂ) + 1) - 1 / ((n : ℂ) + 1) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hfun : (fun w => 1 + wTerm n w)
      = fun w => (1 + w / ((n : ℂ) + 1)) * Complex.exp (-(w / ((n : ℂ) + 1))) := by
    funext w
    simp [wTerm]
  rw [hfun]
  have hd1 : HasDerivAt (fun w : ℂ => 1 + w / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    simpa using ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
  have hd2 : HasDerivAt (fun w : ℂ => Complex.exp (-(w / ((n : ℂ) + 1))))
      (Complex.exp (-(z / ((n : ℂ) + 1))) * (-(1 / ((n : ℂ) + 1)))) z := by
    have h := (((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg).cexp
    simpa using h
  rw [logDeriv_fun_mul (f := fun w : ℂ => 1 + w / ((n : ℂ) + 1))
      (g := fun w : ℂ => Complex.exp (-(w / ((n : ℂ) + 1)))) z hz
      (Complex.exp_ne_zero _) hd1.differentiableAt hd2.differentiableAt,
    logDeriv_apply, logDeriv_apply, hd1.deriv, hd2.deriv]
  rw [mul_comm, mul_div_assoc, div_self (Complex.exp_ne_zero _), mul_one]
  field_simp
  ring

/-- The logarithmic derivative of the `N`-th partial product. -/
theorem logDeriv_prod_wTerm (N : ℕ) {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    logDeriv (fun w => ∏ n ∈ Finset.range N, (1 + wTerm n w)) z
      = ∑ n ∈ Finset.range N, (1 / (z + (n : ℂ) + 1) - 1 / ((n : ℂ) + 1)) := by
  have hne : ∀ n ∈ Finset.range N, (fun w => 1 + wTerm n w) z ≠ 0 := by
    intro n _
    have h := one_add_div_ne_zero hz n
    have hfun : (fun w => 1 + wTerm n w) z = (1 + z / ((n : ℂ) + 1))
        * Complex.exp (-(z / ((n : ℂ) + 1))) := by simp [wTerm]
    rw [hfun]
    exact mul_ne_zero h (Complex.exp_ne_zero _)
  have hdiff : ∀ n ∈ Finset.range N, DifferentiableAt ℂ (fun w => 1 + wTerm n w) z := by
    intro n _
    simp only [wTerm]
    fun_prop
  rw [logDeriv_fun_prod (f := fun (n : ℕ) (w : ℂ) => 1 + wTerm n w) hne hdiff]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact logDeriv_wFactor n (one_add_div_ne_zero hz n)

/-- The tail product is nonzero: `B94` forces it. -/
theorem tprod_ne_zero {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    (∏' n : ℕ, (1 + wTerm n z)) ≠ 0 := by
  intro h
  have hb := Gamma_mul_weierstrass hz
  rw [h] at hb
  simp at hb

/-- The partial products are entire. -/
theorem differentiable_prod (N : ℕ) :
    Differentiable ℂ (fun w : ℂ => ∏ n ∈ Finset.range N, (1 + wTerm n w)) := by
  simp only [wTerm]
  fun_prop

/-- **The series converges to the logarithmic derivative of the product.** This is
the step a pointwise limit cannot take, and the reason `B93` was proved. -/
theorem tendsto_logDeriv_series {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / (z + (n : ℂ) + 1) - 1 / ((n : ℂ) + 1)))
      atTop (𝓝 (logDeriv (fun w => ∏' n : ℕ, (1 + wTerm n w)) z)) := by
  have h := Complex.logDeriv_tendsto (s := univ) isOpen_univ (mem_univ z)
    hasProdLocallyUniformlyOn_wTerm.tendstoLocallyUniformlyOn_finsetRange
    (by filter_upwards with N using (differentiable_prod N).differentiableOn)
    (tprod_ne_zero hz)
  refine h.congr fun N => ?_
  exact logDeriv_prod_wTerm N hz

/-- On the right half-plane the product is the reciprocal of `z e^{γz} Γ(z)`. -/
theorem tprod_eq_inv {z : ℂ} (hz : 0 < z.re) :
    (∏' n : ℕ, (1 + wTerm n z))
      = 1 / (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.Gamma z) := by
  have hpole : ∀ m : ℕ, z ≠ -m := by
    intro m h
    rw [h] at hz
    simp only [neg_re, Complex.natCast_re, neg_pos] at hz
    exact absurd hz (not_lt.mpr (Nat.cast_nonneg m))
  have hb := Gamma_mul_weierstrass hpole
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hQ : z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.Gamma z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hz0 (Complex.exp_ne_zero _)) hG
  rw [eq_div_iff hQ]
  linear_combination hb

/-- **The logarithmic derivative of the Weierstrass product, in closed form.** -/
theorem logDeriv_tprod_eq {z : ℂ} (hz : 0 < z.re) :
    logDeriv (fun w => ∏' n : ℕ, (1 + wTerm n w)) z
      = -(1 / z + (Real.eulerMascheroniConstant : ℂ) + Complex.digamma z) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : (fun w => ∏' n : ℕ, (1 + wTerm n w))
      =ᶠ[𝓝 z] (fun w => 1 / (w * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w)
        * Complex.Gamma w)) := by
    filter_upwards [hopen.mem_nhds hz] with w hw using tprod_eq_inv hw
  rw [(logDeriv_congr_nhds heq).eq_of_nhds]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hpole : ∀ m : ℕ, z ≠ -m := by
    intro m h
    rw [h] at hz
    simp only [neg_re, Complex.natCast_re, neg_pos] at hz
    exact absurd hz (not_lt.mpr (Nat.cast_nonneg m))
  have hdG : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hpole
  have hdexp : HasDerivAt (fun w : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w))
      (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * (Real.eulerMascheroniConstant : ℂ)) z := by
    simpa using ((hasDerivAt_id z).const_mul (Real.eulerMascheroniConstant : ℂ)).cexp
  have hdid : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have hQ1 : z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) ≠ 0 :=
    mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hlog1 : logDeriv (fun w : ℂ => w * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w)) z
      = 1 / z + (Real.eulerMascheroniConstant : ℂ) := by
    rw [logDeriv_fun_mul (f := fun w : ℂ => w)
      (g := fun w : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w)) z hz0
      (Complex.exp_ne_zero _) hdid.differentiableAt hdexp.differentiableAt,
      logDeriv_apply, logDeriv_apply, hdid.deriv, hdexp.deriv]
    rw [mul_comm, mul_div_assoc, div_self (Complex.exp_ne_zero _), mul_one]
  have hlog2 : logDeriv (fun w : ℂ => w * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w)
      * Complex.Gamma w) z
      = 1 / z + (Real.eulerMascheroniConstant : ℂ) + Complex.digamma z := by
    rw [logDeriv_fun_mul (f := fun w : ℂ => w * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w))
      (g := Complex.Gamma) z hQ1 hG
      (hdid.differentiableAt.mul hdexp.differentiableAt) hdG, hlog1, Complex.digamma_def]
  have hQfull : z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.Gamma z ≠ 0 :=
    mul_ne_zero hQ1 hG
  have hdQ : DifferentiableAt ℂ (fun w : ℂ => w
      * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w) * Complex.Gamma w) z :=
    (hdid.differentiableAt.mul hdexp.differentiableAt).mul hdG
  rw [logDeriv_fun_div (f := fun _ : ℂ => (1 : ℂ))
      (g := fun w : ℂ => w * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * w)
        * Complex.Gamma w) z one_ne_zero hQfull (differentiableAt_const 1) hdQ, hlog2]
  simp [logDeriv_const]

/-- On the right half-plane there are no poles. -/
theorem ne_neg_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [neg_re, Complex.natCast_re, neg_pos] at hz
  exact absurd hz (not_lt.mpr (Nat.cast_nonneg m))

/-- The digamma terms are `O(n^{-2})`, hence absolutely summable. -/
theorem summable_digamma_terms {z : ℂ} (hz : 0 < z.re) :
    Summable fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1) := by
  refine (summable_const_div_sq ‖z‖).of_norm_bounded fun n => ?_
  have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hnr : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := norm_natCast_add_one n
  have hz1 : z + (n : ℂ) + 1 ≠ 0 := by
    intro h
    have hre : (z + (n : ℂ) + 1).re = z.re + n + 1 := by simp
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlow : (n : ℝ) + 1 ≤ ‖z + (n : ℂ) + 1‖ := by
    have h1 : (z + (n : ℂ) + 1).re ≤ ‖z + (n : ℂ) + 1‖ := Complex.re_le_norm _
    have h2 : (z + (n : ℂ) + 1).re = z.re + n + 1 := by simp
    rw [h2] at h1
    linarith
  have hsplit : 1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1)
      = z / (((n : ℂ) + 1) * (z + (n : ℂ) + 1)) := by
    field_simp
    ring
  rw [hsplit, norm_div, norm_mul, hnr]
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have hden : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖ := by nlinarith [hlow]
  exact div_le_div_of_nonneg_left (norm_nonneg z) hpos hden

/-- **The digamma series.** `ψ(z) + γ + 1/z = ∑ (1/(n+1) − 1/(z+n+1))` on the right half-plane —
the classical expansion, now machine-checked. -/
theorem hasSum_digamma {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  refine (Summable.hasSum_iff_tendsto_nat (summable_digamma_terms hz)).mpr ?_
  have h := tendsto_logDeriv_series (ne_neg_of_re_pos hz)
  rw [logDeriv_tprod_eq hz] at h
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1))) atTop
      (𝓝 (-(-(1 / z + (Real.eulerMascheroniConstant : ℂ) + Complex.digamma z)))) := by
    refine h.neg.congr fun N => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have h3 : -(-(1 / z + (Real.eulerMascheroniConstant : ℂ) + Complex.digamma z))
      = Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z := by ring
  rw [h3] at h2
  exact h2

end Cvs.Digamma
