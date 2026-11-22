import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Digamma.WeierstrassFactorsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Complex Set Filter Topology Cvs.Digamma

namespace Cvs.Digamma

/-!
# The Weierstrass partial products are `GammaSeq` in disguise

`B93` showed the factors `(1 + z/(n+1)) e^{-z/(n+1)}` have a locally uniformly convergent
product.
-/

/-- The partial product, split into its rational and exponential halves. -/
theorem prod_one_add_wTerm (N : ℕ) (z : ℂ) :
    ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
        * Complex.exp (-(∑ n ∈ Finset.range N, z / ((n : ℂ) + 1))) := by
  have hfac : ∀ n : ℕ, (1 + wTerm n z)
      = (1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) := by
    intro n
    simp [wTerm]
  simp_rw [hfac, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.sum_neg_distrib]

/-- Each Weierstrass rational factor is nonzero away from the poles. -/
theorem one_add_div_ne_zero {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) (n : ℕ) :
    (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
  have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  intro h
  apply hz (n + 1)
  have h2 : ((n : ℂ) + 1) + z = 0 := by
    field_simp at h
    linear_combination h
  push_cast
  linear_combination h2

/-- **The finite bridge.** Dividing the factorial out of `GammaSeq`'s Pochhammer
denominator leaves exactly the Weierstrass rational factors. -/
theorem GammaSeq_mul_prod (N : ℕ) {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    z * Complex.GammaSeq z N * ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (N : ℂ) ^ z := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hne : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => Nat.cast_add_one_ne_zero n
  have hfacN : (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) = (Nat.factorial N : ℂ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      push_cast [Nat.factorial_succ]
      ring
  have hden : ∏ j ∈ Finset.range (N + 1), (z + j)
      = z * (Nat.factorial N : ℂ) * ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    have hstep : ∀ n ∈ Finset.range N, (z + ((n + 1 : ℕ) : ℂ))
        = ((n : ℂ) + 1) * (1 + z / ((n : ℂ) + 1)) := by
      intro n _
      field_simp
      push_cast
      ring
    rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, hfacN]
    push_cast
    ring
  have hPne : (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun n _ => one_add_div_ne_zero hz n
  have hFne : (Nat.factorial N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  simp only [Complex.GammaSeq]
  rw [hden]
  set P := ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)) with hPdef
  clear_value P
  have hDne : z * (Nat.factorial N : ℂ) * P ≠ 0 := mul_ne_zero (mul_ne_zero hz0 hFne) hPne
  rw [show z * ((N : ℂ) ^ z * (Nat.factorial N : ℂ) / (z * (Nat.factorial N : ℂ) * P)) * P
      = (z * P * ((N : ℂ) ^ z * (Nat.factorial N : ℂ))) / (z * (Nat.factorial N : ℂ) * P) from by
        ring, div_eq_iff hDne]
  ring

/-- The exponential half of the partial product is the harmonic number. -/
theorem sum_div_eq_harmonic (N : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range N, z / ((n : ℂ) + 1) = z * ((harmonic N : ℝ) : ℂ) := by
  rw [harmonic]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_mul_inv]

/-- **The bridge, with the prefactor absorbed.** For `N ≥ 1` the `N`-th partial
product times `z e^{γz} · GammaSeq z N` collapses to a single exponential whose
argument is `z(γ + log N − H_N)`. -/
theorem key_eq {N : ℕ} (hN : N ≠ 0) {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.GammaSeq z N
      * ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = Complex.exp (z * ((Real.eulerMascheroniConstant : ℂ) + (Real.log N : ℂ)
          - ((harmonic N : ℝ) : ℂ))) := by
  have hN0 : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [prod_one_add_wTerm, sum_div_eq_harmonic]
  rw [show z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.GammaSeq z N
      * ((∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
        * Complex.exp (-(z * ((harmonic N : ℝ) : ℂ))))
      = (z * Complex.GammaSeq z N * ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
        * (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * Complex.exp (-(z * ((harmonic N : ℝ) : ℂ)))) from by ring]
  rw [GammaSeq_mul_prod N hz, ← Complex.exp_add, Complex.cpow_def_of_ne_zero hN0,
    ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (N : ℂ) = (Real.log N : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg N), Complex.ofReal_natCast]
  rw [hlog]
  ring

/-- The prefactor tends to `1`, because `H_N − log N → γ`. -/
theorem tendsto_key_rhs (z : ℂ) :
    Tendsto (fun N : ℕ => Complex.exp (z * ((Real.eulerMascheroniConstant : ℂ)
      + (Real.log N : ℂ) - ((harmonic N : ℝ) : ℂ)))) atTop (𝓝 1) := by
  have hreal : Tendsto
      (fun N : ℕ => Real.eulerMascheroniConstant + Real.log N - (harmonic N : ℝ))
      atTop (𝓝 0) := by
    have h2 : Tendsto
        (fun N : ℕ => Real.eulerMascheroniConstant - ((harmonic N : ℝ) - Real.log N)) atTop
        (𝓝 (Real.eulerMascheroniConstant - Real.eulerMascheroniConstant)) :=
      tendsto_const_nhds.sub Real.tendsto_harmonic_sub_log
    rw [sub_self] at h2
    exact h2.congr fun N => by ring
  have hcast : Tendsto (fun N : ℕ =>
      ((Real.eulerMascheroniConstant + Real.log N - (harmonic N : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hreal
    simpa [Function.comp_def] using h
  have h4 : Tendsto (fun N : ℕ =>
      z * ((Real.eulerMascheroniConstant + Real.log N - (harmonic N : ℝ) : ℝ) : ℂ)) atTop
      (𝓝 (z * 0)) := hcast.const_mul z
  rw [mul_zero] at h4
  have hc : Tendsto (fun N : ℕ => z * ((Real.eulerMascheroniConstant : ℂ)
      + (Real.log N : ℂ) - ((harmonic N : ℝ) : ℂ))) atTop (𝓝 0) := by
    refine h4.congr fun N => ?_
    push_cast
    ring
  have hfin := (Complex.continuous_exp.tendsto 0).comp hc
  simpa [Function.comp_def] using hfin

/-- **The Weierstrass product for `Γ`.** `Γ(z) · z e^{γz} ∏ (1+z/n)e^{-z/n} = 1`
for every `z` off the poles. This is the product formula Mathlib does not have,
and the locally uniform convergence in `B93` is what makes it differentiable. -/
theorem Gamma_mul_weierstrass {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    Complex.Gamma z * (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
      * ∏' n : ℕ, (1 + wTerm n z)) = 1 := by
  have hprod : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + wTerm n z))) :=
    (Multipliable.hasProd_iff_tendsto_nat (multipliable_wTerm z)).mp (multipliable_wTerm z).hasProd
  have hlhs : Tendsto (fun N : ℕ => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
      * Complex.GammaSeq z N * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.Gamma z
        * ∏' n : ℕ, (1 + wTerm n z))) :=
    (tendsto_const_nhds.mul (Complex.GammaSeq_tendsto_Gamma z)).mul hprod
  have heq : Tendsto (fun N : ℕ => z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
      * Complex.GammaSeq z N * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop (𝓝 1) := by
    refine (tendsto_key_rhs z).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (key_eq hN hz).symm
  have hu := tendsto_nhds_unique hlhs heq
  have hcomm : Complex.Gamma z * (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
      * ∏' n : ℕ, (1 + wTerm n z))
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z) * Complex.Gamma z
        * ∏' n : ℕ, (1 + wTerm n z) := by ring
  rw [hcomm, hu]

end Cvs.Digamma
