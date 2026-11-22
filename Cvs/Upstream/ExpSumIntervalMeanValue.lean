import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The mean value of an exponential sum over an interval

Expanding `‖Σ b_n e^{iλ_n g}‖²` and integrating term by term gives
`∫_{a₁}^{a₂} ‖Σ b_n e^{iλ_n g}‖² dg ≤ Σ_{m,n} ‖b_m‖‖b_n‖ (a₂ − a₁ if m = n, else 2/|λ_m − λ_n|)`; for the frequencies
`λ_n = log n − L/2`, `1 ≤ n ≤ x`, and real `b_n`, this is at most `(a₂ − a₁ + 4x(1 + log x)) Σ b_n²`.
-/

noncomputable section

open Real Set MeasureTheory Complex intervalIntegral

namespace Cvs.Upstream.ExpSumIntervalMeanValue

/-- `|∫_{a₁}^{a₂} e^{iδg} dg| ≤ 2/|δ|` for `δ ≠ 0`. -/
theorem norm_integral_exp_le {δ : ℝ} (hδ : δ ≠ 0) (a₁ a₂ : ℝ) :
    ‖∫ g in a₁..a₂, Complex.exp (δ * I * g)‖ ≤ 2 / |δ| := by
  have hc : (δ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hδ) I_ne_zero
  rw [integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  refine div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (le_of_eq ?_)) (abs_nonneg _)
  have k : ∀ y : ℝ, ‖Complex.exp ((δ : ℂ) * I * y)‖ = 1 := fun y => by
    rw [show (δ : ℂ) * I * y = ((δ * y : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [k, k]; norm_num

/-- `‖z‖² = Re(z z̄)` for a sum, expanded into the double sum. -/
theorem norm_sq_sum {ι : Type*} (s : Finset ι) (b : ι → ℂ) (fr : ι → ℝ) (g : ℝ) :
    ‖∑ n ∈ s, b n * Complex.exp (fr n * I * g)‖ ^ 2
      = (∑ m ∈ s, ∑ n ∈ s, b m * (starRingEnd ℂ) (b n) * Complex.exp ((fr m - fr n : ℝ) * I * g)).re := by
  set z := ∑ n ∈ s, b n * Complex.exp (fr n * I * g) with hz
  have h1 : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  rw [h1, hz, map_sum, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have : (starRingEnd ℂ) ((fr n : ℂ) * I * g) = -((fr n : ℂ) * I * g) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [this]
  have e : Complex.exp ((fr m : ℂ) * I * g) * Complex.exp (-((fr n : ℂ) * I * g))
      = Complex.exp (((fr m - fr n : ℝ) : ℂ) * I * g) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e]; ring

/-- **The mean value inequality** for an exponential sum with distinct frequencies. -/
theorem integral_norm_sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℂ) (fr : ι → ℝ)
    (hfr : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → fr m ≠ fr n) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) :
    ∫ g in a₁..a₂, ‖∑ n ∈ s, b n * Complex.exp (fr n * I * g)‖ ^ 2
      ≤ ∑ m ∈ s, ∑ n ∈ s, ‖b m‖ * ‖b n‖ * (if m = n then a₂ - a₁ else 2 / |fr m - fr n|) := by
  have hcont : ∀ m n, IntervalIntegrable (fun g : ℝ => b m * (starRingEnd ℂ) (b n)
      * Complex.exp ((fr m - fr n : ℝ) * I * g)) volume a₁ a₂ := fun m n =>
    (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  have hI : ∀ g : ℝ, ‖∑ n ∈ s, b n * Complex.exp (fr n * I * g)‖ ^ 2
      = RCLike.re (∑ m ∈ s, ∑ n ∈ s, b m * (starRingEnd ℂ) (b n) * Complex.exp ((fr m - fr n : ℝ) * I * g)) :=
    fun g => norm_sq_sum s b fr g
  simp_rw [hI]
  have hsum : IntervalIntegrable (fun g : ℝ => ∑ m ∈ s, ∑ n ∈ s, b m * (starRingEnd ℂ) (b n)
      * Complex.exp ((fr m - fr n : ℝ) * I * g)) volume a₁ a₂ :=
    (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  have hre := Complex.reCLM.intervalIntegral_comp_comm hsum
  simp only [Complex.reCLM_apply] at hre
  rw [show (fun g : ℝ => RCLike.re (∑ m ∈ s, ∑ n ∈ s, b m * (starRingEnd ℂ) (b n)
      * Complex.exp ((fr m - fr n : ℝ) * I * g))) = fun g : ℝ => (∑ m ∈ s, ∑ n ∈ s, b m * (starRingEnd ℂ) (b n)
      * Complex.exp ((fr m - fr n : ℝ) * I * g)).re from rfl, hre]
  refine (Complex.re_le_norm _).trans ?_
  rw [intervalIntegral.integral_finsetSum fun m _ => (Continuous.continuousOn (by fun_prop)).intervalIntegrable]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [intervalIntegral.integral_finsetSum fun n _ => hcont m n]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, Complex.norm_conj]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  split_ifs with h
  · subst h
    simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      real_smul, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  · exact norm_integral_exp_le (sub_ne_zero.2 (hfr m hm n hn h)) a₁ a₂

/-- `|m − n|/x ≤ |log m − log n|` for `1 ≤ m, n ≤ x`. -/
theorem abs_sub_div_le_abs_log_sub {x m n : ℕ} (hm : m ∈ Finset.Icc 1 x) (hn : n ∈ Finset.Icc 1 x) :
    |(m : ℝ) - n| / x ≤ |Real.log m - Real.log n| := by
  obtain ⟨hm1, hmx⟩ := Finset.mem_Icc.1 hm
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.1 hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmx' : (m : ℝ) ≤ x := by exact_mod_cast hmx
  have hnx' : (n : ℝ) ≤ x := by exact_mod_cast hnx
  have hx : (0 : ℝ) < x := lt_of_lt_of_le hmr hmx'
  -- `log a − log b ≥ (a − b)/a` for `a ≥ b > 0`
  have key : ∀ a b : ℝ, 0 < b → b ≤ a → a ≤ x → (a - b) / x ≤ Real.log a - Real.log b := by
    intro a b hb hba hax
    have ha : 0 < a := lt_of_lt_of_le hb hba
    have h1 : 1 - b / a ≤ Real.log (a / b) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
      rwa [inv_div] at this
    rw [Real.log_div ha.ne' hb.ne'] at h1
    have h2 : (a - b) / x ≤ (a - b) / a := div_le_div_of_nonneg_left (by linarith) ha hax
    have h3 : (a - b) / a = 1 - b / a := by field_simp
    linarith
  rcases le_total (n : ℝ) m with h | h
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [Real.log_le_log hnr h])]
    exact key m n hnr h hmx'
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [Real.log_le_log hmr h])]
    have := key n m hmr h hnx'
    rw [neg_sub, neg_sub]; linarith

/-- `Σ_{n ∈ [1, x], n ≠ m} 1/|m − n| ≤ 2(1 + log x)`. -/
theorem sum_inv_abs_sub_le {x m : ℕ} (hm : m ∈ Finset.Icc 1 x) :
    ∑ n ∈ Finset.Icc 1 x, (if m = n then 0 else 1 / |(m : ℝ) - n|) ≤ 2 * (1 + Real.log x) := by
  obtain ⟨hm1, hmx⟩ := Finset.mem_Icc.1 hm
  -- split into `n < m` and `n > m`, each a harmonic sum of length below `x`
  have hH : ((harmonic x : ℚ) : ℝ) ≤ 1 + Real.log x := harmonic_le_one_add_log x
  have hsplit : ∑ n ∈ Finset.Icc 1 x, (if m = n then 0 else 1 / |(m : ℝ) - n|)
      ≤ ∑ k ∈ Finset.Icc 1 x, 1 / (k : ℝ) + ∑ k ∈ Finset.Icc 1 x, 1 / (k : ℝ) := by
    have hle : ∀ n ∈ Finset.Icc 1 x, (if m = n then 0 else 1 / |(m : ℝ) - n|)
        ≤ (if n < m then 1 / ((m - n : ℕ) : ℝ) else 0) + (if m < n then 1 / ((n - m : ℕ) : ℝ) else 0) := by
      intro n _
      rcases lt_trichotomy n m with h | h | h
      · have hnm : (n : ℝ) < m := by exact_mod_cast h
        rw [if_neg (by omega), if_pos h, if_neg (by omega), add_zero, Nat.cast_sub h.le,
          abs_of_pos (sub_pos.2 hnm)]
      · subst h; simp
      · have hmn : (m : ℝ) < n := by exact_mod_cast h
        rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add, Nat.cast_sub h.le,
          abs_of_neg (sub_neg.2 hmn), neg_sub]
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_filter]
      have hinj : Set.InjOn (fun n => m - n) ((Finset.Icc 1 x).filter (· < m) : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
        simp only at hab; omega
      rw [← Finset.sum_image (f := fun k : ℕ => 1 / (k : ℝ)) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
    · rw [← Finset.sum_filter]
      have hinj : Set.InjOn (fun n => n - m) ((Finset.Icc 1 x).filter (m < ·) : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
        simp only at hab; omega
      rw [← Finset.sum_image (f := fun k : ℕ => 1 / (k : ℝ)) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
  have hh : ∑ k ∈ Finset.Icc 1 x, 1 / (k : ℝ) = ((harmonic x : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  rw [hh] at hsplit
  linarith

/-- **The mean value inequality for the frequencies `log n`**: for real `b_n`, `1 ≤ n ≤ x`,
`∫_{a₁}^{a₂} ‖Σ b_n e^{i(log n − L/2)g}‖² dg ≤ (a₂ − a₁ + 4x(1 + log x)) Σ b_n²`. -/
theorem integral_norm_sq_logSum_le {x : ℕ} (b : ℕ → ℝ) (L : ℝ) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) :
    ∫ g in a₁..a₂, ‖∑ n ∈ Finset.Icc 1 x, (b n : ℂ) * Complex.exp ((Real.log n - L) * I * g)‖ ^ 2
      ≤ (a₂ - a₁ + 4 * x * (1 + Real.log x)) * ∑ n ∈ Finset.Icc 1 x, b n ^ 2 := by
  have hfr : ∀ m ∈ Finset.Icc 1 x, ∀ n ∈ Finset.Icc 1 x, m ≠ n → Real.log m - L ≠ Real.log n - L := by
    intro m hm n hn hmn h
    have h' : Real.log m = Real.log n := by linarith
    have hm1 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    exact hmn (by exact_mod_cast Real.log_injOn_pos hm1 hn1 h')
  have hM := integral_norm_sq_sum_le (Finset.Icc 1 x) (fun n => (b n : ℂ)) (fun n => Real.log n - L) hfr ha
  refine (le_of_eq_of_le ?_ hM).trans ?_
  · simp only [Complex.ofReal_sub]
  simp only [Complex.norm_real, Real.norm_eq_abs, sub_sub_sub_cancel_right]
  have hx0 : ∀ m ∈ Finset.Icc 1 x, (0 : ℝ) < x := fun m hm => by
    have := (Finset.mem_Icc.1 hm); exact_mod_cast (by omega : 0 < x)
  -- each term is at most `(b_m² + b_n²)/2` times its kernel; the kernel row sums are `a₂ − a₁ + 4x(1 + log x)`
  have hterm : ∀ m ∈ Finset.Icc 1 x, ∀ n ∈ Finset.Icc 1 x,
      |b m| * |b n| * (if m = n then a₂ - a₁ else 2 / |Real.log m - Real.log n|)
        ≤ (b m ^ 2 + b n ^ 2) / 2 * (if m = n then a₂ - a₁ else 2 * x * (1 / |(m : ℝ) - n|)) := by
    intro m hm n hn
    have hab : |b m| * |b n| ≤ (b m ^ 2 + b n ^ 2) / 2 := by
      nlinarith [sq_nonneg (|b m| - |b n|), sq_abs (b m), sq_abs (b n)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right hab (by linarith)
    · have hne : (m : ℝ) ≠ n := by exact_mod_cast h
      have hpos : 0 < |(m : ℝ) - n| := abs_pos.2 (sub_ne_zero.2 hne)
      have hl := abs_sub_div_le_abs_log_sub hm hn
      have hx := hx0 m hm
      have hk : 2 / |Real.log m - Real.log n| ≤ 2 * x * (1 / |(m : ℝ) - n|) := by
        rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hl)]
        rw [div_le_iff₀ hx] at hl
        field_simp
        nlinarith
      exact mul_le_mul hab hk (by positivity) (by positivity)
  refine (Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hterm m hm n hn).trans ?_
  -- symmetrise
  have hsym : ∑ m ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
      (b m ^ 2 + b n ^ 2) / 2 * (if m = n then a₂ - a₁ else 2 * x * (1 / |(m : ℝ) - n|))
      = ∑ m ∈ Finset.Icc 1 x, b m ^ 2 * ∑ n ∈ Finset.Icc 1 x,
          (if m = n then a₂ - a₁ else 2 * x * (1 / |(m : ℝ) - n|)) := by
    have hk : ∀ m n : ℕ, (if m = n then a₂ - a₁ else 2 * x * (1 / |(m : ℝ) - n|))
        = (if n = m then a₂ - a₁ else 2 * x * (1 / |(n : ℝ) - m|)) := fun m n => by
      by_cases h : m = n
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]
    simp_rw [add_div, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun m n => b n ^ 2 / 2 * _)]
    simp_rw [hk _ _]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hsym, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hrow : ∑ n ∈ Finset.Icc 1 x, (if m = n then a₂ - a₁ else 2 * x * (1 / |(m : ℝ) - n|))
      = (a₂ - a₁) + 2 * x * ∑ n ∈ Finset.Icc 1 x, (if m = n then 0 else 1 / |(m : ℝ) - n|) := by
    have e : ∀ n : ℕ, (if m = n then a₂ - a₁ else 2 * x * (1 / |(m : ℝ) - n|))
        = (if m = n then a₂ - a₁ else 0) + 2 * x * (if m = n then 0 else 1 / |(m : ℝ) - n|) := fun n => by
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun n _ => e n, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hm,
      Finset.mul_sum]
  rw [hrow]
  have := sum_inv_abs_sub_le hm
  have hx := (hx0 m hm).le
  nlinarith

end Cvs.Upstream.ExpSumIntervalMeanValue

end
