import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The aliasing identity for a `C²` profile on `[−1, 1]`

For `f` of class `C²` on `[−1, 1]` with `f(−1) = f(1)`, the `2`-periodic extension has Fourier coefficients
`c_k = O(k^{−2})` (two integrations by parts, Mathlib's `fourierCoeffOn_of_hasDerivAt`), so its Fourier series
converges everywhere; summing it over the `2N` points `−1 + n/N` keeps only `k ∈ 2Nℤ`:
`(1/2N)Σ_{n<2N} f(−1 + n/N) = ½∫_{−1}^{1} f + Σ_{m ≥ 1} ∫_{−1}^{1} f(t) cos(2πNmt) dt`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology intervalIntegral

namespace Cvs.Upstream.PeriodicAliasingIdentity

/-- `‖fourier n x‖ = 1`. -/
theorem norm_fourier_apply {T : ℝ} (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- A Fourier coefficient on `[a, b]` is at most the sup of the function. -/
theorem norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ t ∈ uIcc a b, ‖f t‖ ≤ M) (n : ℤ) : ‖fourierCoeffOn hab f n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have hba : 0 < b - a := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := M)
    (f := fun x => fourier (-n) (x : AddCircle (b - a)) • f x) (fun t ht => by
      rw [norm_smul, norm_fourier_apply, one_mul]
      exact hM t (uIoc_subset_uIcc ht))
  rw [abs_of_pos hba] at h
  calc ‖(1 / (b - a) : ℝ)‖ * ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x‖
      ≤ (1 / (b - a)) * (M * (b - a)) := by
        refine mul_le_mul (le_of_eq ?_) h (norm_nonneg _) (by positivity)
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ = M := by field_simp

section coeff

variable {f f₁ f₂ : ℝ → ℂ}

/-- One integration by parts on `[−1, 1]`: `‖c_n(f)‖ ≤ (‖f(1) − f(−1)‖ + 2‖c_n(f′)‖)/(2π|n|)`. -/
theorem norm_coeff_le_deriv (hab : (-1 : ℝ) < -1 + 2) {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ t) t) (hi : IntervalIntegrable f₁ volume (-1) 1) :
    ‖fourierCoeffOn hab f n‖ ≤ (‖f 1 - f (-1)‖ + 2 * ‖fourierCoeffOn hab f₁ n‖) / (2 * π * |(n : ℝ)|) := by
  have e2 : (-1 : ℝ) + 2 = 1 := by norm_num
  have hf' : ∀ t ∈ uIcc (-1 : ℝ) (-1 + 2), HasDerivAt f (f₁ t) t := by rw [e2]; exact hf
  have hi' : IntervalIntegrable f₁ volume (-1) (-1 + 2) := by rw [e2]; exact hi
  rw [fourierCoeffOn_of_hasDerivAt hab hn hf' hi']
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hden : ‖(-2 * π * I * n : ℂ)‖ = 2 * π * |(n : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast]
    ring
  have hden0 : 0 < 2 * π * |(n : ℝ)| := by positivity
  rw [norm_mul, norm_div, norm_one, hden, one_div, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hden0]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_fourier_apply, one_mul, norm_mul]
  have h1 : f (-1 + 2) = f 1 := by norm_num
  have h2 : ‖(((-1 + 2 : ℝ) : ℂ) - ((-1 : ℝ) : ℂ))‖ = 2 := by norm_num
  rw [h1, h2]

/-- **The coefficients decay like `n^{−2}`**: for `n ≠ 0`, `‖c_n(f)‖ ≤ (‖f₁(1) − f₁(−1)‖ + 2M₂)/(2π²n²)`. -/
theorem norm_coeff_le (hab : (-1 : ℝ) < -1 + 2) {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (hf₂ : ContinuousOn f₂ (uIcc (-1) 1)) (hper : f (-1) = f 1) {M₂ : ℝ}
    (hM : ∀ t ∈ uIcc (-1 : ℝ) 1, ‖f₂ t‖ ≤ M₂) :
    ‖fourierCoeffOn hab f n‖ ≤ (‖f₁ 1 - f₁ (-1)‖ + 2 * M₂) / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) := by
  have e2 : (-1 : ℝ) + 2 = 1 := by norm_num
  have hi₁ : IntervalIntegrable f₁ volume (-1) 1 :=
    ContinuousOn.intervalIntegrable fun t ht => (hf₁ t ht).continuousAt.continuousWithinAt
  have hi₂ : IntervalIntegrable f₂ volume (-1) 1 := hf₂.intervalIntegrable
  have h1 := norm_coeff_le_deriv hab hn hf hi₁
  have h2 := norm_coeff_le_deriv hab hn hf₁ hi₂
  have hM' : ∀ t ∈ uIcc (-1 : ℝ) (-1 + 2), ‖f₂ t‖ ≤ M₂ := by rw [e2]; exact hM
  have h3 := norm_fourierCoeffOn_le hab hM' n
  rw [hper, sub_self, norm_zero, zero_add] at h1
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hd : 0 < 2 * π * |(n : ℝ)| := by positivity
  have hM0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM 1 (by simp))
  calc ‖fourierCoeffOn hab f n‖ ≤ 2 * ‖fourierCoeffOn hab f₁ n‖ / (2 * π * |(n : ℝ)|) := h1
    _ ≤ 2 * ((‖f₁ 1 - f₁ (-1)‖ + 2 * M₂) / (2 * π * |(n : ℝ)|)) / (2 * π * |(n : ℝ)|) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = (‖f₁ 1 - f₁ (-1)‖ + 2 * M₂) / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) := by
        rw [← sq_abs (n : ℝ)]
        field_simp

end coeff

section poisson

variable {f f₁ f₂ : ℝ → ℂ}

/-- The period `2` is positive. -/
scoped instance fact_two_pos : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/-- The `n`-th Fourier coefficient `c_k = ½∫_{−1}^{1} e^{−iπkt} f(t) dt` of the `2`-periodic extension. -/
def coeffK (f : ℝ → ℂ) (k : ℤ) : ℂ := 1 / 2 * ∫ t in (-1 : ℝ)..1, Complex.exp (-(π * I * k * t)) * f t

theorem fourierCoeff_liftIco (f : ℝ → ℂ) (k : ℤ) :
    fourierCoeff (AddCircle.liftIco 2 (-1) f) k = coeffK f k := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1), coeffK]
  have e2 : (-1 : ℝ) + 2 = 1 := by norm_num
  rw [e2, Complex.real_smul]
  refine congrArg₂ (· * ·) (by norm_num) ?_
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun t ht => ?_
  rw [fourier_coe_apply, smul_eq_mul, AddCircle.liftIco_coe_apply ⟨ht.1.le, by linarith [ht.2]⟩]
  refine congrArg (· * f t) (congrArg Complex.exp ?_)
  push_cast; ring_nf

/-- **The lattice sum of a frequency**: `Σ_{n<2N} e^{iπk(−1 + n/N)}` is `2N` if `2N ∣ k` and `0` otherwise. -/
theorem sum_exp_lattice {N : ℕ} (hN : 0 < N) (k : ℤ) :
    ∑ n ∈ Finset.range (2 * N), Complex.exp (π * I * k * ((-1 + n / N : ℝ) : ℂ))
      = if (2 * N : ℤ) ∣ k then (2 * N : ℂ) else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set r := Complex.exp (π * I * k / N) with hr
  have hterm : ∀ n : ℕ, Complex.exp (π * I * k * ((-1 + n / N : ℝ) : ℂ)) = Complex.exp (-(π * I * k)) * r ^ n :=
    fun n => by
      rw [hr, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; field_simp
  simp_rw [hterm, ← Finset.mul_sum]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    have hr1 : r = 1 := by
      rw [hr, Complex.exp_eq_one_iff]
      exact ⟨m, by push_cast; field_simp⟩
    have he : Complex.exp (-(π * I * ((2 * N * m : ℤ) : ℂ))) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨-(N * m), by push_cast; ring⟩
    rw [hr1, he, one_mul]
    simp
  · have hr1 : r ≠ 1 := by
      intro h1
      rw [hr, Complex.exp_eq_one_iff] at h1
      obtain ⟨l, hl⟩ := h1
      apply hd
      refine ⟨l, ?_⟩
      have hpi : (π : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
      have : (k : ℂ) = 2 * N * l := by
        have h2 := hl
        field_simp at h2
        linear_combination h2
      exact_mod_cast this
    have hrN : r ^ (2 * N) = 1 := by
      rw [hr, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨k, by push_cast; field_simp⟩
    rw [geom_sum_eq hr1, hrN, sub_self, zero_div, mul_zero]

variable (hf : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
  (hf₂ : ContinuousOn f₂ (uIcc (-1) 1)) (hper : f (-1) = f 1)
include hf hf₁ hf₂ hper

/-- **The coefficients are summable**. -/
theorem summable_coeffK : Summable (coeffK f) := by
  obtain ⟨M₂, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf₂
  have hab : (-1 : ℝ) < -1 + 2 := by norm_num
  have hs : Summable fun n : ℤ => (‖f₁ 1 - f₁ (-1)‖ + 2 * M₂) / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) :=
    (summable_one_div_int_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  have : {(0 : ℤ)}ᶜ ∈ cofinite := (Set.finite_singleton 0).compl_mem_cofinite
  filter_upwards [this] with n hn
  have hn : n ≠ 0 := hn
  rw [← fourierCoeff_liftIco, fourierCoeff_liftIco_eq]
  exact norm_coeff_le _ hn hf hf₁ hf₂ hper hM

/-- **The Fourier series converges pointwise**: for `t ∈ [−1, 1)`, `Σ_k c_k e^{iπkt} = f(t)`. -/
theorem hasSum_coeffK_exp {t : ℝ} (ht : t ∈ Ico (-1 : ℝ) 1) :
    HasSum (fun k : ℤ => coeffK f k * Complex.exp (π * I * k * t)) (f t) := by
  have e2 : (-1 : ℝ) + 2 = 1 := by norm_num
  have hc : Continuous (AddCircle.liftIco 2 (-1) f) := by
    refine AddCircle.liftIco_continuous (by rw [e2]; exact hper) ?_
    rw [e2]
    intro s hs
    exact (hf s (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])).continuousAt.continuousWithinAt
  set F : C(AddCircle (2 : ℝ), ℂ) := ⟨_, hc⟩
  have hsum : Summable (fourierCoeff F) := by
    have : fourierCoeff F = coeffK f := funext fun k => fourierCoeff_liftIco f k
    rw [this]; exact summable_coeffK hf hf₁ hf₂ hper
  have h := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle (2 : ℝ))
  have hF : F (t : AddCircle (2 : ℝ)) = f t :=
    AddCircle.liftIco_coe_apply ⟨ht.1, by rw [e2]; exact ht.2⟩
  rw [hF] at h
  convert h using 1
  funext k
  rw [smul_eq_mul, fourier_coe_apply]
  change coeffK f k * _ = fourierCoeff (AddCircle.liftIco 2 (-1) f) k * _
  rw [fourierCoeff_liftIco]
  refine congrArg (coeffK f k * ·) (congrArg Complex.exp ?_)
  push_cast; ring

omit hf₁ hf₂ hper in
/-- `c_k + c_{−k} = ∫_{−1}^{1} f(t) cos(πkt) dt`. -/
theorem coeffK_add_neg (k : ℤ) :
    coeffK f k + coeffK f (-k) = ∫ t in (-1 : ℝ)..1, f t * Complex.cos (π * k * t) := by
  have hfc : ContinuousOn f (uIcc (-1 : ℝ) 1) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hi : ∀ a : ℂ, IntervalIntegrable (fun t : ℝ => Complex.exp (a * t) * f t) volume (-1) 1 := fun a =>
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (a * t)).continuousOn.mul hfc).intervalIntegrable
  unfold coeffK
  have e1 : (fun t : ℝ => Complex.exp (-(π * I * (k : ℂ) * t)) * f t)
      = fun t : ℝ => Complex.exp ((-(π * I * k)) * t) * f t := by funext t; ring_nf
  have e2 : (fun t : ℝ => Complex.exp (-(π * I * ((-k : ℤ) : ℂ) * t)) * f t)
      = fun t : ℝ => Complex.exp ((π * I * k) * t) * f t := by funext t; push_cast; ring_nf
  rw [e1, e2, ← mul_add, ← intervalIntegral.integral_add (hi _) (hi _), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Complex.cos]
  ring_nf

/-- **The aliasing identity**: for `N ≥ 1`,
`Σ_{m ≥ 1} ∫_{−1}^{1} f(t) cos(2πNmt) dt = (1/2N)Σ_{n<2N} f(−1 + n/N) − ½∫_{−1}^{1} f`. -/
theorem hasSum_alias {N : ℕ} (hN : 0 < N) :
    HasSum (fun m : ℕ => ∫ t in (-1 : ℝ)..1, f t * Complex.cos (2 * π * N * (m + 1) * t))
      (1 / (2 * N) * ∑ n ∈ Finset.range (2 * N), f (-1 + n / N) - 1 / 2 * ∫ t in (-1 : ℝ)..1, f t) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  -- the series at each lattice point
  have hpt : ∀ n ∈ Finset.range (2 * N), HasSum (fun k : ℤ => coeffK f k
      * Complex.exp (π * I * k * ((-1 + n / N : ℝ) : ℂ))) (f (-1 + n / N)) := fun n hn => by
    have hn' : (n : ℝ) < 2 * N := by exact_mod_cast Finset.mem_range.1 hn
    refine hasSum_coeffK_exp hf hf₁ hf₂ hper ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ n / N := by positivity
      linarith
    · have : (n : ℝ) / N < 2 := by rw [div_lt_iff₀ hNr]; linarith
      linarith
  have hS := hasSum_sum hpt
  simp_rw [← Finset.mul_sum, sum_exp_lattice hN] at hS
  -- only the frequencies in `2Nℤ` survive
  have hg : Function.Injective fun m : ℤ => (2 * N : ℤ) * m :=
    fun a b h => by
      have h2 : (2 * N : ℤ) ≠ 0 := by positivity
      exact mul_left_cancel₀ h2 h
  have hz : ∀ k ∉ Set.range fun m : ℤ => (2 * N : ℤ) * m,
      coeffK f k * (if (2 * N : ℤ) ∣ k then (2 * N : ℂ) else 0) = 0 := fun k hk => by
    rw [ite_eq_right, mul_zero]
    rintro ⟨m, rfl⟩
    exact hk ⟨m, rfl⟩
  have hL := (hg.hasSum_iff hz).2 hS
  have hL' : HasSum (fun m : ℤ => coeffK f (2 * N * m) * (2 * N)) (∑ n ∈ Finset.range (2 * N), f (-1 + n / N)) := by
    convert hL using 2 with m
    simp
  -- fold `±m`
  have hP := hL'.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at hP
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, mul_zero] at hP
  have hfin := hP.mul_left (1 / (2 * N : ℂ))
  have hval : 1 / (2 * N : ℂ) * (∑ n ∈ Finset.range (2 * N), f (-1 + n / N) + coeffK f 0 * (2 * N)
      - (coeffK f 0 * (2 * N) + coeffK f 0 * (2 * N)))
      = 1 / (2 * N) * ∑ n ∈ Finset.range (2 * N), f (-1 + n / N) - 1 / 2 * ∫ t in (-1 : ℝ)..1, f t := by
    have hc0 : coeffK f 0 = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t := by unfold coeffK; simp
    rw [hc0]
    generalize ∑ n ∈ Finset.range (2 * N), f (-1 + n / N) = S
    field_simp
    ring
  rw [hval] at hfin
  refine hfin.congr_fun fun m => ?_
  rw [← add_mul, show (2 * N * -((m + 1 : ℕ) : ℤ) : ℤ) = -(2 * N * (m + 1 : ℕ) : ℤ) by ring,
    coeffK_add_neg hf]
  field_simp
  refine intervalIntegral.integral_congr fun t _ => ?_
  congr 2; push_cast; ring

end poisson

section even

variable {f : ℝ → ℂ}

theorem sum_Icc_eq_sum_range (g : ℕ → ℂ) (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, g n = ∑ n ∈ Finset.range N, g (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun n _ => by rw [add_comm]

/-- **Folding the lattice of an even profile**: `Σ_{n<2N} f(−1 + n/N) = 2Σ_{n=1}^{N} f(n/N) + f(0) − f(1)`. -/
theorem sum_lattice_even (heven : ∀ t ∈ Icc (-1 : ℝ) 1, f (-t) = f t) {N : ℕ} (hN : 0 < N) :
    ∑ n ∈ Finset.range (2 * N), f (-1 + n / N)
      = 2 * ∑ n ∈ Finset.Icc 1 N, f (n / N) + f 0 - f 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNr.ne'
  rw [two_mul N, Finset.sum_range_add]
  have h2 : ∀ n : ℕ, f (-1 + ((N + n : ℕ) : ℝ) / N) = f ((n : ℝ) / N) := fun n => by
    congr 1; push_cast; field_simp; ring
  simp_rw [h2]
  have h1 : ∑ n ∈ Finset.range N, f (-1 + (n : ℝ) / N) = ∑ n ∈ Finset.range N, f (((n + 1 : ℕ) : ℝ) / N) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    have hle : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn'
    rw [← heven]
    · congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; field_simp; ring
    · constructor
      · have : (0 : ℝ) ≤ ((N - 1 - n : ℕ) : ℝ) / N := by positivity
        linarith
      · have : ((N - 1 - n : ℕ) : ℝ) / N ≤ 1 := by
          rw [div_le_one hNr]; exact_mod_cast (by omega : N - 1 - n ≤ N)
        linarith
  rw [h1, sum_Icc_eq_sum_range]
  have h3 : ∑ n ∈ Finset.range N, f ((n : ℝ) / N) + f (N / N)
      = f 0 + ∑ n ∈ Finset.range N, f (((n + 1 : ℕ) : ℝ) / N) := by
    rw [← Finset.sum_range_succ (fun n : ℕ => f ((n : ℝ) / N)), Finset.sum_range_succ']
    simp [add_comm]
  rw [div_self hNne] at h3
  simp only [Nat.cast_add, Nat.cast_one] at h3 ⊢
  linear_combination h3

end even

/-- **The aliasing identity for an even profile**: for `f` of class `C²` and even on `[−1, 1]` and `N ≥ 1`,
`Σ_{m ≥ 1} ∫_{−1}^{1} f(t) cos(2πNmt) dt = (1/N)Σ_{n=1}^{N} f(n/N) − ∫_0^1 f − (f(1) − f(0))/(2N)`. -/
theorem hasSum_alias_even {f f₁ f₂ : ℝ → ℂ} (hf : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ t) t) (hf₂ : ContinuousOn f₂ (uIcc (-1) 1))
    (heven : ∀ t ∈ Icc (-1 : ℝ) 1, f (-t) = f t) {N : ℕ} (hN : 0 < N) :
    HasSum (fun m : ℕ => ∫ t in (-1 : ℝ)..1, f t * Complex.cos (2 * π * N * (m + 1) * t))
      (1 / N * ∑ n ∈ Finset.Icc 1 N, f (n / N) - (∫ t in (0 : ℝ)..1, f t) - (f 1 - f 0) / (2 * N)) := by
  have hper : f (-1) = f 1 := heven 1 (by norm_num)
  have h := hasSum_alias hf hf₁ hf₂ hper hN
  rw [sum_lattice_even heven hN] at h
  have hfc : ContinuousOn f (uIcc (-1 : ℝ) 1) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hA : IntervalIntegrable f volume (-1) 0 := (hfc.mono (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
  have hB : IntervalIntegrable f volume 0 1 := (hfc.mono (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hneg : ∫ t in (-1 : ℝ)..0, f t = ∫ t in (0 : ℝ)..1, f t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) f
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    exact heven t ⟨by linarith [ht.1], ht.2⟩
  rw [hneg] at hsplit
  rw [← hsplit] at h
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  convert h using 1
  field_simp
  ring

end Cvs.Upstream.PeriodicAliasingIdentity

end
