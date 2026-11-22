import Mathlib.Analysis.SpecialFunctions.Complex.Log
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
# Orthogonality, and the second moment of a Dirichlet polynomial

The second moment of a Dirichlet polynomial on a vertical segment, by orthogonality of the
frequencies `n^{−it}`.
-/

open Complex intervalIntegral

namespace Cvs.GaussKernel

/-- **Orthogonality on `[-T, T]`.**  The engine of every mean value theorem for
Dirichlet polynomials: off the diagonal the oscillation `e^{-itu}` integrates to
`2 sin(Tu)/u`, which is `O(1/|u|)` uniformly in `T`. -/
theorem integral_exp_neg_mul_I {u : ℝ} (hu : u ≠ 0) (T : ℝ) :
    (∫ t in (-T)..T, Complex.exp (-((u * t : ℝ) : ℂ) * Complex.I))
      = ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
  have hc : (-(u : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.ext_iff, hu]
  have harg : ∀ t : ℝ, -((u * t : ℝ) : ℂ) * Complex.I
      = (-(u : ℂ) * Complex.I) * (t : ℂ) := by
    intro t; push_cast; ring
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    Complex.exp ((-(u : ℂ) * Complex.I) * (t : ℂ))) (fun t _ => by rw [harg]),
    integral_exp_mul_complex hc]
  have e1 : (-(u : ℂ) * Complex.I) * (T : ℂ) = (-(u * T : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : (-(u : ℂ) * Complex.I) * ((-T : ℝ) : ℂ) = ((u * T : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I]
  have hcos : Complex.cos ((-(u * T : ℝ) : ℂ)) = Complex.cos ((u * T : ℝ) : ℂ) := by
    rw [show ((-(u * T : ℝ) : ℂ)) = -((u * T : ℝ) : ℂ) by push_cast; ring,
      Complex.cos_neg]
  have hsin : Complex.sin ((-(u * T : ℝ) : ℂ)) = -Complex.sin ((u * T : ℝ) : ℂ) := by
    rw [show ((-(u * T : ℝ) : ℂ)) = -((u * T : ℝ) : ℂ) by push_cast; ring,
      Complex.sin_neg]
  rw [hcos, hsin]
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [← Complex.ofReal_sin]
  push_cast
  field_simp
  ring

/-- **The off-diagonal is `O(1/|u|)`, uniformly in `T`.**  This is the whole
content of orthogonality: the further apart two frequencies are, the less their
cross term can contribute however long the integration runs. -/
theorem norm_integral_exp_neg_mul_I_le {u : ℝ} (hu : u ≠ 0) (T : ℝ) :
    ‖∫ t in (-T)..T, Complex.exp (-((u * t : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |u| := by
  rw [integral_exp_neg_mul_I hu, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have h1 : |2 * Real.sin (T * u)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    nlinarith [Real.abs_sin_le_one (T * u)]
  exact div_le_div_of_nonneg_right h1 (abs_nonneg u)

/-- A Dirichlet polynomial on the critical-line parameter, `∑_{n ≤ N} aₙ n^{-it}`,
written through `exp` so no `cpow` branch appears. -/
noncomputable def dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)

/-- It is the Dirichlet polynomial: each factor is `n^{-it}`. -/
theorem exp_eq_cpow {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)
      = (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hn0.le]
  congr 1
  push_cast
  ring

/-- **The second moment expands into a double sum**, with the cross term at
frequency `log n - log m`. -/
theorem dirichletPoly_mul_conj (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    dirichletPoly a N t * (starRingEnd ℂ) (dirichletPoly a N t)
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          a n * (starRingEnd ℂ) (a m)
            * Complex.exp (-(((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I) := by
  rw [dirichletPoly, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (-((t * Real.log m : ℝ) : ℂ) * Complex.I)
      = ((t * Real.log m : ℝ) : ℂ) * Complex.I := by
    rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc, show a n * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)
        * ((starRingEnd ℂ) (a m) * Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I))
      = a n * (starRingEnd ℂ) (a m)
        * (Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I)) by ring,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem cont_kernel (c : ℝ) :
    Continuous fun t : ℝ => Complex.exp (-((c * t : ℝ) : ℂ) * Complex.I) := by
  fun_prop

/-- **Term by term.**  The second moment is the double sum of the cross terms'
oscillatory integrals — nothing has been estimated yet, only interchanged. -/
theorem integral_dirichletPoly_mul_conj (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ t in (-T)..T, dirichletPoly a N t * (starRingEnd ℂ) (dirichletPoly a N t))
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          a n * (starRingEnd ℂ) (a m)
            * ∫ t in (-T)..T,
                Complex.exp (-(((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I) := by
  rw [intervalIntegral.integral_congr
    (g := fun t : ℝ => ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      a n * (starRingEnd ℂ) (a m)
        * Complex.exp (-(((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I))
    (fun t _ => dirichletPoly_mul_conj a N t)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun m _ => intervalIntegral.integral_const_mul _ _
    · exact fun m _ => (((cont_kernel _).const_mul _).intervalIntegrable _ _)
  · intro n _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The diagonal term: `n = m` kills the oscillation and the integral is `2T`. -/
theorem integral_kernel_diagonal (n : ℕ) (T : ℝ) :
    (∫ t in (-T)..T,
        Complex.exp (-(((Real.log n - Real.log n) * t : ℝ) : ℂ) * Complex.I))
      = ((2 * T : ℝ) : ℂ) := by
  simp only [sub_self, zero_mul, Complex.ofReal_zero, neg_zero, zero_mul,
    Complex.exp_zero]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

/-- **The mean value theorem, split.**  Diagonal `2T·Σ|aₙ|²` plus an
off-diagonal whose every term is `O(1/|log(n/m)|)` by orthogonality.  The
off-diagonal is estimated below and the two combine in `mean_value_le`. -/
theorem norm_integral_sub_diagonal_le (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ‖(∫ t in (-T)..T, dirichletPoly a N t * (starRingEnd ℂ) (dirichletPoly a N t))
        - ((2 * T : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, ((‖a n‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
          ‖a n‖ * ‖a m‖ * (2 / |Real.log n - Real.log m|) := by
  classical
  rw [integral_dirichletPoly_mul_conj]
  have hsplit : ∀ n ∈ Finset.Icc 1 N,
      (∑ m ∈ Finset.Icc 1 N, a n * (starRingEnd ℂ) (a m)
          * ∫ t in (-T)..T,
              Complex.exp (-(((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I))
        = ((2 * T : ℝ) : ℂ) * ((‖a n‖ ^ 2 : ℝ) : ℂ)
          + ∑ m ∈ (Finset.Icc 1 N).erase n, a n * (starRingEnd ℂ) (a m)
              * ∫ t in (-T)..T,
                  Complex.exp (-(((Real.log n - Real.log m) * t : ℝ) : ℂ) * Complex.I) := by
    intro n hn
    rw [← Finset.add_sum_erase _ _ hn, integral_kernel_diagonal]
    congr 1
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
    add_sub_cancel_left]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm)).1
  have hmn : m ≠ n := Finset.ne_of_mem_erase hm
  have hne : Real.log n - Real.log m ≠ 0 := by
    intro hc
    have heq : Real.log (n : ℝ) = Real.log (m : ℝ) := by linarith
    have hpn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hpm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hpn) (Set.mem_Ioi.mpr hpm) heq
    exact hmn (by exact_mod_cast this.symm)
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_exp_neg_mul_I_le hne T) (by positivity)

/-! ## The next brick: the logarithmic gap

`norm_integral_sub_diagonal_le` leaves `Σ_{n ≠ m} |aₙ||aₘ| / |log(n/m)|`.  The
first step is to replace the logarithm by something combinatorial. -/

/-- **The ordinate gap of two Dirichlet frequencies.** For `m < n` the logarithmic gap is at least
`(n - m)/n`, hence at least `(n - m)/N` when both are at most `N`. -/
theorem sub_div_le_log_div {m n : ℝ} (hm : 0 < m) (hmn : m ≤ n) :
    (n - m) / n ≤ Real.log (n / m) := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < m / n by positivity)
  rw [Real.log_div (ne_of_gt hm) (ne_of_gt hn)] at h
  rw [Real.log_div (ne_of_gt hn) (ne_of_gt hm)]
  have hmn' : m / n ≤ 1 := by rw [div_le_one hn]; exact hmn
  have : m / n - 1 = -((n - m) / n) := by field_simp; ring
  rw [this] at h
  linarith

/-- **The form the off-diagonal sum consumes.** With both frequencies at most `N`, the logarithmic
gap is at least `(n - m)/N`. -/
theorem sub_div_le_log_div_of_le {m n N : ℝ} (hm : 0 < m) (hmn : m ≤ n)
    (hnN : n ≤ N) : (n - m) / N ≤ Real.log (n / m) := by
  refine le_trans ?_ (sub_div_le_log_div hm hmn)
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hN : 0 < N := lt_of_lt_of_le hn hnN
  rw [div_le_div_iff₀ hN hn]
  nlinarith

/-! ### The harmonic row

`sub_div_le_log_div_of_le` turns `1/|log(n/m)|` into `N/|n - m|`.  Summing that
over one row is a harmonic sum, and this is where the `log N` enters. -/

/-- Distance between naturals, in ℕ. -/
def natDist (n m : ℕ) : ℕ := (n - m) + (m - n)

/-- The distance map is at most two-to-one: only `n - d` and `n + d` sit at
distance `d` from `n`. -/
theorem card_dist_fibre_le (N n d : ℕ) :
    (((Finset.Icc 1 N).erase n).filter (fun m => natDist n m = d)).card ≤ 2 := by
  classical
  refine le_trans (Finset.card_le_card (t := ({n - d, n + d} : Finset ℕ))
    (fun m hm => ?_)) ?_
  · obtain ⟨-, hd⟩ := Finset.mem_filter.mp hm
    simp only [natDist] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- **The harmonic row bound.** Summing `1/dist(n,m)` over `m ≤ N` with `m ≠ n` costs at most two
harmonic numbers, because each distance is achieved at most twice. -/
theorem sum_inv_dist_le {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    ∑ m ∈ (Finset.Icc 1 N).erase n, (1 : ℝ) / (natDist n m)
      ≤ 2 * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d := by
  classical
  rw [Finset.sum_comp (fun d : ℕ => (1 : ℝ) / d) (fun m => natDist n m)]
  calc ∑ b ∈ ((Finset.Icc 1 N).erase n).image (fun m => natDist n m),
        (((Finset.Icc 1 N).erase n).filter
          (fun a => natDist n a = b)).card • ((1 : ℝ) / b)
      ≤ ∑ _b ∈ ((Finset.Icc 1 N).erase n).image (fun m => natDist n m),
          (2 : ℝ) * ((1 : ℝ) / _b) := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_dist_fibre_le N n d) (by positivity)
    _ ≤ 2 * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun d _ _ => by positivity)) (by norm_num)
        intro d hd
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hm
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem
        obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
        simp only [natDist]
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> omega

/-! ### The three remaining elementary steps

The log gap made symmetric and moved into `ℕ`; the harmonic sum in the shape
`sum_inv_dist_le` produces it; and the symmetrisation that turns a double sum
into a row sum. -/

/-- **The log gap dominates the integer gap, scaled by `N`.**  This is
`sub_div_le_log_div_of_le` made symmetric and moved into `ℕ`. -/
theorem natDist_div_le_abs_log_sub {n m N : ℕ} (hn : n ∈ Finset.Icc 1 N)
    (hm : m ∈ Finset.Icc 1 N) :
    (natDist n m : ℝ) / N ≤ |Real.log n - Real.log m| := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  rcases le_total m n with h | h
  · have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
    have hkey := sub_div_le_log_div_of_le hmR hmn hnN
    rw [Real.log_div (ne_of_gt hnR) (ne_of_gt hmR)] at hkey
    have hd : ((natDist n m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
      have he : natDist n m = n - m := by simp only [natDist]; omega
      rw [he, Nat.cast_sub h]
    rw [hd, abs_of_nonneg (by linarith [Real.log_le_log hmR hmn])]
    exact hkey
  · have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm2
    have hkey := sub_div_le_log_div_of_le hnR hmn hmN
    rw [Real.log_div (ne_of_gt hmR) (ne_of_gt hnR)] at hkey
    have hd : ((natDist n m : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
      have he : natDist n m = m - n := by simp only [natDist]; omega
      rw [he, Nat.cast_sub h]
    rw [hd, abs_of_nonpos (by linarith [Real.log_le_log hnR hmn])]
    linarith

/-- The harmonic sum in the shape `sum_inv_dist_le` produces it. -/
theorem sum_inv_Icc_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have he : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun d _ => by rw [one_div]
  rw [he] at h
  exact h

/-- **Symmetrisation.**  The product of two norms is at most the mean of their
squares — which is what turns a double sum into a row sum. -/
theorem norm_mul_norm_le (x y : ℝ) : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (x - y)]

/-! ### Symmetry, and the cross term

The two pieces the summation needs: that the off-diagonal set is symmetric in
the index order, and that one cross term obeys the bound the row sum will
consume. -/

/-- **The off-diagonal double sum is symmetric in its index order.**  Both sides
run over the same set — pairs in `Icc 1 N` with distinct entries. -/
theorem offdiag_swap {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n, f n m
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, f n m := by
  classical
  refine Finset.sum_comm' ?_
  intro n m
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hn, hne, hm⟩; exact ⟨⟨fun h => hne h.symm, hn⟩, hm⟩
  · rintro ⟨⟨hne, hn⟩, hm⟩; exact ⟨hn, fun h => hne h.symm, hm⟩

/-- **The cross term, bounded.**  Symmetrisation and the log-to-distance
conversion, applied to one pair. -/
theorem offdiag_term_le (a : ℕ → ℂ) {N n m : ℕ} (hn : n ∈ Finset.Icc 1 N)
    (hm : m ∈ Finset.Icc 1 N) (hne : m ≠ n) :
    ‖a n‖ * ‖a m‖ * (2 / |Real.log n - Real.log m|)
      ≤ (N : ℝ) * ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / (natDist n m)) := by
  have hd0 : 0 < natDist n m := by simp only [natDist]; omega
  have hdR : (0 : ℝ) < (natDist n m : ℝ) := by exact_mod_cast hd0
  have hN : (0 : ℝ) < N := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 h2)
    exact_mod_cast this
  have hlog := natDist_div_le_abs_log_sub hn hm
  have hlogpos : (0 : ℝ) < |Real.log n - Real.log m| :=
    lt_of_lt_of_le (by positivity) hlog
  have hlog' : (natDist n m : ℝ) ≤ |Real.log n - Real.log m| * N := by
    rw [div_le_iff₀ hN] at hlog; exact hlog
  have hinv : 2 / |Real.log n - Real.log m| ≤ 2 * (N : ℝ) / (natDist n m) := by
    rw [div_le_div_iff₀ hlogpos hdR]
    nlinarith [hlog']
  calc ‖a n‖ * ‖a m‖ * (2 / |Real.log n - Real.log m|)
      ≤ ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2) * (2 * (N : ℝ) / (natDist n m)) :=
        mul_le_mul (norm_mul_norm_le _ _) hinv (by positivity) (by positivity)
    _ = (N : ℝ) * ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / (natDist n m)) := by field_simp

/-! ## The mean value theorem

The assembly.  Both halves of the off-diagonal are the same sum under
`offdiag_swap` and `natDist_comm`, so each contributes `2N(1 + log N)`, and the
diagonal was exact from the start. -/

theorem natDist_comm (n m : ℕ) : natDist n m = natDist m n := by
  simp only [natDist]; omega

/-- One row of the reciprocal-distance sum is at most two harmonic numbers. -/
theorem row_sum_le {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    ∑ m ∈ (Finset.Icc 1 N).erase n, (1 : ℝ) / (natDist n m)
      ≤ 2 * (1 + Real.log N) :=
  le_trans (sum_inv_dist_le hn) (by linarith [sum_inv_Icc_le N])

/-- The half of the off-diagonal sum whose numerator matches the outer index. -/
theorem offdiag_half_le (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
        (N : ℝ) * (‖a n‖ ^ 2 / (natDist n m))
      ≤ 2 * N * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hrow := row_sum_le (N := N) (n := n) hn
  calc ∑ m ∈ (Finset.Icc 1 N).erase n, (N : ℝ) * (‖a n‖ ^ 2 / (natDist n m))
      = (N : ℝ) * ‖a n‖ ^ 2 * ∑ m ∈ (Finset.Icc 1 N).erase n,
          (1 : ℝ) / (natDist n m) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ (N : ℝ) * ‖a n‖ ^ 2 * (2 * (1 + Real.log N)) := by
        refine mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = 2 * N * (1 + Real.log N) * ‖a n‖ ^ 2 := by ring

/-- **The off-diagonal bound.**  Both halves are the same sum under
`offdiag_swap` and `natDist_comm`, so each contributes `2N(1 + log N)`. -/
theorem offdiag_le (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
        ‖a n‖ * ‖a m‖ * (2 / |Real.log n - Real.log m|)
      ≤ 4 * N * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  have hstep : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
      ‖a n‖ * ‖a m‖ * (2 / |Real.log n - Real.log m|)
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
          ((N : ℝ) * (‖a n‖ ^ 2 / (natDist n m))
            + (N : ℝ) * (‖a m‖ ^ 2 / (natDist n m))) := by
    refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hm
    have h := offdiag_term_le a hn hmem hne
    calc ‖a n‖ * ‖a m‖ * (2 / |Real.log n - Real.log m|)
        ≤ (N : ℝ) * ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / (natDist n m)) := h
      _ = _ := by rw [add_div, mul_add]
  refine hstep.trans ?_
  have hsplit : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
      ((N : ℝ) * (‖a n‖ ^ 2 / (natDist n m))
        + (N : ℝ) * (‖a m‖ ^ 2 / (natDist n m)))
      = (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
            (N : ℝ) * (‖a n‖ ^ 2 / (natDist n m)))
        + ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
            (N : ℝ) * (‖a m‖ ^ 2 / (natDist n m)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_add_distrib
  rw [hsplit]
  have hB : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
      (N : ℝ) * (‖a m‖ ^ 2 / (natDist n m))
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
          (N : ℝ) * (‖a n‖ ^ 2 / (natDist n m)) := by
    rw [offdiag_swap N (fun n m => (N : ℝ) * (‖a m‖ ^ 2 / (natDist n m)))]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by
      rw [natDist_comm]
  rw [hB]
  have := offdiag_half_le a N
  linarith

/-- **The mean value theorem for Dirichlet polynomials.** `‖∫_{-T}^{T} |Σ_{n ≤ N} aₙ n^{-it}|² dt
− 2T Σ|aₙ|²‖ ≤ 4N(1 + log N) Σ|aₙ|²` The diagonal is exactly `2T Σ|aₙ|²`; everything else is
bounded by `4N(1 + log N) Σ|aₙ|²`. -/
theorem mean_value_le (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ‖(∫ t in (-T)..T, dirichletPoly a N t * (starRingEnd ℂ) (dirichletPoly a N t))
        - ((2 * T : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, ((‖a n‖ ^ 2 : ℝ) : ℂ)‖
      ≤ 4 * N * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  le_trans (norm_integral_sub_diagonal_le a N T) (offdiag_le a N)

end Cvs.GaussKernel
