import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Decoupling a pair sum over `1/(A + β₁e_n − β₂e_m)^p`

With `z_{nm} = (β₂e_m − β₁e_n)/A`, `|e| ≤ r` and `q = r(β₁ + β₂)/|A| < 1`, the finite geometric expansions of
`1/(1 − z)` and `1/(1 − z)²` split `Σ_{nm} F_nG_m/(A + β₁e_n − β₂e_m)^p` into products of the one-sided moments
`Σ_n F_ne_n^a` with weight `q^N` and a remainder `O(Mq^M)`.
-/

noncomputable section

open Finset

namespace Cvs.Upstream.PairSumPowerDecoupling

variable {ι : Type*} [Fintype ι]

/-- `Σ_{nm} F_nG_m(x_n + y_m)^N = Σ_a C(N, a)(Σ F_nx_n^a)(Σ G_my_m^{N−a})`. -/
theorem sum_mul_add_pow (F G x y : ι → ℝ) (N : ℕ) :
    ∑ n, ∑ m, F n * G m * (x n + y m) ^ N
      = ∑ a ∈ range (N + 1), (N.choose a : ℝ) * ((∑ n, F n * x n ^ a) * (∑ m, G m * y m ^ (N - a))) := by
  calc ∑ n, ∑ m, F n * G m * (x n + y m) ^ N
      = ∑ n, ∑ m, ∑ a ∈ range (N + 1), F n * G m * (x n ^ a * y m ^ (N - a) * N.choose a) := by
        simp only [add_pow, Finset.mul_sum]
    _ = ∑ n, ∑ a ∈ range (N + 1), ∑ m, F n * G m * (x n ^ a * y m ^ (N - a) * N.choose a) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = ∑ a ∈ range (N + 1), ∑ n, ∑ m, F n * G m * (x n ^ a * y m ^ (N - a) * N.choose a) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring

/-- `1/(1 − z)² = Σ_{N<M}(N + 1)z^N + ((M + 1)z^M − Mz^{M+1})/(1 − z)²`. -/
theorem inv_one_sub_sq_eq {z : ℝ} (hz : z ≠ 1) (M : ℕ) :
    1 / (1 - z) ^ 2 = ∑ N ∈ range M, ((N : ℝ) + 1) * z ^ N
      + (((M : ℝ) + 1) * z ^ M - M * z ^ (M + 1)) / (1 - z) ^ 2 := by
  have h : (1 - z) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hz))
  have key : ∀ M : ℕ, (∑ N ∈ range M, ((N : ℝ) + 1) * z ^ N) * (1 - z) ^ 2
      = 1 - ((M : ℝ) + 1) * z ^ M + M * z ^ (M + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring
  rw [eq_div_of_mul_eq h (key M), ← add_div]
  congr 1
  ring

/-- One binomial term is at most the whole binomial sum. -/
theorem choose_mul_le_add_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {N a : ℕ} (ha : a ∈ range (N + 1)) :
    (N.choose a : ℝ) * (x ^ a * y ^ (N - a)) ≤ (x + y) ^ N := by
  rw [add_pow]
  refine (le_of_eq (by ring)).trans (Finset.single_le_sum (f := fun m => x ^ m * y ^ (N - m) * N.choose m)
    (fun m _ => by positivity) ha)

/-- `|Σ_{nm} F_nG_m z_{nm}^N| ≤ q^N Σ_a |P_a||Q_{N−a}|` with the normalised moments `P_a = Σ F_ne_n^a/r^a`. -/
theorem abs_sum_z_pow_le (F G e : ι → ℝ) {A β₁ β₂ r : ℝ} (hA : A ≠ 0) (hr : 0 < r) (hβ₁ : 0 ≤ β₁)
    (hβ₂ : 0 ≤ β₂) (N : ℕ) :
    |∑ n, ∑ m, F n * G m * ((β₂ * e m - β₁ * e n) / A) ^ N|
      ≤ (r * (β₁ + β₂) / |A|) ^ N * ∑ a ∈ range (N + 1),
          |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)| := by
  have e1 : ∀ n m, (β₂ * e m - β₁ * e n) / A = -β₁ / A * e n + β₂ / A * e m := fun n m => by ring
  simp_rw [e1]
  rw [sum_mul_add_pow, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  have ha' : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hra : r ^ a ≠ 0 := pow_ne_zero _ hr.ne'
  have hrb : r ^ (N - a) ≠ 0 := pow_ne_zero _ hr.ne'
  have hP : ∑ n, F n * (-β₁ / A * e n) ^ a = (-β₁ / A) ^ a * r ^ a * ((∑ n, F n * e n ^ a) / r ^ a) := by
    rw [mul_assoc, mul_div_cancel₀ _ hra, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hQ : ∑ m, G m * (β₂ / A * e m) ^ (N - a)
      = (β₂ / A) ^ (N - a) * r ^ (N - a) * ((∑ m, G m * e m ^ (N - a)) / r ^ (N - a)) := by
    rw [mul_assoc, mul_div_cancel₀ _ hrb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hP, hQ]
  set P := (∑ n, F n * e n ^ a) / r ^ a
  set Q := (∑ m, G m * e m ^ (N - a)) / r ^ (N - a)
  have hc := choose_mul_le_add_pow (mul_nonneg hr.le hβ₁) (mul_nonneg hr.le hβ₂) ha
  have hA' : 0 < |A| := abs_pos.mpr hA
  have hpow : |A| ^ N = |A| ^ a * |A| ^ (N - a) := by rw [← pow_add, Nat.add_sub_cancel' ha']
  have habs : |(N.choose a : ℝ) * ((-β₁ / A) ^ a * r ^ a * P * ((β₂ / A) ^ (N - a) * r ^ (N - a) * Q))|
      = (N.choose a : ℝ) * ((r * β₁) ^ a * (r * β₂) ^ (N - a)) / |A| ^ N * (|P| * |Q|) := by
    rw [abs_mul, Nat.abs_cast]
    simp only [abs_mul, abs_pow, abs_div, abs_neg, abs_of_nonneg hβ₁, abs_of_nonneg hβ₂, abs_of_pos hr]
    rw [hpow]
    have h1 : |A| ^ a * |A|⁻¹ ^ a = 1 := by rw [← mul_pow, mul_inv_cancel₀ hA'.ne', one_pow]
    have h2 : |A| ^ (N - a) * |A|⁻¹ ^ (N - a) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hA'.ne', one_pow]
    field_simp
    linear_combination (↑(N.choose a) * β₁ ^ a * r ^ a * r ^ (N - a) * |P| * β₂ ^ (N - a) * |Q|) *
      (|A| ^ (N - a) * |A|⁻¹ ^ (N - a) * h1 + h2)
  rw [habs, div_pow]
  have hA0 : 0 < |A| ^ N := by positivity
  have hPQ : 0 ≤ |P| * |Q| := by positivity
  calc (N.choose a : ℝ) * ((r * β₁) ^ a * (r * β₂) ^ (N - a)) / |A| ^ N * (|P| * |Q|)
      ≤ (r * (β₁ + β₂)) ^ N / |A| ^ N * (|P| * |Q|) := by
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hA0.le) hPQ
        calc (N.choose a : ℝ) * ((r * β₁) ^ a * (r * β₂) ^ (N - a)) ≤ (r * β₁ + r * β₂) ^ N := hc
          _ = (r * (β₁ + β₂)) ^ N := by ring
    _ = _ := by ring

/-- `1/(1 − z) = Σ_{N<M} z^N + z^M/(1 − z)`. -/
theorem inv_one_sub_eq {z : ℝ} (hz : z ≠ 1) (M : ℕ) :
    1 / (1 - z) = ∑ N ∈ range M, z ^ N + z ^ M / (1 - z) := by
  have h : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [geom_sum_eq hz]
  field_simp
  ring

section Bilin

/-- The pair ratio `z_{nm} = (β₂e_m − β₁e_n)/A`. -/
def zr (e : ι → ℝ) (A β₁ β₂ : ℝ) (n m : ι) : ℝ := (β₂ * e m - β₁ * e n) / A

variable (F G e : ι → ℝ) {A β₁ β₂ r q : ℝ}

omit [Fintype ι] in
/-- `|z_{nm}| ≤ q`. -/
theorem abs_zr_le (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (he : ∀ n, |e n| ≤ r)
    (hq : r * (β₁ + β₂) / |A| ≤ q) (n m : ι) : |zr e A β₁ β₂ n m| ≤ q := by
  refine le_trans ?_ hq
  rw [zr, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg A)
  calc |β₂ * e m - β₁ * e n| ≤ |β₂ * e m| + |β₁ * e n| := abs_sub _ _
    _ = β₂ * |e m| + β₁ * |e n| := by rw [abs_mul, abs_mul, abs_of_nonneg hβ₁, abs_of_nonneg hβ₂]
    _ ≤ β₂ * r + β₁ * r :=
        add_le_add (mul_le_mul_of_nonneg_left (he m) hβ₂) (mul_le_mul_of_nonneg_left (he n) hβ₁)
    _ = r * (β₁ + β₂) := by ring

omit [Fintype ι] in
/-- `A + β₁e_n − β₂e_m = A(1 − z_{nm})`. -/
theorem denom_eq (hA : A ≠ 0) (n m : ι) :
    A + β₁ * e n - β₂ * e m = A * (1 - zr e A β₁ β₂ n m) := by
  rw [zr]; field_simp; ring

/-- **The first-order decoupling**: the pair sum over `1/(A + β₁e_n − β₂e_m)` minus its leading term. -/
theorem bilin1 (hA : A ≠ 0) (hr : 0 < r) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (he : ∀ n, |e n| ≤ r)
    (hq : r * (β₁ + β₂) / |A| ≤ q) (hq1 : q < 1) {M : ℕ} (hM : 1 ≤ M) :
    |∑ n, ∑ m, F n * G m / (A + β₁ * e n - β₂ * e m) - (∑ n, F n) * (∑ m, G m) / A|
      ≤ (∑ N ∈ Ico 1 M, (r * (β₁ + β₂) / |A|) ^ N * ∑ a ∈ range (N + 1),
          |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)|
        + q ^ M / (1 - q) * ∑ n, ∑ m, |F n| * |G m|) / |A| := by
  have hzq : ∀ n m, |zr e A β₁ β₂ n m| ≤ q := abs_zr_le e hβ₁ hβ₂ he hq
  have hz1 : ∀ n m, zr e A β₁ β₂ n m ≠ 1 := fun n m h => by
    have := hzq n m; rw [h, abs_one] at this; linarith
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  set T : ℕ → ℝ := fun N => ∑ n, ∑ m, F n * G m * zr e A β₁ β₂ n m ^ N with hT
  set R : ℝ := ∑ n, ∑ m, F n * G m * (zr e A β₁ β₂ n m ^ M / (1 - zr e A β₁ β₂ n m)) with hR
  have key : ∀ n m, F n * G m / (A + β₁ * e n - β₂ * e m)
      = (∑ N ∈ range M, F n * G m * zr e A β₁ β₂ n m ^ N
        + F n * G m * (zr e A β₁ β₂ n m ^ M / (1 - zr e A β₁ β₂ n m))) / A := by
    intro n m
    have h1 : 1 - zr e A β₁ β₂ n m ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz1 n m))
    rw [← Finset.mul_sum, ← mul_add, ← inv_one_sub_eq (hz1 n m), denom_eq e hA]
    field_simp
  have hsum : ∑ n, ∑ m, F n * G m / (A + β₁ * e n - β₂ * e m) = (∑ N ∈ range M, T N + R) / A := by
    simp_rw [key, ← Finset.sum_div, Finset.sum_add_distrib]
    congr 2
    rw [hT]
    exact (Finset.sum_congr rfl fun n _ => Finset.sum_comm).trans Finset.sum_comm
  have hT0 : T 0 = (∑ n, F n) * (∑ m, G m) := by
    rw [hT, Finset.sum_mul_sum]; simp
  rw [hsum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM, hT0, add_assoc, add_div, add_sub_cancel_left,
    abs_div]
  refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun N _ =>
      abs_sum_z_pow_le F G e hA hr hβ₁ hβ₂ N)
  · rw [hR, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    have h1 : 0 < 1 - q := by linarith
    have hz := hzq n m
    have hden : 1 - q ≤ |1 - zr e A β₁ β₂ n m| := by
      have := neg_abs_le (zr e A β₁ β₂ n m)
      have := le_abs_self (1 - zr e A β₁ β₂ n m)
      have := abs_le.mp hz
      linarith
    rw [abs_mul, abs_mul, abs_div, abs_pow]
    calc |F n| * |G m| * (|zr e A β₁ β₂ n m| ^ M / |1 - zr e A β₁ β₂ n m|)
        ≤ |F n| * |G m| * (q ^ M / (1 - q)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hz M) h1 hden
      _ = q ^ M / (1 - q) * (|F n| * |G m|) := by ring

/-- **The second-order decoupling**: the pair sum over `1/(A + β₁e_n − β₂e_m)²`. -/
theorem bilin2 (hA : A ≠ 0) (hr : 0 < r) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (he : ∀ n, |e n| ≤ r)
    (hq : r * (β₁ + β₂) / |A| ≤ q) (hq1 : q < 1) (M : ℕ) :
    |∑ n, ∑ m, F n * G m / (A + β₁ * e n - β₂ * e m) ^ 2|
      ≤ (∑ N ∈ range M, ((N : ℝ) + 1) * ((r * (β₁ + β₂) / |A|) ^ N * ∑ a ∈ range (N + 1),
          |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)|)
        + (2 * M + 1) * q ^ M / (1 - q) ^ 2 * ∑ n, ∑ m, |F n| * |G m|) / A ^ 2 := by
  have hzq : ∀ n m, |zr e A β₁ β₂ n m| ≤ q := abs_zr_le e hβ₁ hβ₂ he hq
  have hz1 : ∀ n m, zr e A β₁ β₂ n m ≠ 1 := fun n m h => by
    have := hzq n m; rw [h, abs_one] at this; linarith
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  set T : ℕ → ℝ := fun N => ∑ n, ∑ m, F n * G m * (((N : ℝ) + 1) * zr e A β₁ β₂ n m ^ N) with hT
  set R : ℝ := ∑ n, ∑ m, F n * G m * ((((M : ℝ) + 1) * zr e A β₁ β₂ n m ^ M
    - M * zr e A β₁ β₂ n m ^ (M + 1)) / (1 - zr e A β₁ β₂ n m) ^ 2) with hR
  have key : ∀ n m, F n * G m / (A + β₁ * e n - β₂ * e m) ^ 2
      = (∑ N ∈ range M, F n * G m * (((N : ℝ) + 1) * zr e A β₁ β₂ n m ^ N)
        + F n * G m * ((((M : ℝ) + 1) * zr e A β₁ β₂ n m ^ M
          - M * zr e A β₁ β₂ n m ^ (M + 1)) / (1 - zr e A β₁ β₂ n m) ^ 2)) / A ^ 2 := by
    intro n m
    have h1 : 1 - zr e A β₁ β₂ n m ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz1 n m))
    rw [← Finset.mul_sum, ← mul_add, ← inv_one_sub_sq_eq (hz1 n m), denom_eq e hA]
    field_simp
  have hsum : ∑ n, ∑ m, F n * G m / (A + β₁ * e n - β₂ * e m) ^ 2 = (∑ N ∈ range M, T N + R) / A ^ 2 := by
    simp_rw [key, ← Finset.sum_div, Finset.sum_add_distrib]
    congr 2
    rw [hT]
    exact (Finset.sum_congr rfl fun n _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hsum, abs_div, abs_of_nonneg (sq_nonneg A)]
  refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (sq_nonneg _)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun N _ => ?_)
    have e2 : T N = ((N : ℝ) + 1) * ∑ n, ∑ m, F n * G m * zr e A β₁ β₂ n m ^ N := by
      rw [hT, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [e2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left (abs_sum_z_pow_le F G e hA hr hβ₁ hβ₂ N) (by positivity)
  · rw [hR, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    have h1 : 0 < 1 - q := by linarith
    have hz := hzq n m
    set z := zr e A β₁ β₂ n m
    have hden : (1 - q) ^ 2 ≤ |1 - z| ^ 2 := by
      have := neg_abs_le z
      have := le_abs_self (1 - z)
      have := abs_le.mp hz
      exact pow_le_pow_left₀ h1.le (by linarith) 2
    have hnum : |((M : ℝ) + 1) * z ^ M - M * z ^ (M + 1)| ≤ (2 * M + 1) * q ^ M := by
      have hzM : |z| ^ M ≤ q ^ M := pow_le_pow_left₀ (abs_nonneg _) hz M
      have hzM1 : |z| ^ (M + 1) ≤ q ^ M := by
        rw [pow_succ]
        calc |z| ^ M * |z| ≤ q ^ M * 1 :=
              mul_le_mul hzM (hz.trans hq1.le) (abs_nonneg _) (by positivity)
          _ = q ^ M := mul_one _
      calc |((M : ℝ) + 1) * z ^ M - M * z ^ (M + 1)| ≤ ((M : ℝ) + 1) * |z| ^ M + M * |z| ^ (M + 1) := by
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1),
              Nat.abs_cast]
        _ ≤ ((M : ℝ) + 1) * q ^ M + M * q ^ M := by gcongr
        _ = (2 * M + 1) * q ^ M := by ring
    rw [abs_mul, abs_mul, abs_div, abs_pow]
    calc |F n| * |G m| * (|((M : ℝ) + 1) * z ^ M - M * z ^ (M + 1)| / |1 - z| ^ 2)
        ≤ |F n| * |G m| * ((2 * M + 1) * q ^ M / (1 - q) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = (2 * M + 1) * q ^ M / (1 - q) ^ 2 * (|F n| * |G m|) := by ring

end Bilin

/-- Partial sums of `Σ C(N + j, j) q^N` are at most `1/(1 − q)^{j+1}`. -/
theorem sum_choose_mul_pow_le (j : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    ∑ N ∈ range M, ((N + j).choose j : ℝ) * q ^ N ≤ 1 / (1 - q) ^ (j + 1) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) j (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
  exact sum_le_hasSum _ (fun N _ => by positivity) h

/-- `Σ_{l ∈ s, l ≠ k} 1/(k − l)² ≤ 4`. -/
theorem sum_inv_sq_sub_le (s : Finset ℕ) (k : ℕ) :
    ∑ l ∈ s, (if l = k then 0 else 1 / ((k : ℝ) - l) ^ 2) ≤ 4 := by
  set f : ℕ → ℝ := fun l => if l = k then 0 else 1 / ((k : ℝ) - l) ^ 2
  have hf0 : ∀ l, 0 ≤ f l := fun l => by simp only [f]; split_ifs <;> positivity
  rw [← Finset.sum_filter_add_sum_filter_not s (· < k)]
  have hlow : ∑ l ∈ s.filter (· < k), f l ≤ 2 := by
    have hinj : Set.InjOn (fun l => k - l) (s.filter (· < k) : Set ℕ) := by
      intro a ha b hb h
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      simp only at h; omega
    have e : ∑ l ∈ s.filter (· < k), f l = ∑ d ∈ (s.filter (· < k)).image (fun l => k - l), 1 / (d : ℝ) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := (Finset.mem_filter.mp hl).2
      simp only [f, if_neg (Nat.ne_of_lt hl'), Nat.cast_sub hl'.le]
    rw [e]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Icc 1 k) ?_ fun _ _ _ => by positivity).trans ?_
    · intro d hd
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
      have := (Finset.mem_filter.mp hl).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (k + 1) |>.trans_eq' (by
        refine Finset.sum_congr (by ext d; simp; omega) fun d _ => by simp) |>.trans (by norm_num)
  have hhigh : ∑ l ∈ s.filter (fun l => ¬ l < k), f l ≤ 2 := by
    set N := s.sup id
    have hinj : Set.InjOn (fun l => l - k) ((s.filter (fun l => ¬ l < k)).filter (· ≠ k) : Set ℕ) := by
      intro a ha b hb h
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at ha hb
      simp only at h; omega
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun l => ¬ l < k)) (· ≠ k)]
    have hz : ∑ l ∈ (s.filter (fun l => ¬ l < k)).filter (fun l => ¬ l ≠ k), f l = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have := (Finset.mem_filter.mp hl).2
      simp only [f, if_pos (not_not.mp this)]
    rw [hz, add_zero]
    have e : ∑ l ∈ (s.filter (fun l => ¬ l < k)).filter (· ≠ k), f l
        = ∑ d ∈ ((s.filter (fun l => ¬ l < k)).filter (· ≠ k)).image (fun l => l - k), 1 / (d : ℝ) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun l hl => ?_
      have h1 := (Finset.mem_filter.mp hl).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
      simp only [f, if_neg h1, Nat.cast_sub (not_lt.mp h2)]
      congr 1; ring
    rw [e]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Icc 1 N) ?_ fun _ _ _ => by positivity).trans ?_
    · intro d hd
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
      have h1 := (Finset.mem_filter.mp hl).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
      have h3 : l ≤ N := Finset.le_sup (f := id) (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1) |>.trans_eq' (by
        refine Finset.sum_congr (by ext d; simp; omega) fun d _ => by simp) |>.trans (by norm_num)
  linarith

end Cvs.Upstream.PairSumPowerDecoupling
