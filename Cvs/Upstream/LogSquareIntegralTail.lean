import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The log-square integral tail

For `a, b, c ≥ 0` the majorant `f(x) = (a log²x + b log x + c)/x²` decreases on `[e, ∞)` and has the primitive
`−F`, `F(x) = (a(log²x + 2log x + 2) + b(log x + 1) + c)/x`; so `Σ_{m > M} f(m) ≤ F(M)` for `M ≥ 3`, and a
nonnegative series dominated by `f` past `M` sums to at most its head plus `F(M)`.
-/

noncomputable section

open Real Set

namespace Cvs.Upstream.LogSquareIntegralTail

/-- The tail majorant `f(x) = (a log²x + b log x + c)/x²`. -/
def tailf (a b c x : ℝ) : ℝ := (a * Real.log x ^ 2 + b * Real.log x + c) / x ^ 2

/-- Minus its primitive, `F(x) = (a(log²x + 2log x + 2) + b(log x + 1) + c)/x`. -/
def tailF (a b c x : ℝ) : ℝ :=
  (a * (Real.log x ^ 2 + 2 * Real.log x + 2) + b * (Real.log x + 1) + c) / x

theorem hasDerivAt_tailF (a b c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (tailF a b c) (-tailf a b c x) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hN : HasDerivAt (fun y => a * (Real.log y ^ 2 + 2 * Real.log y + 2) + b * (Real.log y + 1) + c)
      (a * (2 * Real.log x * x⁻¹ + 2 * x⁻¹) + b * x⁻¹) x := by
    have h2 := hl.pow 2
    have := ((((h2.add (hl.const_mul 2)).add_const 2).const_mul a).add ((hl.add_const 1).const_mul b)).add_const c
    refine this.congr_deriv ?_
    push_cast; ring
  refine (hN.div (hasDerivAt_id x) hx.ne').congr_deriv ?_
  unfold tailf
  simp only [id]
  field_simp
  ring

/-- `f` decreases on `[e, ∞)`: it is a nonnegative combination of `(log x/x)²`, `(log x/x)(1/x)`, `1/x²`. -/
theorem tailf_antitoneOn {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    AntitoneOn (tailf a b c) (Ici (exp 1)) := by
  intro x hx y hy hxy
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  have hx0 : 0 < x := lt_of_lt_of_le he hx
  have hy0 : 0 < y := lt_of_lt_of_le he hy
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hx)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hy)
  have hq := Real.log_div_self_antitoneOn hx hy hxy
  simp only at hq
  have hq0 : 0 ≤ Real.log y / y := div_nonneg hly hy0.le
  have hsq : (Real.log y / y) ^ 2 ≤ (Real.log x / x) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have hinv : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
  have hinv0 : 0 ≤ 1 / y := by positivity
  have hlin : Real.log y / y * (1 / y) ≤ Real.log x / x * (1 / x) :=
    mul_le_mul hq hinv hinv0 (div_nonneg hlx hx0.le)
  have hinv2 : (1 / y) ^ 2 ≤ (1 / x) ^ 2 := pow_le_pow_left₀ hinv0 hinv 2
  have ey : tailf a b c y = a * (Real.log y / y) ^ 2 + b * (Real.log y / y * (1 / y)) + c * (1 / y) ^ 2 := by
    unfold tailf; field_simp
  have ex : tailf a b c x = a * (Real.log x / x) ^ 2 + b * (Real.log x / x * (1 / x)) + c * (1 / x) ^ 2 := by
    unfold tailf; field_simp
  rw [ey, ex]
  have := mul_le_mul_of_nonneg_left hsq ha
  have := mul_le_mul_of_nonneg_left hlin hb
  have := mul_le_mul_of_nonneg_left hinv2 hc
  linarith

theorem tailF_nonneg {a b c x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 1 ≤ x) : 0 ≤ tailF a b c x := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold tailF
  have : 0 ≤ a * (Real.log x ^ 2 + 2 * Real.log x + 2) + b * (Real.log x + 1) + c := by positivity
  exact div_nonneg this (by linarith)

/-- **The log-square tail**: `Σ_{M ≤ i < n} f(i + 1) ≤ F(M)` for `M ≥ 3` and `a, b, c ≥ 0`. -/
theorem sum_tailf_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {M : ℕ} (hM : 3 ≤ M) (n : ℕ) :
    ∑ i ∈ Finset.Ico M n, tailf a b c ((i + 1 : ℕ) : ℝ) ≤ tailF a b c M := by
  rcases le_or_gt n M with hn | hn
  · rw [Finset.Ico_eq_empty_of_le hn, Finset.sum_empty]
    exact tailF_nonneg ha hb hc (by exact_mod_cast (show 1 ≤ M by omega))
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have he3 : exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hanti : AntitoneOn (tailf a b c) (Icc (M : ℝ) (n : ℝ)) :=
    (tailf_antitoneOn ha hb hc).mono fun x hx => le_trans he3 (le_trans hM' hx.1)
  have h := hanti.sum_le_integral_Ico hn.le
  have hint : ∫ x in (M : ℝ)..(n : ℝ), tailf a b c x = tailF a b c M - tailF a b c n := by
    have hpos : ∀ x ∈ uIcc (M : ℝ) (n : ℝ), 0 < x := fun x hx => by
      rw [uIcc_of_le (by exact_mod_cast hn.le)] at hx; linarith [hx.1]
    have hderiv : ∀ x ∈ uIcc (M : ℝ) (n : ℝ), HasDerivAt (fun y => -tailF a b c y) (tailf a b c x) x :=
      fun x hx => (hasDerivAt_tailF a b c (hpos x hx)).neg.congr_deriv (neg_neg _)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    · ring
    · refine ContinuousOn.intervalIntegrable fun x hx => ?_
      have hx0 := hpos x hx
      unfold tailf
      exact ((((continuousAt_const.mul ((Real.continuousAt_log hx0.ne').pow 2)).add
        (continuousAt_const.mul (Real.continuousAt_log hx0.ne'))).add continuousAt_const).div
        (continuousAt_id.pow 2) (pow_ne_zero 2 hx0.ne')).continuousWithinAt
  have hF0 := tailF_nonneg ha hb hc (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
  rw [hint] at h
  linarith

/-- **Head plus tail**: a nonnegative series with head `Σ_{m ≤ M} ≤ h` and terms `≤ f(m)` past `M ≥ 3` sums to at
most `h + F(M)`. -/
theorem tsum_le_head_add_tail {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {M : ℕ} (hM : 3 ≤ M) {a b c h : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hhead : ∑ i ∈ Finset.range (M + 1), f i ≤ h)
    (htail : ∀ m : ℕ, M + 1 ≤ m → f m ≤ tailf a b c m) : ∑' n, f n ≤ h + tailF a b c M := by
  have hF0 := tailF_nonneg ha hb hc (show (1 : ℝ) ≤ M by exact_mod_cast (show 1 ≤ M by omega))
  refine Real.tsum_le_of_sum_range_le hf fun n => ?_
  rcases le_or_gt n (M + 1) with hn | hn
  · have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hn) (fun i _ _ => hf i)
    linarith
  rw [← Finset.sum_range_add_sum_Ico _ hn.le]
  have ht : ∑ i ∈ Finset.Ico (M + 1) n, f i ≤ tailF a b c M := by
    calc ∑ i ∈ Finset.Ico (M + 1) n, f i ≤ ∑ i ∈ Finset.Ico (M + 1) n, tailf a b c i :=
          Finset.sum_le_sum fun i hi => htail i (Finset.mem_Ico.1 hi).1
      _ = ∑ i ∈ Finset.Ico M (n - 1), tailf a b c ((i + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, show n - 1 - M = n - (M + 1) by omega]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show M + 1 + k = M + k + 1 by omega]
      _ ≤ tailF a b c M := sum_tailf_le ha hb hc hM (n - 1)
  linarith

end Cvs.Upstream.LogSquareIntegralTail
