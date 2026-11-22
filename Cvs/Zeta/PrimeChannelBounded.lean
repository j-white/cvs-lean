import Mathlib
import Cvs.Zeta.PrimeChannelFiniteInterval
import Cvs.Zeta.XiPrimeSide

/-!
# The prime channel is `O(1)`, uniformly in `T`

`PrimeChannelFiniteInterval` expanded the channel into its Dirichlet series and bounded each term's integrand,
giving `O(T)`.
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta ArithmeticFunction LSeries
open scoped ArithmeticFunction

namespace Cvs.ZeroCounting

/-- The Dirichlet term on the line, as a constant times a pure exponential in `y`. -/
theorem term_vline_eq {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    term (fun k => (Λ k : ℂ)) (vline y) n
      = ((Λ n : ℂ) / (n : ℂ) ^ (2 : ℂ))
        * Complex.exp ((-(Real.log n : ℂ) * I) * (y : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hI : (n : ℂ) ^ ((y : ℂ) * I)
      = Complex.exp (((Real.log n : ℂ) * I) * (y : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    ring_nf
  have hEinv : (Complex.exp (((Real.log n : ℂ) * I) * (y : ℂ)))⁻¹
      = Complex.exp ((-(Real.log n : ℂ) * I) * (y : ℂ)) := by
    rw [← Complex.exp_neg]
    ring_nf
  rw [LSeries.term_of_ne_zero hn, vline, Complex.cpow_add _ _ hn0, hI,
    div_mul_eq_div_div, div_eq_mul_inv, hEinv]

/-- The inner integral, bounded by `2/log n` **uniformly in `T`**. -/
theorem norm_integral_exp_le {L : ℝ} (hL : 0 < L) (T : ℝ) :
    ‖∫ y in (-T)..T, Complex.exp ((-(L : ℂ) * I) * (y : ℂ))‖ ≤ 2 / L := by
  have hc : (-(L : ℂ) * I) ≠ 0 := by
    simp [Complex.I_ne_zero, ne_of_gt hL]
  rw [integral_exp_mul_complex hc]
  have hnum : ‖Complex.exp ((-(L : ℂ) * I) * (T : ℂ))
      - Complex.exp ((-(L : ℂ) * I) * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_exp, Complex.norm_exp]
    have h1 : ((-(L : ℂ) * I) * (T : ℂ)).re = 0 := by simp
    have h2 : ((-(L : ℂ) * I) * ((-T : ℝ) : ℂ)).re = 0 := by simp
    rw [h1, h2]
    norm_num
  have hden : ‖(-(L : ℂ) * I)‖ = L := by
    rw [norm_mul, Complex.norm_I, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hL, mul_one]
  rw [norm_div, hden]
  gcongr

/-- **Each term's integral, `T`-free.** -/
theorem norm_integral_term_le {n : ℕ} (hn : 2 ≤ n) (T : ℝ) :
    ‖∫ y in (-T)..T, term (fun k => (Λ k : ℂ)) (vline y) n‖
      ≤ 2 / ((n : ℝ) ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  simp_rw [term_vline_eq hn0]
  rw [intervalIntegral.integral_const_mul, norm_mul]
  have hA : ‖(Λ n : ℂ) / (n : ℂ) ^ (2 : ℂ)‖ = Λ n / (n : ℝ) ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    congr 1
    rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    rw [norm_pow, Complex.norm_natCast]
  rw [hA]
  have hexp := norm_integral_exp_le hL T
  have hΛ : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  calc Λ n / (n : ℝ) ^ 2
        * ‖∫ y in (-T)..T, Complex.exp ((-(Real.log n : ℂ) * I) * (y : ℂ))‖
      ≤ Λ n / (n : ℝ) ^ 2 * (2 / Real.log n) := by
        refine mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 2 / (n : ℝ) ^ 2 := by
        have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hn2]
        nlinarith [hΛ, hn2]

/-- The same bound for every `n`, including the two degenerate indices: `term _ _ 0 = 0` by
definition, and `term _ _ 1 = 0` because `Λ 1 = 0`. -/
theorem norm_integral_term_le' (n : ℕ) (T : ℝ) :
    ‖∫ y in (-T)..T, term (fun k => (Λ k : ℂ)) (vline y) n‖ ≤ 2 / ((n : ℝ) ^ 2) := by
  rcases lt_or_ge n 2 with h | h
  · interval_cases n
    · simp
    · simp [LSeries.term_of_ne_zero (one_ne_zero), ArithmeticFunction.vonMangoldt_apply_one]
  · exact norm_integral_term_le h T

theorem summable_two_div_sq : Summable fun n : ℕ => 2 / ((n : ℝ) ^ 2) := by
  have h : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h2 := h.mul_left 2
  simp_rw [mul_one_div] at h2
  exact h2

/-- **The prime channel is `O(1)`, uniformly in `T`.**  No `T` appears in the bound: the
oscillation `e^{-iy log n}` supplies a factor `1/log n` that cancels `Λ(n)` against `log n`,
and what is left is `∑ 2/n²`. -/
theorem exists_bound_prime_channel :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ‖∫ y in (-T)..T, logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  refine ⟨∑' n : ℕ, 2 / ((n : ℝ) ^ 2), tsum_nonneg (fun n => by positivity), fun T hT => ?_⟩
  have hle : (-T : ℝ) ≤ T := by linarith
  rw [Cvs.ZeroCounting.integral_logDeriv_zeta_interval hT, norm_neg]
  have hconv : ∀ n : ℕ, (∫ y in Set.Ioc (-T) T, term (fun k => (Λ k : ℂ)) (vline y) n)
      = ∫ y in (-T)..T, term (fun k => (Λ k : ℂ)) (vline y) n :=
    fun n => (intervalIntegral.integral_of_le hle).symm
  simp_rw [hconv]
  have hb : ∀ n : ℕ, ‖∫ y in (-T)..T, term (fun k => (Λ k : ℂ)) (vline y) n‖
      ≤ 2 / ((n : ℝ) ^ 2) := fun n => norm_integral_term_le' n T
  have hs2 : Summable fun n : ℕ =>
      ‖∫ y in (-T)..T, term (fun k => (Λ k : ℂ)) (vline y) n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb summable_two_div_sq
  exact le_trans (norm_tsum_le_tsum_norm hs2)
    (Summable.tsum_le_tsum hb hs2 summable_two_div_sq)

end Cvs.ZeroCounting
