import Mathlib
import Cvs.Upstream.RemainingPrimeLogBounds
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant

/-!
# Sharp rational bounds for the archimedean constant

The accelerated sequence `H n - log n - 1/(2n) + 1/(12 n^2)` converges to Euler's constant with
fourth-order error, which puts `γ`, `log π` and `archSymbol 0` within `10⁻⁸` of explicit rationals.
-/

noncomputable section

namespace Cvs.WeilForm.Archimedean.ArchConstantRationalBounds

open Real Filter Topology Finset

/-- The Euler–Maclaurin corrected approximation to Euler's constant. -/
def cseq (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log (n : ℝ) - 1 / 2 * ((n : ℝ))⁻¹
    + 1 / 12 * (((n : ℝ))⁻¹ * ((n : ℝ))⁻¹)

/-- **The corrected sequence still converges to `γ`.** -/
theorem tendsto_cseq : Tendsto cseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul (1 / 2 : ℝ)
  have h2 : Tendsto (fun n : ℕ => (1 / 12 : ℝ) * (((n : ℝ))⁻¹ * ((n : ℝ))⁻¹)) atTop (𝓝 0) := by
    simpa using (hinv.mul hinv).const_mul (1 / 12 : ℝ)
  have h := (Real.tendsto_harmonic_sub_log.sub h1).add h2
  simp only [sub_zero, add_zero] at h
  exact h.congr fun n => by simp only [cseq]

/-- **The five-term Taylor bracket for `log (1 + 1/k)`.** -/
theorem abs_log_one_add_inv_sub_le {k : ℝ} (hk : 2 ≤ k) :
    |Real.log (1 + 1 / k) -
        (1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))| ≤
      1 / (k ^ 5 * (k - 1)) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hkinv : (0 : ℝ) < 1 / k := by positivity
  have habs : |(-(1 / k) : ℝ)| = 1 / k := by rw [abs_neg, abs_of_pos hkinv]
  have hx : |(-(1 / k) : ℝ)| < 1 := by rw [habs, div_lt_one hk0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 5
  rw [habs] at h
  have hsum : (∑ i ∈ Finset.range 5, (-(1 / k)) ^ (i + 1) / ((i : ℝ) + 1))
      = -(1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    field_simp
    ring
  have h1x : (1 : ℝ) - -(1 / k) = 1 + 1 / k := by ring
  rw [hsum, h1x] at h
  have hk1 : (0 : ℝ) < k - 1 := by linarith
  have hrhs : (1 / k) ^ (5 + 1) / (1 - 1 / k) = 1 / (k ^ 5 * (k - 1)) := by
    rw [div_eq_div_iff (by
      have : (0:ℝ) < 1 - 1 / k := by
        rw [sub_pos, div_lt_one hk0]; linarith
      exact ne_of_gt this) (by positivity)]
    have hkne : k ≠ 0 := ne_of_gt hk0
    have hk1ne : k - 1 ≠ 0 := ne_of_gt hk1
    field_simp
    rw [← mul_pow, one_div, mul_inv_cancel₀ hkne, one_pow]
  rw [hrhs] at h
  have hcongr : |Real.log (1 + 1 / k) -
      (1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))|
      = |-(1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))
          + Real.log (1 + 1 / k)| := by
    congr 1; ring
  rw [hcongr]
  exact h

/-- **The Taylor part is at most `(7/200)/k⁵`.** -/
theorem taylor_le {k : ℝ} (hk : 64 ≤ k) :
    (1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))
        - 1 / (k + 1) - 1 / (2 * k * (k + 1)) + (2 * k + 1) / (12 * k ^ 2 * (k + 1) ^ 2)
      ≤ (7 / 200) / k ^ 5 := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  rw [← sub_nonneg]
  have key : (7 / 200) / k ^ 5 -
      ((1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))
        - 1 / (k + 1) - 1 / (2 * k * (k + 1)) + (2 * k + 1) / (12 * k ^ 2 * (k + 1) ^ 2))
      = (k ^ 2 - 48 * k - 99) / (600 * k ^ 5 * (k + 1) ^ 2) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  nlinarith [hk]

/-- **The Taylor part is at least `(1/40)/k⁵`.** -/
theorem le_taylor {k : ℝ} (hk : 64 ≤ k) :
    (1 / 40) / k ^ 5 ≤
      (1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))
        - 1 / (k + 1) - 1 / (2 * k * (k + 1)) + (2 * k + 1) / (12 * k ^ 2 * (k + 1) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  rw [← sub_nonneg]
  have key : ((1 / k - 1 / (2 * k ^ 2) + 1 / (3 * k ^ 3) - 1 / (4 * k ^ 4) + 1 / (5 * k ^ 5))
        - 1 / (k + 1) - 1 / (2 * k * (k + 1)) + (2 * k + 1) / (12 * k ^ 2 * (k + 1) ^ 2))
      - (1 / 40) / k ^ 5
      = (5 * k ^ 2 + 60 * k + 105) / (600 * k ^ 5 * (k + 1) ^ 2) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  nlinarith [hk]

/-- **The increment of the corrected sequence, in closed form.** -/
theorem cseq_sub_succ {k : ℕ} (hk : 1 ≤ k) :
    cseq k - cseq (k + 1)
      = Real.log (1 + 1 / (k : ℝ)) - 1 / ((k : ℝ) + 1) - 1 / (2 * (k : ℝ) * ((k : ℝ) + 1))
        + (2 * (k : ℝ) + 1) / (12 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hH : ((harmonic (k + 1) : ℚ) : ℝ) = ((harmonic k : ℚ) : ℝ) + 1 / ((k : ℝ) + 1) := by
    rw [harmonic_succ]; push_cast; ring
  have hlog : Real.log ((k : ℝ) + 1) = Real.log (k : ℝ) + Real.log (1 + 1 / (k : ℝ)) := by
    rw [← Real.log_mul (ne_of_gt hk0) (by positivity)]
    congr 1
    field_simp
  simp only [cseq, Nat.cast_add, Nat.cast_one]
  rw [hH, hlog]
  field_simp
  ring

/-- **Each increment is at most `(1/16)/k⁵`.** -/
theorem cseq_sub_succ_le {k : ℕ} (hk : 64 ≤ k) :
    cseq k - cseq (k + 1) ≤ (1 / 16) / (k : ℝ) ^ 5 := by
  have hkR : (64 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  rw [cseq_sub_succ (by omega)]
  have hb := abs_log_one_add_inv_sub_le (k := (k : ℝ)) (by linarith)
  have hb' := (abs_le.mp hb).2
  have ht := taylor_le (k := (k : ℝ)) hkR
  have htail : 1 / ((k : ℝ) ^ 5 * ((k : ℝ) - 1)) ≤ (1 / 63) / (k : ℝ) ^ 5 := by
    rw [div_le_div_iff₀ (mul_pos (pow_pos hk0 5) (by linarith : (0 : ℝ) < (k : ℝ) - 1))
      (by positivity)]
    nlinarith [hkR, pow_pos hk0 5]
  have hsum : (7 / 200) / (k : ℝ) ^ 5 + (1 / 63) / (k : ℝ) ^ 5 ≤ (1 / 16) / (k : ℝ) ^ 5 := by
    have hcomb : (7 / 200 : ℝ) / (k : ℝ) ^ 5 + (1 / 63) / (k : ℝ) ^ 5
        = (641 / 12600) / (k : ℝ) ^ 5 := by ring
    rw [hcomb, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hk0 5]
  linarith

/-- **Each increment is positive.** -/
theorem cseq_succ_lt {k : ℕ} (hk : 64 ≤ k) : cseq (k + 1) < cseq k := by
  have hkR : (64 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hpos : 0 < cseq k - cseq (k + 1) := by
    rw [cseq_sub_succ (by omega)]
    have hb := abs_log_one_add_inv_sub_le (k := (k : ℝ)) (by linarith)
    have hb' := (abs_le.mp hb).1
    have ht := le_taylor (k := (k : ℝ)) hkR
    have htail : 1 / ((k : ℝ) ^ 5 * ((k : ℝ) - 1)) ≤ (1 / 63) / (k : ℝ) ^ 5 := by
      rw [div_le_div_iff₀ (mul_pos (pow_pos hk0 5) (by linarith : (0 : ℝ) < (k : ℝ) - 1))
        (by positivity)]
      nlinarith [hkR, pow_pos hk0 5]
    have hgap : (1 / 63) / (k : ℝ) ^ 5 < (1 / 40) / (k : ℝ) ^ 5 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hk0 5]
    linarith
  linarith

/-- **The telescoping majorant.** -/
theorem tele_step {k : ℝ} (hk : 2 ≤ k) :
    (1 / 16) / k ^ 5 ≤ (1 / 64) * (1 / (k - 1) ^ 4 - 1 / k ^ 4) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < k - 1 := by linarith
  rw [← sub_nonneg]
  have key : (1 / 64) * (1 / (k - 1) ^ 4 - 1 / k ^ 4) - (1 / 16) / k ^ 5
      = (10 * k ^ 3 - 20 * k ^ 2 + 15 * k - 4) / (64 * k ^ 5 * (k - 1) ^ 4) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  nlinarith [hk]

/-- **The telescoped bound between two indices.** -/
theorem cseq_sub_le (N : ℕ) (hN : 64 ≤ N) :
    ∀ M, N ≤ M → cseq N - cseq M ≤ (1 / 64) * (1 / ((N : ℝ) - 1) ^ 4 - 1 / ((M : ℝ) - 1) ^ 4) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hM64 : 64 ≤ M := le_trans hN hNM
      have hMR : (64 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM64
      have hd := cseq_sub_succ_le hM64
      have ht := tele_step (k := (M : ℝ)) (by linarith)
      have hsplit : cseq N - cseq (M + 1) = (cseq N - cseq M) + (cseq M - cseq (M + 1)) := by ring
      have hcast : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
      rw [hsplit, hcast]
      linarith

/-- **Euler's constant is below every corrected term.** -/
theorem gamma_le_cseq (N : ℕ) (hN : 64 ≤ N) : Real.eulerMascheroniConstant ≤ cseq N := by
  have h : ∀ M, N ≤ M → cseq M ≤ cseq N := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => exact le_refl _
    | succ M hNM ih =>
        have := cseq_succ_lt (k := M) (le_trans hN hNM)
        linarith
  refine le_of_tendsto tendsto_cseq ?_
  filter_upwards [eventually_ge_atTop N] with M hM using h M hM

/-- **The corrected term is above `γ` by at most the fourth-order tail.** -/
theorem cseq_sub_gamma_le (N : ℕ) (hN : 64 ≤ N) :
    cseq N - Real.eulerMascheroniConstant ≤ (1 / 64) * (1 / ((N : ℝ) - 1) ^ 4) := by
  have h : Tendsto (fun M : ℕ => cseq N - cseq M) atTop
      (𝓝 (cseq N - Real.eulerMascheroniConstant)) := tendsto_const_nhds.sub tendsto_cseq
  refine le_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  have hb := cseq_sub_le N hN M hM
  have hpos : (0 : ℝ) ≤ 1 / ((M : ℝ) - 1) ^ 4 := by positivity
  nlinarith [hb, hpos]

set_option maxHeartbeats 6400000 in
/-- **The sixty-fourth harmonic number.** -/
theorem harmonic_64_eq :
    ((harmonic 64 : ℚ) : ℝ)
      = (623171679694215690971693339 : ℝ) / 131362987122535807501262400 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- **The logarithm of sixty-four.** -/
theorem log_64_eq : Real.log 64 = 6 * Real.log 2 := by
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- **The sixty-fourth corrected term, in closed form.** -/
theorem cseq_64_eq :
    cseq 64 = (623171679694215690971693339 : ℝ) / 131362987122535807501262400
      - 6 * Real.log 2 - 1 / 128 + 1 / 49152 := by
  simp only [cseq]
  norm_num [harmonic_64_eq, log_64_eq]

set_option maxHeartbeats 1600000 in
/-- **Euler's constant, from above.** -/
theorem gamma_upper : Real.eulerMascheroniConstant < 0.5772156670 := by
  have h := gamma_le_cseq 64 (by norm_num)
  rw [cseq_64_eq] at h
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **Euler's constant, from below.** -/
theorem gamma_lower : (0.5772156629 : ℝ) < Real.eulerMascheroniConstant := by
  have h := cseq_sub_gamma_le 64 (by norm_num)
  rw [cseq_64_eq] at h
  have hl2 := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

/-- **A twelve-term upper bound for the exponential at half the logarithm of `π`.** -/
theorem exp_half_le : Real.exp (0.5723649427 : ℝ) ≤ 1.7724538506 :=
  Cvs.Moments.exp_le_of_sum (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- **A twelve-term lower bound for the exponential at half the logarithm of `π`.** -/
theorem le_exp_half : (1.7724538512 : ℝ) ≤ Real.exp (0.5723649432 : ℝ) :=
  Cvs.Moments.le_exp_of_sum (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- **The logarithm of `π`, from below.** -/
theorem log_pi_lower : (1.1447298854 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have hdouble : Real.exp (1.1447298854 : ℝ)
      = Real.exp (0.5723649427 : ℝ) * Real.exp (0.5723649427 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have hpos : (0 : ℝ) < Real.exp (0.5723649427 : ℝ) := Real.exp_pos _
  have hsq : Real.exp (1.1447298854 : ℝ) ≤ (1.7724538506 : ℝ) * 1.7724538506 := by
    rw [hdouble]
    exact mul_le_mul exp_half_le exp_half_le (le_of_lt hpos) (by norm_num)
  have hpi := Real.pi_gt_d20
  nlinarith [hsq, hpi]

/-- **The logarithm of `π`, from above.** -/
theorem log_pi_upper : Real.log Real.pi < 1.1447298864 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have hdouble : Real.exp (1.1447298864 : ℝ)
      = Real.exp (0.5723649432 : ℝ) * Real.exp (0.5723649432 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have hsq : (1.7724538512 : ℝ) * 1.7724538512 ≤ Real.exp (1.1447298864 : ℝ) := by
    rw [hdouble]
    exact mul_le_mul le_exp_half le_exp_half (by norm_num) (le_of_lt (Real.exp_pos _))
  have hpi := Real.pi_lt_d20
  nlinarith [hsq, hpi]

/-- **The archimedean constant, to eight decimal places.** -/
theorem archSymbol_zero_bounds :
    (-5.3721834231 : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      ∧ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ -5.3721834158 := by
  rw [Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_eq]
  have hg1 := gamma_lower
  have hg2 := gamma_upper
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  have hlp1 := log_pi_lower
  have hlp2 := log_pi_upper
  constructor <;> linarith

end Cvs.WeilForm.Archimedean.ArchConstantRationalBounds
