import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Upstream.LinearPhaseIntegrationByParts
import Cvs.Zeta.ExplicitFormula.PoleFactorRealPart

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Sine Parseval on the centred window, and the tail of the sine projection

For continuous odd `h`, `∑_{k ≥ 0} (2/L)(∫_{−L/2}^{L/2} h(t) sin(2π(k+1)t/L) dt)² = ∫_{−L/2}^{L/2} h²`.
For odd `h` with a continuous derivative `h'`, the `k`-th sine overlap is at most `(2|h(L/2)| + ∫|h'|)·L/(2π(k+1))`,
so the energy outside the first `N` sine modes is at most `(2|h(L/2)| + ∫|h'|)²·L/(π²(N+1))`.
-/

noncomputable section

open MeasureTheory Real

namespace Cvs.StepA.SineParseval

variable {L : ℝ} {h : ℝ → ℝ}

/-! ### The Fourier coefficient of an odd function on the centred window -/

/-- The centred window `(−L/2, L/2]` has positive length when `L > 0`. -/
theorem neg_half_lt_half (hL : 0 < L) : -(L / 2) < L / 2 := neg_lt_self (half_pos hL)

/-- **The Fourier coefficient of an odd window function is `−i/L` times its sine overlap.** -/
theorem fourierCoeffOn_eq (hL : 0 < L) (hc : Continuous h) (hodd : ∀ t, h (-t) = -h t) (n : ℤ) :
    fourierCoeffOn (neg_half_lt_half hL) (fun t => (h t : ℂ)) n
      = ((-(L⁻¹ * ∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * n / L * t)) : ℝ) : ℂ)
          * Complex.I := by
  rw [fourierCoeffOn_eq_integral]
  have hT : L / 2 - -(L / 2) = L := by ring
  have hint : ∀ x : ℝ,
      (fourier (-n) ((x : ℝ) : AddCircle (L / 2 - -(L / 2)))) • ((h x : ℂ))
      = ((h x * Real.cos (2 * π * n / L * x) : ℝ) : ℂ)
        - ((h x * Real.sin (2 * π * n / L * x) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [smul_eq_mul, fourier_coe_apply]
    have harg : (2 * π * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / ((L / 2 - -(L / 2) : ℝ) : ℂ))
        = ((-(2 * π * (n : ℝ) / L * x) : ℝ) : ℂ) * Complex.I := by
      rw [hT]
      have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hi1 : IntervalIntegrable
      (fun x : ℝ => ((h x * Real.cos (2 * π * n / L * x) : ℝ) : ℂ)) volume (-(L / 2)) (L / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable
      (fun x : ℝ => ((h x * Real.sin (2 * π * n / L * x) : ℝ) : ℂ) * Complex.I)
      volume (-(L / 2)) (L / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcos : (∫ x in -(L / 2)..L / 2, h x * Real.cos (2 * π * n / L * x)) = 0 := by
    refine Cvs.Detection.integral_odd_eq_zero (fun x => ?_) (L / 2)
    rw [hodd, mul_neg, Real.cos_neg]
    ring
  have hkey : (∫ x in -(L / 2)..L / 2,
        (fourier (-n) ((x : ℝ) : AddCircle (L / 2 - -(L / 2)))) • ((h x : ℂ)))
      = -(((∫ x in -(L / 2)..L / 2, h x * Real.sin (2 * π * n / L * x) : ℝ) : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_congr (fun x _ => hint x),
      intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hcos]
    push_cast
    ring
  rw [hkey, hT, Complex.real_smul]
  push_cast
  ring

/-- **The squared modulus of the coefficient is the squared sine overlap over `L²`.** -/
theorem norm_fourierCoeffOn_sq (hL : 0 < L) (hc : Continuous h) (hodd : ∀ t, h (-t) = -h t)
    (n : ℤ) :
    ‖fourierCoeffOn (neg_half_lt_half hL) (fun t => (h t : ℂ)) n‖ ^ 2
      = (L⁻¹ * ∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * n / L * t)) ^ 2 := by
  rw [fourierCoeffOn_eq hL hc hodd n, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, neg_sq]

/-! ### Parseval for the sine modes -/

/-- **Sine Parseval on the centred window**: for a continuous odd `h`,
`∑_k (2/L)(∫ h(t) sin(2π(k+1)t/L) dt)² = ∫ h²` over `[−L/2, L/2]`. -/
theorem hasSum_sq_integral_sin (hL : 0 < L) (hc : Continuous h) (hodd : ∀ t, h (-t) = -h t) :
    HasSum (fun k : ℕ => 2 / L * (∫ t in -(L / 2)..L / 2,
        h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2)
      (∫ t in -(L / 2)..L / 2, h t ^ 2) := by
  set hab := neg_half_lt_half hL
  set G : ℝ → ℂ := fun t => (h t : ℂ) with hG
  set S : ℤ → ℝ := fun n => ∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * n / L * t) with hS
  set f : ℤ → ℝ := fun n => ‖fourierCoeffOn hab G n‖ ^ 2 with hf
  have hL2 : MemLp G 2 ((volume : Measure ℝ).restrict (Set.Ioc (-(L / 2)) (L / 2))) := by
    have hmeas : AEStronglyMeasurable G
        ((volume : Measure ℝ).restrict (Set.Ioc (-(L / 2)) (L / 2))) :=
      (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
    have hcont : Continuous (fun x : ℝ => ‖G x‖ ^ 2) := by
      rw [hG]; fun_prop
    exact hcont.integrableOn_Ioc
  have hpar := hasSum_sq_fourierCoeffOn hab hL2
  rw [← hf] at hpar
  have hval : ∀ n : ℤ, f n = (L⁻¹ * S n) ^ 2 := fun n => norm_fourierCoeffOn_sq hL hc hodd n
  have hSneg : ∀ n : ℤ, S (-n) = -S n := by
    intro n
    simp only [hS]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [show 2 * π * ((-n : ℤ) : ℝ) / L * x = -(2 * π * (n : ℝ) / L * x) by push_cast; ring,
      Real.sin_neg]
    ring
  have hS0 : S 0 = 0 := by simp [hS]
  have hfe : ∀ n : ℤ, f (-n) = f n := by
    intro n
    rw [hval, hval, hSneg, mul_neg, neg_sq]
  have hf0 : f 0 = 0 := by rw [hval, hS0, mul_zero, sq, mul_zero]
  have hfold := hpar.nat_add_neg
  have hstep : ∀ n : ℕ, f n + f (-(n : ℤ)) = 2 * f n := fun n => by rw [hfe]; ring
  simp only [hstep, hf0, add_zero] at hfold
  have hshift := (hasSum_nat_add_iff' 1).mpr hfold
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, hf0, mul_zero,
    sub_zero] at hshift
  have hscale := hshift.mul_left L
  have hnormG : ∀ x : ℝ, ‖G x‖ ^ 2 = h x ^ 2 := by
    intro x
    rw [hG]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have htot : L * ((L / 2 - -(L / 2))⁻¹ • ∫ x in -(L / 2)..L / 2, ‖G x‖ ^ 2)
      = ∫ t in -(L / 2)..L / 2, h t ^ 2 := by
    rw [intervalIntegral.integral_congr (fun x _ => hnormG x), smul_eq_mul,
      show L / 2 - -(L / 2) = L by ring]
    field_simp
  rw [htot] at hscale
  refine hscale.congr_fun (fun k => ?_)
  rw [hval]
  have hSk : S ((k + 1 : ℕ) : ℤ)
      = ∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * (k + 1) / L * t) := by
    simp only [hS]
    push_cast
    rfl
  rw [hSk]
  field_simp

/-! ### The sine overlap of a `C¹` function decays like `1/k` -/

/-- **The `k`-th sine overlap of an odd `C¹` function on the centred window** is at most
`(2|h(L/2)| + ∫|h'|)·L/(2π(k+1))`. -/
theorem abs_integral_mul_sin_le (hL : 0 < L) {h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t)
    (hc' : Continuous h') (hodd : ∀ t, h (-t) = -h t) (k : ℕ) :
    |∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * (k + 1) / L * t)|
      ≤ (2 * |h (L / 2)| + ∫ t in -(L / 2)..L / 2, |h' t|) * (L / (2 * π * (k + 1))) := by
  have hω : 0 < 2 * π * ((k : ℝ) + 1) / L := by positivity
  have e : ∀ t, Real.sin (2 * π * ((k : ℝ) + 1) / L * t)
      = Real.cos (2 * π * ((k : ℝ) + 1) / L * t + -(π / 2)) := fun t => by
    rw [← sub_eq_add_neg, Real.cos_sub_pi_div_two]
  simp_rw [e]
  have hle := Cvs.Upstream.LinearPhaseIntegrationByParts.abs_integral_mul_cos_le (a := h) (φ := -(π / 2))
    (neg_half_lt_half hL).le hω.ne' (fun t _ => hd t) hc'.continuousOn
  rw [hodd, abs_neg, abs_of_pos hω] at hle
  refine hle.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### The energy outside the first `N` sine modes -/

/-- **Tail of a series dominated by `c/(k+1)²`**: if `f` sums to `s` with `0 ≤ f k ≤ c/(k+1)²`, then
`s − ∑_{k<N} f k ≤ 2c/(N+1)`. -/
theorem sub_sum_range_le_of_le_inv_sq {f : ℕ → ℝ} {s c : ℝ} (hf : HasSum f s)
    (h0 : ∀ k, 0 ≤ f k) (hle : ∀ k : ℕ, f k ≤ c * (((k : ℝ) + 1) ^ 2)⁻¹) (N : ℕ) :
    s - ∑ k ∈ Finset.range N, f k ≤ 2 * c / (N + 1) := by
  have hc : 0 ≤ c := by
    have := (h0 0).trans (hle 0)
    norm_num at this
    exact this
  have hsplit := hf.summable.sum_add_tsum_nat_add N
  rw [hf.tsum_eq] at hsplit
  have htail : s - ∑ k ∈ Finset.range N, f k = ∑' i : ℕ, f (i + N) := by linarith
  rw [htail]
  refine Real.tsum_le_of_sum_range_le (fun i => h0 _) (fun n => ?_)
  have hreidx : ∑ i ∈ Finset.range n, ((((i + N : ℕ) : ℝ) + 1) ^ 2)⁻¹
      = ∑ m ∈ Finset.Ioo N (n + (N + 1)), ((m : ℝ) ^ 2)⁻¹ := by
    have e := Finset.sum_Ico_add' (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) 0 n (N + 1)
    rw [zero_add] at e
    rw [Finset.range_eq_Ico, ← Finset.Ico_add_one_left_eq_Ioo, ← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  have hinv := sum_Ioo_inv_sq_le (α := ℝ) N (n + (N + 1))
  calc ∑ i ∈ Finset.range n, f (i + N)
      ≤ ∑ i ∈ Finset.range n, c * ((((i + N : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun i _ => hle (i + N)
    _ = c * ∑ m ∈ Finset.Ioo N (n + (N + 1)), ((m : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.mul_sum, hreidx]
    _ ≤ c * (2 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hinv hc
    _ = 2 * c / (N + 1) := by ring

/-- **Projection tail**: for an odd `C¹` function on the centred window, the energy outside the first
`N` sine modes is at most `(2|h(L/2)| + ∫|h'|)²·L/(π²(N+1))`. -/
theorem integral_sq_sub_sum_le (hL : 0 < L) {h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t)
    (hc' : Continuous h') (hodd : ∀ t, h (-t) = -h t) (N : ℕ) :
    (∫ t in -(L / 2)..L / 2, h t ^ 2)
        - ∑ k ∈ Finset.range N, 2 / L * (∫ t in -(L / 2)..L / 2,
            h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2
      ≤ (2 * |h (L / 2)| + ∫ t in -(L / 2)..L / 2, |h' t|) ^ 2 * L / (π ^ 2 * (N + 1)) := by
  have hc : Continuous h := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  set C : ℝ := 2 * |h (L / 2)| + ∫ t in -(L / 2)..L / 2, |h' t|
  have hterm : ∀ k : ℕ, 2 / L * (∫ t in -(L / 2)..L / 2,
        h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2
      ≤ C ^ 2 * L / (2 * π ^ 2) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    intro k
    have hb := abs_integral_mul_sin_le hL hd hc' hodd k
    have hsq : (∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2
        ≤ (C * (L / (2 * π * (k + 1)))) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc 2 / L * (∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2
        ≤ 2 / L * (C * (L / (2 * π * (k + 1)))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = C ^ 2 * L / (2 * π ^ 2) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
          field_simp
  refine (sub_sum_range_le_of_le_inv_sq (hasSum_sq_integral_sin hL hc hodd)
    (fun k => by positivity) hterm N).trans (le_of_eq ?_)
  field_simp

end Cvs.StepA.SineParseval
