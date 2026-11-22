import Mathlib
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Route.Visibility.ReflectedRemainderMellin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Plancherel bounds for the sawtooth transform and its antiderivative

For `G′` continuous on `[0, 1]` and `x ≥ 0`: `‖T‖_{L²(x,∞)} ≤ ζ(3/2)‖G′‖₂/(2π)`, via `S(u) = Σ sin(2πnu)/(πn)`
in `L²(0, 1)`, Minkowski over the modes and the half-line Plancherel `∫_0^∞ S_g² = ‖g‖²/4` from Parseval on
`[−1, 1]` with shifted frequencies. If also `G′(t)/t ∈ L²`, `‖Ψ‖_{L²(x,∞)} ≤ ζ(5/2)‖G′/t‖₂/(4π²)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped Interval ENNReal
open Cvs.Route.Visibility.ProjectionShareSawtooth (saw)
open Cvs.Route.Visibility.ReflectedRemainderMellin (sawT)

namespace Cvs.Route.Visibility.SawtoothPlancherelBounds

/-! ### `L²` norms as lintegrals of squares, and Minkowski over a series -/

/-- `‖φ‖_{L²(μ)} = (∫⁻ φ²)^{1/2}`. -/
theorem eLpNorm_two_eq {μ : Measure ℝ} (φ : ℝ → ℝ) (hφ : AEStronglyMeasurable φ μ) :
    eLpNorm φ 2 μ = (∫⁻ y, ENNReal.ofReal (φ y ^ 2) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hφ]
  congr 2
  · ext y
    rw [Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two, Real.rpow_two, sq_abs]

/-- `‖φ‖_{L²(μ)} ≤ b` iff `∫⁻ φ² ≤ b²`, for `b ≥ 0`. -/
theorem eLpNorm_two_le_iff {μ : Measure ℝ} (φ : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hφ : AEStronglyMeasurable φ μ) :
    eLpNorm φ 2 μ ≤ ENNReal.ofReal b ↔ ∫⁻ y, ENNReal.ofReal (φ y ^ 2) ∂μ ≤ ENNReal.ofReal (b ^ 2) := by
  rw [eLpNorm_two_eq φ hφ, one_div, ENNReal.rpow_inv_le_iff two_pos, ENNReal.ofReal_pow hb,
    ENNReal.rpow_two]

/-- **Minkowski over a series with Fatou**: if `Σ_{n<N} ψₙ → f` a.e. and `‖ψₙ‖₂ ≤ cₙ`, then
`‖f‖₂ ≤ Σ cₙ`. -/
theorem eLpNorm_le_of_tendsto_sum {μ : Measure ℝ} {ψ : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℕ → ℝ}
    (hψ : ∀ n, AEStronglyMeasurable (ψ n) μ) (hc : ∀ n, eLpNorm (ψ n) 2 μ ≤ ENNReal.ofReal (c n))
    (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c)
    (hlim : ∀ᵐ y ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, ψ n y) atTop (𝓝 (f y))) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (∑' n, c n) := by
  have hmeas : ∀ N, AEStronglyMeasurable (fun y => ∑ n ∈ Finset.range N, ψ n y) μ := fun N =>
    Finset.aestronglyMeasurable_sum (Finset.range N) (fun n _ => hψ n) |>.congr (by
      filter_upwards with y; simp [Finset.sum_apply])
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas f
    (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) hlim).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
  have h1 : eLpNorm (fun y => ∑ n ∈ Finset.range N, ψ n y) 2 μ
      ≤ ∑ n ∈ Finset.range N, eLpNorm (ψ n) 2 μ := by
    have := eLpNorm_sum_le (μ := μ) (p := 2) (s := Finset.range N) (f := ψ) one_le_two
    convert this using 2
    ext y; simp [Finset.sum_apply]
  refine h1.trans ((Finset.sum_le_sum fun n _ => hc n).trans ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => hc0 n]
  exact ENNReal.ofReal_le_ofReal (hcs.sum_le_tsum _ fun n _ => hc0 n)

/-- **Dilation of a lintegral**: `∫⁻ f(cy) dy = c⁻¹ ∫⁻ f` for `c > 0`. -/
theorem lintegral_comp_mul_left {f : ℝ → ℝ≥0∞} (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    ∫⁻ y, f (c * y) = ENNReal.ofReal c⁻¹ * ∫⁻ y, f y := by
  have hm : Measurable (fun y : ℝ => c * y) := measurable_const.mul measurable_id
  rw [← lintegral_map hf hm, Real.map_volume_mul_left hc.ne', lintegral_smul_measure,
    abs_of_pos (inv_pos.2 hc)]
  rfl

/-! ### Plancherel for the sine and cosine transforms on `[0, 1]` -/

/-- The sine transform `S_h(ξ) = ∫₀¹ h(t) sin(2πξt) dt`. -/
def sinT (h : ℝ → ℝ) (ξ : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, h t * Real.sin (2 * π * ξ * t)

section Mode

variable {h : ℝ → ℝ} (hm : Measurable h) (hi : IntegrableOn (fun t => h t ^ 2) (Ioc 0 1))
include hm hi

end Mode

/-! ### From a shifted Parseval identity to a half-line `L²` bound -/

section Lattice

variable {Φ : ℝ → ℝ} {A : ℝ} (hΦ : Continuous Φ) (hA : ∀ θ : ℝ, HasSum (fun k : ℤ => Φ ((k + θ) / 2) ^ 2) A)
include hΦ hA

end Lattice

/-! ### The sine and cosine transforms of an `L²` profile -/

section Transforms

variable {h : ℝ → ℝ} (hm : Measurable h) (hi : IntegrableOn (fun t => h t ^ 2) (Ioc 0 1))
include hm hi

end Transforms

/-! ### The sine partial sums of the sawtooth and their `L²` error -/

section Sawtooth

/-- `∫₀¹ cos(2πku) du = 0` for a nonzero integer `k`. -/
theorem integral_cos_int_mul {k : ℤ} (hk : k ≠ 0) : ∫ u in (0 : ℝ)..1, Real.cos (2 * π * k * u) = 0 := by
  have hc : (2 * π * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
    positivity
  rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hc, integral_cos, mul_one, mul_zero,
    Real.sin_zero, sub_zero, show (2 * π * k : ℝ) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring,
    Real.sin_int_mul_pi, smul_zero]

/-- `∫₀¹ (½ − u)² du = 1/12`. -/
theorem integral_half_sub_sq : ∫ u in (0 : ℝ)..1, (1 / 2 - u) ^ 2 = 1 / 12 := by
  have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => -(1 / 2 - u) ^ 3 / 3) ((1 / 2 - u) ^ 2) u := by
    intro u _
    have := (((hasDerivAt_id u).const_sub (1 / 2)).pow 3).neg.div_const 3
    exact this.congr_deriv (by simp only [id]; norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- `∫₀¹ (½ − u) sin(2πnu) du = 1/(2πn)` (both sides vanish at `n = 0`). -/
theorem integral_half_sub_mul_sin (n : ℕ) :
    ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.sin (2 * π * n * u) = 1 / (2 * π * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set a : ℝ := 2 * π * n
  have ha : a ≠ 0 := by
    have : (0 : ℝ) < n := Nat.cast_pos.2 hn
    positivity
  have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => -(1 / 2 - u) * Real.cos (a * u) / a - Real.sin (a * u) / a ^ 2)
      ((1 / 2 - u) * Real.sin (a * u)) u := by
    intro u _
    have h1 := ((hasDerivAt_id u).const_mul a)
    have h2 := (((hasDerivAt_id u).const_sub (1 / 2)).neg.mul (h1.cos)).div_const a
    have h3 := (h1.sin).div_const (a ^ 2)
    refine (h2.sub h3).congr_deriv ?_
    simp only [id, mul_one, Pi.neg_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hc : Real.cos a = 1 := by
    rw [show a = (n : ℝ) * (2 * π) by ring]; exact Real.cos_nat_mul_two_pi n
  have hs : Real.sin a = 0 := by
    rw [show a = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]; exact Real.sin_nat_mul_pi _
  simp only [mul_one, mul_zero, Real.cos_zero, Real.sin_zero, hc, hs]
  field_simp
  ring

/-- **Orthogonality of the sines** on `[0, 1]`. -/
theorem integral_sin_mul_sin (n m : ℕ) :
    ∫ u in (0 : ℝ)..1, Real.sin (2 * π * n * u) * Real.sin (2 * π * m * u)
      = if n = m then (if n = 0 then 0 else 1 / 2) else 0 := by
  have e : ∀ u : ℝ, Real.sin (2 * π * n * u) * Real.sin (2 * π * m * u)
      = (Real.cos (2 * π * ((n : ℤ) - m : ℤ) * u) - Real.cos (2 * π * ((n : ℤ) + m : ℤ) * u)) / 2 := by
    intro u
    push_cast
    rw [show 2 * π * ((n : ℝ) - m) * u = 2 * π * n * u - 2 * π * m * u by ring,
      show 2 * π * ((n : ℝ) + m) * u = 2 * π * n * u + 2 * π * m * u by ring, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  by_cases hnm : n = m
  · subst hnm
    by_cases h0 : n = 0
    · subst h0; simp
    · have h2 : ((n : ℤ) + n) ≠ 0 := by omega
      rw [integral_cos_int_mul h2]
      simp [h0]
  · have h1 : ((n : ℤ) - m) ≠ 0 := by omega
    have h2 : ((n : ℤ) + m) ≠ 0 := by omega
    rw [integral_cos_int_mul h1, integral_cos_int_mul h2]
    simp [hnm]

/-- The coefficient `1/(πn)` of the sawtooth's sine series (zero at `n = 0`). -/
def sawC (n : ℕ) : ℝ := 1 / (π * n)

/-- The partial sum `S_N(u) = Σ_{n<N} sin(2πnu)/(πn)` of the sawtooth's sine series. -/
def sawS (N : ℕ) (u : ℝ) : ℝ := ∑ n ∈ Finset.range N, sawC n * Real.sin (2 * π * n * u)

/-- The error `e_N = S − S_N` of the partial sum. -/
def sawE (N : ℕ) (u : ℝ) : ℝ := saw u - sawS N u

theorem continuous_sawS (N : ℕ) : Continuous (sawS N) := by
  unfold sawS; fun_prop

theorem sawC_mul_div (n : ℕ) : sawC n * (1 / (2 * π * n)) = 1 / (2 * π ^ 2 * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sawC]
  · have : (0 : ℝ) < n := Nat.cast_pos.2 hn
    unfold sawC; field_simp

/-- **Parseval for the partial sums**: `∫₀¹ (½ − u − S_N(u))² du = 1/12 − Σ_{n<N} 1/(2π²n²)`. -/
theorem integral_half_sub_sub_sawS_sq (N : ℕ) :
    ∫ u in (0 : ℝ)..1, (1 / 2 - u - sawS N u) ^ 2
      = 1 / 12 - ∑ n ∈ Finset.range N, 1 / (2 * π ^ 2 * n ^ 2) := by
  set s : ℕ → ℝ → ℝ := fun n u => Real.sin (2 * π * n * u)
  have pt : ∀ u, (1 / 2 - u - sawS N u) ^ 2 = (1 / 2 - u) ^ 2
      - 2 * ∑ n ∈ Finset.range N, sawC n * ((1 / 2 - u) * s n u)
      + ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, sawC n * sawC m * (s n u * s m u) := by
    intro u
    have h1 : (1 / 2 - u) * sawS N u = ∑ n ∈ Finset.range N, sawC n * ((1 / 2 - u) * s n u) := by
      rw [sawS, Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    have h2 : sawS N u ^ 2 = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, sawC n * sawC m * (s n u * s m u) := by
      rw [sq, sawS, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
    rw [← h1, ← h2]; ring
  simp_rw [pt]
  have ci : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 1 :=
    fun f hf => hf.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (ci _ (by fun_prop)) (ci _ (by fun_prop)),
    intervalIntegral.integral_sub (ci _ (by fun_prop)) (ci _ (by fun_prop)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun n _ => ci _ (by fun_prop)),
    intervalIntegral.integral_finsetSum (fun n _ => ci _ (by fun_prop)), integral_half_sub_sq]
  rw [Finset.sum_congr rfl fun n _ => intervalIntegral.integral_finsetSum
    (fun m _ => ci (fun u => sawC n * sawC m * (s n u * s m u)) (by fun_prop))]
  simp_rw [intervalIntegral.integral_const_mul, s, integral_half_sub_mul_sin, integral_sin_mul_sin]
  have hdiag : ∀ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      sawC n * sawC m * (if n = m then (if n = 0 then (0 : ℝ) else 1 / 2) else 0)
        = 1 / (2 * π ^ 2 * n ^ 2) := by
    intro n hn
    rw [Finset.sum_eq_single n (fun m _ hmn => by simp [Ne.symm hmn]) (fun h => absurd hn h)]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have : (0 : ℝ) < n := Nat.cast_pos.2 hn0
      simp only [ite_true, hn0.ne', ite_false, sawC]
      field_simp
  rw [Finset.sum_congr rfl hdiag]
  simp_rw [sawC_mul_div]
  ring

theorem measurable_sawE (N : ℕ) : Measurable (sawE N) :=
  Cvs.Route.Visibility.ProjectionShareSawtooth.measurable_saw.sub (continuous_sawS N).measurable

theorem periodic_sawE (N : ℕ) : Function.Periodic (sawE N) 1 := by
  intro u
  have hs : sawS N (u + 1) = sawS N u := by
    unfold sawS
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 2 * π * n * (u + 1) = 2 * π * n * u + n * (2 * π) by ring, Real.sin_add_nat_mul_two_pi]
  simp only [sawE, hs, saw, Int.fract_add_one]

theorem abs_sawE_le (N : ℕ) (u : ℝ) : |sawE N u| ≤ 1 / 2 + ∑ n ∈ Finset.range N, |sawC n| := by
  have hS : |sawS N u| ≤ ∑ n ∈ Finset.range N, |sawC n| := by
    unfold sawS
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  unfold sawE
  exact (abs_sub _ _).trans (add_le_add (Cvs.Route.Visibility.ProjectionShareSawtooth.abs_saw_le u) hS)

theorem intervalIntegrable_sawE_sq (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => sawE N u ^ 2) volume a b := by
  set K := 1 / 2 + ∑ n ∈ Finset.range N, |sawC n|
  refine (intervalIntegrable_const (c := K ^ 2)).mono_fun' ((measurable_sawE N).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sawE_le N u) 2

/-- `∫₀¹ e_N² = 1/12 − Σ_{n<N} 1/(2π²n²)`. -/
theorem integral_sawE_sq (N : ℕ) :
    ∫ u in (0 : ℝ)..1, sawE N u ^ 2 = 1 / 12 - ∑ n ∈ Finset.range N, 1 / (2 * π ^ 2 * n ^ 2) := by
  rw [← integral_half_sub_sub_sawS_sq N]
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
    rw [ae_iff]; simp
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hne] with u hu1 hu
  rw [uIoc_of_le zero_le_one] at hu
  have hf : Int.fract u = u := Int.fract_eq_self.2 ⟨hu.1.le, lt_of_le_of_ne hu.2 hu1⟩
  simp only [sawE, saw, hf]

/-- `∫₀¹ e_N² → 0` (Basel). -/
theorem tendsto_integral_sawE_sq :
    Tendsto (fun N => ∫ u in (0 : ℝ)..1, sawE N u ^ 2) atTop (𝓝 0) := by
  simp_rw [integral_sawE_sq]
  have h := (hasSum_zeta_two.mul_left (1 / (2 * π ^ 2))).tendsto_sum_nat
  have e1 : 1 / (2 * π ^ 2) * (π ^ 2 / 6) = 1 / 12 := by field_simp; ring
  rw [e1] at h
  have e2 : ∀ n : ℕ, 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) = 1 / (2 * π ^ 2 * n ^ 2) := fun n => by
    rw [one_div_mul_one_div]
  simp_rw [e2] at h
  simpa using h.const_sub (1 / 12 : ℝ)

/-- **Dilation of the error**: `∫₀¹ e_N(yt)² dt ≤ (⌈y⌉/y) ∫₀¹ e_N²` for `y > 0`. -/
theorem integral_sawE_comp_sq_le (N : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ t in (0 : ℝ)..1, sawE N (y * t) ^ 2 ≤ (⌈y⌉₊ / y) * ∫ u in (0 : ℝ)..1, sawE N u ^ 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun u => sawE N u ^ 2) hy.ne', mul_zero, mul_one, smul_eq_mul]
  have hper : Function.Periodic (fun u => sawE N u ^ 2) 1 := fun u => by simp only [periodic_sawE N u]
  have hK := hper.intervalIntegral_add_zsmul_eq (⌈y⌉₊ : ℤ) 0 (intervalIntegrable_sawE_sq N)
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast] at hK
  have hle : ∫ u in (0 : ℝ)..y, sawE N u ^ 2 ≤ ∫ u in (0 : ℝ)..⌈y⌉₊, sawE N u ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_sawE_sq N 0 y)
      (intervalIntegrable_sawE_sq N y (⌈y⌉₊ : ℝ))]
    have : 0 ≤ ∫ u in y..(⌈y⌉₊ : ℝ), sawE N u ^ 2 :=
      intervalIntegral.integral_nonneg (Nat.le_ceil y) fun u _ => sq_nonneg _
    linarith
  rw [hK] at hle
  rw [div_mul_eq_mul_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hle hy.le

end Sawtooth

/-! ### Convergence of the mode sums to `T` -/

section Modes

/-- **Weighted Cauchy–Schwarz**: `|∫₀¹ fk| ≤ (ε∫₀¹f² + ε⁻¹∫₀¹k²)/2` for `ε > 0`. -/
theorem abs_integral_mul_le {f k : ℝ → ℝ} (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 1)
    (hk2 : IntervalIntegrable (fun t => k t ^ 2) volume 0 1)
    (hfk : IntervalIntegrable (fun t => f t * k t) volume 0 1) {ε : ℝ} (hε : 0 < ε) :
    |∫ t in (0 : ℝ)..1, f t * k t|
      ≤ (ε * ∫ t in (0 : ℝ)..1, f t ^ 2) / 2 + (ε⁻¹ * ∫ t in (0 : ℝ)..1, k t ^ 2) / 2 := by
  have pt : ∀ t, |f t * k t| ≤ ε * f t ^ 2 / 2 + ε⁻¹ * k t ^ 2 / 2 := by
    intro t
    have h := sq_nonneg (ε * |f t| - |k t|)
    rw [abs_mul, ← sq_abs (f t), ← sq_abs (k t)]
    have e : ε * |f t| ^ 2 / 2 + ε⁻¹ * |k t| ^ 2 / 2 - |f t| * |k t|
        = (ε * |f t| - |k t|) ^ 2 / (2 * ε) := by field_simp; ring
    have : 0 ≤ (ε * |f t| - |k t|) ^ 2 / (2 * ε) := by positivity
    linarith
  calc |∫ t in (0 : ℝ)..1, f t * k t| ≤ ∫ t in (0 : ℝ)..1, |f t * k t| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, (ε * f t ^ 2 / 2 + ε⁻¹ * k t ^ 2 / 2) :=
        intervalIntegral.integral_mono_on zero_le_one hfk.abs
          (((hf2.const_mul ε).div_const 2).add ((hk2.const_mul ε⁻¹).div_const 2)) fun t _ => pt t
    _ = _ := by
        rw [intervalIntegral.integral_add ((hf2.const_mul ε).div_const 2) ((hk2.const_mul ε⁻¹).div_const 2),
          intervalIntegral.integral_div, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]

theorem intervalIntegrable_sawE_comp_sq (N : ℕ) (y : ℝ) :
    IntervalIntegrable (fun t => sawE N (y * t) ^ 2) volume 0 1 := by
  set K := 1 / 2 + ∑ n ∈ Finset.range N, |sawC n|
  refine (intervalIntegrable_const (c := K ^ 2)).mono_fun'
    (((measurable_sawE N).comp (measurable_const.mul measurable_id)).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sawE_le N _) 2

variable {g : ℝ → ℝ} (hg : Continuous g)
include hg

/-- **The mode sum and the error**: `T(y) − Σ_{n<N} S_g(ny)/(πn) = ∫₀¹ g(t) e_N(yt) dt`. -/
theorem sawT_sub_sum_eq (N : ℕ) (y : ℝ) :
    sawT g y - ∑ n ∈ Finset.range N, sawC n * sinT g (n * y)
      = ∫ t in (0 : ℝ)..1, g t * sawE N (y * t) := by
  have hS : ∑ n ∈ Finset.range N, sawC n * sinT g (n * y) = ∫ t in (0 : ℝ)..1, g t * sawS N (y * t) := by
    simp only [sinT, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum (fun n _ => (Continuous.intervalIntegrable (by fun_prop) _ _))]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [sawS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 2 * π * (n * y) * t = 2 * π * n * (y * t) by ring]; ring
  have h1 := Cvs.Route.Visibility.ReflectedRemainderMellin.intervalIntegrable_mul_saw hg.continuousOn y
  have h2 : IntervalIntegrable (fun t => g t * sawS N (y * t)) volume 0 1 :=
    Continuous.intervalIntegrable (hg.mul ((continuous_sawS N).comp (by fun_prop))) _ _
  rw [hS, Cvs.Route.Visibility.ReflectedRemainderMellin.sawT, ← intervalIntegral.integral_sub h1 h2]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [sawE]; ring

/-- **Pointwise convergence of the mode sum**: `Σ_{n<N} S_g(ny)/(πn) → T(y)` for `y > 0`. -/
theorem tendsto_sum_sinT {y : ℝ} (hy : 0 < y) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, sawC n * sinT g (n * y)) atTop (𝓝 (sawT g y)) := by
  set A := ∫ t in (0 : ℝ)..1, g t ^ 2
  set K := (⌈y⌉₊ : ℝ) / y
  set E : ℕ → ℝ := fun N => ∫ u in (0 : ℝ)..1, sawE N u ^ 2
  have hE0 : ∀ N, 0 ≤ E N := fun N => intervalIntegral.integral_nonneg zero_le_one fun u _ => sq_nonneg _
  have hK0 : 0 ≤ K := by positivity
  set ε : ℕ → ℝ := fun N => √(E N) + 1 / ((N : ℝ) + 1)
  have hε : ∀ N, 0 < ε N := fun N => by positivity
  have hbound : ∀ N, dist (∑ n ∈ Finset.range N, sawC n * sinT g (n * y)) (sawT g y)
      ≤ (ε N * A) / 2 + (K * √(E N)) / 2 := by
    intro N
    rw [dist_comm, Real.dist_eq, sawT_sub_sum_eq hg]
    have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have hgk : IntervalIntegrable (fun t => g t * sawE N (y * t)) volume 0 1 := by
      have h1 := Cvs.Route.Visibility.ReflectedRemainderMellin.intervalIntegrable_mul_saw hg.continuousOn y
      have h2 : IntervalIntegrable (fun t => g t * sawS N (y * t)) volume 0 1 :=
        Continuous.intervalIntegrable (hg.mul ((continuous_sawS N).comp (by fun_prop))) _ _
      refine (h1.sub h2).congr fun t _ => ?_
      simp only [sawE]; ring
    refine (abs_integral_mul_le hg2 (intervalIntegrable_sawE_comp_sq N y) hgk (hε N)).trans ?_
    have hB := integral_sawE_comp_sq_le N hy
    have hs : E N ≤ √(E N) * ε N := by
      calc E N = √(E N) * √(E N) := (Real.mul_self_sqrt (hE0 N)).symm
        _ ≤ √(E N) * ε N := by
          gcongr; simp only [ε]; linarith [show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity]
    have key : (ε N)⁻¹ * ∫ t in (0 : ℝ)..1, sawE N (y * t) ^ 2 ≤ K * √(E N) :=
      calc (ε N)⁻¹ * ∫ t in (0 : ℝ)..1, sawE N (y * t) ^ 2 ≤ (ε N)⁻¹ * (K * E N) :=
            mul_le_mul_of_nonneg_left hB (inv_pos.2 (hε N)).le
        _ ≤ (ε N)⁻¹ * (K * (√(E N) * ε N)) := by gcongr
        _ = K * √(E N) := by field_simp [(hε N).ne']
    linarith
  have hEt : Tendsto E atTop (𝓝 0) := tendsto_integral_sawE_sq
  have hsq : Tendsto (fun N => √(E N)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hEt
    rw [Real.sqrt_zero] at this; exact this
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have := hsq.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at this; exact this
  have hβ : Tendsto (fun N => (ε N * A) / 2 + (K * √(E N)) / 2) atTop (𝓝 0) := by
    simpa using ((hεt.mul_const A).div_const 2).add ((hsq.const_mul K).div_const 2)
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun N => dist_nonneg) hbound hβ)

end Modes

/-! ### The `C¹` Plancherel bound for `T` -/

section TBound

/-- The constant `ζ(3/2) = Σ_{n ≥ 1} n^{−3/2}` as a real series (the `n = 0` term is `0`). -/
def zeta32 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)

theorem summable_zeta32 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
  Real.summable_one_div_nat_rpow.2 (by norm_num)

theorem rpow_three_halves_sq (n : ℕ) : ((n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num

variable {g : ℝ → ℝ} (hg : Continuous g)
include hg

end TBound

/-! ### The antiderivative `Ψ`: cosine series and Plancherel bound -/

section Psi

variable {h : ℝ → ℝ} (hm : Measurable h) (hi : IntegrableOn (fun t => h t ^ 2) (Ioc 0 1))
include hm hi

omit hm hi

end Psi

end Cvs.Route.Visibility.SawtoothPlancherelBounds
