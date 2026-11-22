import Mathlib
import Cvs.Finite.ModeSumDeficit
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Zeta.WeilPositivityStatement

/-!
# The overlap of two window cosine modes at a lag, in closed form

`∫₀^{L−v} cos(ω_i s)·cos(ω_j (s+v)) ds` for `ω = 2πm/L`, expressed through the divided-difference
kernel `K L m n v` of the Connes–van Suijlekom matrix.
-/

noncomputable section

open Real intervalIntegral Cvs.Zeta.Explicit.Weil MeasureTheory

namespace Cvs.Finite.CosineModeOverlap

/-- The divided-difference kernel: `2(1 − v/L)cos(2πmv/L)` on the diagonal, and
`(sin(2πmv/L) − sin(2πnv/L))/(π(n − m))` off it. -/
def K (L : ℝ) (m n : ℤ) (v : ℝ) : ℝ :=
  if m = n then 2 * (1 - v / L) * Real.cos (2 * π * m * v / L)
  else (Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)) / (π * ((n : ℝ) - m))

/-- **The integral of a cosine of an affine argument.** -/
theorem integral_cos_affine (c d b : ℝ) (hc : c ≠ 0) :
    ∫ s in (0:ℝ)..b, Real.cos (c * s + d) = (Real.sin (c * b + d) - Real.sin d) / c := by
  rw [intervalIntegral.integral_comp_mul_add (fun x => Real.cos x) hc d, integral_cos]
  simp [mul_zero, zero_add]
  ring

/-- **The integral of a constant cosine.** -/
theorem integral_cos_const (d b : ℝ) : ∫ s in (0:ℝ)..b, Real.cos (0 * s + d) = b * Real.cos d := by
  simp

/-- The product of cosines as a sum. -/
theorem cos_mul_cos' (a b : ℝ) : Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- `sin(2πk − x) = −sin x` for an integer `k`. -/
theorem sin_two_pi_int_sub (k : ℤ) (x : ℝ) : Real.sin (2 * π * k - x) = -Real.sin x := by
  have : 2 * π * k - x = -x + k * (2 * π) := by ring
  rw [this, Real.sin_add_int_mul_two_pi, Real.sin_neg]

/-- **The overlap in the generic case** `m ≠ ±n`. -/
theorem overlap_generic {L : ℝ} (hL : 0 < L) {m n : ℤ} (hmn : m ≠ n) (hmn' : m ≠ -n) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.cos (2 * π * m / L * s) * Real.cos (2 * π * n / L * (s + v))
      = L / 4 * (K L m n v + K L m (-n) v) := by
  set ωm : ℝ := 2 * π * m / L with hωm
  set ωn : ℝ := 2 * π * n / L with hωn
  have hπ : 0 < π := Real.pi_pos
  have hmn_r : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hmn_r' : (m : ℝ) + n ≠ 0 := by
    intro h; apply hmn'
    have : (m : ℝ) = -n := by linarith
    exact_mod_cast this
  have hdiff_eq : ωm - ωn = 2 * π / L * ((m : ℝ) - n) := by rw [hωm, hωn]; ring
  have hsum_eq : ωm + ωn = 2 * π / L * ((m : ℝ) + n) := by rw [hωm, hωn]; ring
  have hdiff : ωm - ωn ≠ 0 := by rw [hdiff_eq]; exact mul_ne_zero (by positivity) hmn_r
  have hsum : ωm + ωn ≠ 0 := by rw [hsum_eq]; exact mul_ne_zero (by positivity) hmn_r'
  have hint : (fun s => Real.cos (ωm * s) * Real.cos (ωn * (s + v)))
      = fun s => (Real.cos ((ωm - ωn) * s + (-(ωn * v))) + Real.cos ((ωm + ωn) * s + ωn * v)) / 2 := by
    funext s
    rw [cos_mul_cos', show ωm * s - ωn * (s + v) = (ωm - ωn) * s + (-(ωn * v)) by ring,
      show ωm * s + ωn * (s + v) = (ωm + ωn) * s + ωn * v by ring]
  rw [hint, intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun s : ℝ => Real.cos ((ωm - ωn) * s + (-(ωn * v)))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s : ℝ => Real.cos ((ωm + ωn) * s + ωn * v)).intervalIntegrable _ _),
    integral_cos_affine _ _ _ hdiff, integral_cos_affine _ _ _ hsum]
  have h1 : (ωm - ωn) * (L - v) + -(ωn * v) = 2 * π * (m - n) - ωm * v := by
    rw [hωm, hωn]; field_simp; ring
  have h2 : (ωm + ωn) * (L - v) + ωn * v = 2 * π * (m + n) - ωm * v := by
    rw [hωm, hωn]; field_simp; ring
  rw [h1, h2]
  have e1 : Real.sin (2 * π * (m - n) - ωm * v) = -Real.sin (ωm * v) := by
    have := sin_two_pi_int_sub (m - n) (ωm * v); push_cast at this; exact this
  have e2 : Real.sin (2 * π * (m + n) - ωm * v) = -Real.sin (ωm * v) := by
    have := sin_two_pi_int_sub (m + n) (ωm * v); push_cast at this; exact this
  rw [e1, e2]
  simp only [Real.sin_neg]
  -- the kernel, in the frequency variables
  have harg : ∀ k : ℤ, 2 * π * (k : ℝ) * v / L = 2 * π * k / L * v := fun k => by ring
  have hK1 : K L m n v = (Real.sin (ωm * v) - Real.sin (ωn * v)) / (L / 2 * (ωn - ωm)) := by
    simp only [K, ite_eq_right hmn]
    rw [harg m, harg n, hωm, hωn]
    field_simp
  have hK2 : K L m (-n) v = -((Real.sin (ωm * v) + Real.sin (ωn * v)) / (L / 2 * (ωn + ωm))) := by
    have hmn'' : m ≠ -n := hmn'
    simp only [K, ite_eq_right hmn'']
    push_cast
    rw [show 2 * π * -(n : ℝ) * v / L = -(2 * π * n / L * v) by ring, Real.sin_neg, harg m,
      sub_neg_eq_add]
    have hden : L / 2 * (ωn + ωm) = π * ((n : ℝ) + m) := by rw [hωm, hωn]; field_simp
    have hden' : π * (-(n : ℝ) - m) = -(π * ((n : ℝ) + m)) := by ring
    rw [hden]
    rw [hden']
    rw [div_neg]
  rw [hK1, hK2]
  have hLne : L ≠ 0 := hL.ne'
  have hd1 : L / 2 * (ωn - ωm) ≠ 0 := mul_ne_zero (by positivity) (by
    intro h; apply hdiff; linarith)
  have hd2 : L / 2 * (ωn + ωm) ≠ 0 := mul_ne_zero (by positivity) (by
    intro h; apply hsum; linarith)
  have hne1 : -ωm + ωn ≠ 0 := by intro h; apply hdiff; linarith
  have hne2 : ωn - ωm ≠ 0 := by intro h; apply hdiff; linarith
  have hne3 : ωn + ωm ≠ 0 := by intro h; apply hsum; linarith
  field_simp
  ring

/-- **The overlap of a mode with itself, or with its mirror.** -/
theorem overlap_diag {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ≠ 0) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.cos (2 * π * m / L * s) * Real.cos (2 * π * m / L * (s + v))
      = L / 4 * (K L m m v + K L m (-m) v) := by
  set ω : ℝ := 2 * π * m / L with hω
  have hπ : 0 < π := Real.pi_pos
  have hm_r : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hω0 : ω ≠ 0 := by rw [hω]; positivity
  have h2ω : 2 * ω ≠ 0 := by positivity
  have hint : (fun s => Real.cos (ω * s) * Real.cos (ω * (s + v)))
      = fun s => (Real.cos (0 * s + (-(ω * v))) + Real.cos (2 * ω * s + ω * v)) / 2 := by
    funext s
    rw [cos_mul_cos', show ω * s - ω * (s + v) = 0 * s + (-(ω * v)) by ring,
      show ω * s + ω * (s + v) = 2 * ω * s + ω * v by ring]
  rw [hint, intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun s : ℝ => Real.cos (0 * s + (-(ω * v)))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s : ℝ => Real.cos (2 * ω * s + ω * v)).intervalIntegrable _ _),
    integral_cos_const, integral_cos_affine _ _ _ h2ω, Real.cos_neg]
  have h2 : 2 * ω * (L - v) + ω * v = 2 * π * (2 * m) - ω * v := by
    rw [hω]; field_simp; ring
  rw [h2]
  have e2 : Real.sin (2 * π * (2 * m) - ω * v) = -Real.sin (ω * v) := by
    have := sin_two_pi_int_sub (2 * m) (ω * v); push_cast at this; exact this
  rw [e2]
  have hmm : m ≠ -m := by omega
  have harg : 2 * π * (m : ℝ) * v / L = ω * v := by rw [hω]; ring
  have hK1 : K L m m v = 2 * (1 - v / L) * Real.cos (ω * v) := by
    simp only [K, ite_true]; rw [harg]
  have hK2 : K L m (-m) v = -(Real.sin (ω * v) / (π * m)) := by
    simp only [K, ite_eq_right hmm]
    push_cast
    rw [show 2 * π * -(m : ℝ) * v / L = -(2 * π * m / L * v) by ring, Real.sin_neg, harg, hω,
      sub_neg_eq_add]
    have : π * (-(m : ℝ) - m) = -(2 * π * m) := by ring
    rw [this, div_neg]
    congr 1
    field_simp
    ring
  rw [hK1, hK2, hω]
  field_simp
  ring

theorem overlap_zero {L : ℝ} (hL : 0 < L) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.cos (2 * π * (0:ℤ) / L * s) * Real.cos (2 * π * (0:ℤ) / L * (s + v))
      = L / 4 * (K L 0 0 v + K L 0 (-0) v) := by
  simp only [K, Int.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, mul_one,
    neg_zero]
  simp
  field_simp
  ring

/-- **The overlap of two window cosine modes, in closed form.** -/
theorem overlap_eq {L : ℝ} (hL : 0 < L) (m n : ℤ) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.cos (2 * π * m / L * s) * Real.cos (2 * π * n / L * (s + v))
      = L / 4 * (K L m n v + K L m (-n) v) := by
  by_cases hmn : m = n
  · subst hmn
    by_cases hm : m = 0
    · subst hm; exact overlap_zero hL v
    · exact overlap_diag hL hm v
  · by_cases hmn' : m = -n
    · subst hmn'
      have hn : n ≠ 0 := by intro h; subst h; exact hmn (by simp)
      have := overlap_diag hL (neg_ne_zero.mpr hn) v
      -- the mirror's integrand is the same, since cosine is even
      have hint : (fun s => Real.cos (2 * π * (-n : ℤ) / L * s) * Real.cos (2 * π * n / L * (s + v)))
          = fun s => Real.cos (2 * π * (-n : ℤ) / L * s) * Real.cos (2 * π * (-n : ℤ) / L * (s + v)) := by
        funext s; push_cast
        rw [show 2 * π * -(n:ℝ) / L * (s + v) = -(2 * π * n / L * (s + v)) by ring, Real.cos_neg]
      rw [hint, this]
      simp only [neg_neg]
      ring
    · exact overlap_generic hL hmn hmn' v

/-- The two-sided cosine sum on the window is an indicator. -/
theorem modeSum_eq_indicator {ι : Type*} [Fintype ι] (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi
      = Set.indicator (Set.Ioc (0:ℝ) L)
          (fun y => ∑ i, xi i * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)) := by
  funext y
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Set.indicator_apply]

/-- **The self-convolution of a mode sum is the double sum over the kernel.** -/
theorem selfConvolution_modeSum {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    {v : ℝ} (hv0 : 0 ≤ v) (hvL : v ≤ L) :
    selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) v
      = L / 2 * ∑ i, ∑ j, xi i * xi j * K L (mode i) (mode j) v := by
  rw [modeSum_eq_indicator, Cvs.Finite.ModeSumDeficit.selfConvolution_indicator_eq hv0 hvL]
  -- expand the product of sums
  have hexp : (fun s => (∑ i, xi i * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * s))
      * ∑ j, xi j * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j * (s + v)))
      = fun s => ∑ i, ∑ j, xi i * xi j
          * (Real.cos (2 * π * (mode i) / L * s) * Real.cos (2 * π * (mode j) / L * (s + v))) := by
    funext s
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]; ring
  -- fold the mirrored half back by the involution
  have hmirror : ∀ i, ∑ j, xi i * xi j * (L / 4 * (K L (mode i) (mode j) v + K L (mode i) (-mode j) v))
      = L / 2 * ∑ j, xi i * xi j * K L (mode i) (mode j) v := by
    intro i
    have h1 : ∑ j, xi i * xi j * K L (mode i) (-mode j) v
        = ∑ j, xi i * xi j * K L (mode i) (mode j) v := by
      have := Equiv.sum_comp (Function.Involutive.toPerm neg hinv)
        (fun j => xi i * xi j * K L (mode i) (mode j) v)
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Function.Involutive.coe_toPerm, hmode, hxieven]
    calc ∑ j, xi i * xi j * (L / 4 * (K L (mode i) (mode j) v + K L (mode i) (-mode j) v))
        = L / 4 * ((∑ j, xi i * xi j * K L (mode i) (mode j) v)
            + ∑ j, xi i * xi j * K L (mode i) (-mode j) v) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = L / 2 * ∑ j, xi i * xi j * K L (mode i) (mode j) v := by rw [h1]; ring
  have hcont : ∀ i j, Continuous fun s : ℝ => xi i * xi j
      * (Real.cos (2 * π * (mode i) / L * s) * Real.cos (2 * π * (mode j) / L * (s + v))) :=
    fun i j => by fun_prop
  rw [hexp, intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ fun j _ => hcont i j).intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, overlap_eq hL]
  exact hmirror i

end Cvs.Finite.CosineModeOverlap
