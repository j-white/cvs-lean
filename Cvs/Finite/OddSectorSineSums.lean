import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumDeficit
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.WeilPositivityStatement

/-!
# The odd sector of the CvS matrix: sine sums carry the same kernel

Odd coefficient vectors define window sine sums, odd about the midpoint, whose self-convolution
is the same kernel double sum as the cosine sums', so the `_of_rep` identities of `Cvs.Finite.LevyChannelDoubleSum`/`Cvs.Finite.ModeSumPairValues`
give their Weil form and norm through the same matrix.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.OddSectorSineSums

variable {ι : Type*} [Fintype ι]

/-- The window sine sum. -/
def sineSum (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : ℝ → ℝ :=
  fun y => if y ∈ Ioc (0:ℝ) L then ∑ i, o i * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)
    else 0

theorem sineSum_eq_indicator (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) :
    sineSum L mode o = Set.indicator (Ioc (0:ℝ) L)
      (fun y => ∑ i, o i * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)) := by
  funext y; simp only [sineSum, Set.indicator_apply]

theorem measurable_sineSum (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : Measurable (sineSum L mode o) := by
  rw [sineSum_eq_indicator]
  exact (Finset.measurable_sum _ fun i _ => by fun_prop).indicator measurableSet_Ioc

theorem abs_sineSum_le (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (y : ℝ) :
    |sineSum L mode o y| ≤ ∑ i, |o i| := by
  simp only [sineSum]
  split_ifs
  · calc |∑ i, o i * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)|
        ≤ ∑ i, |o i * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |o i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · rw [abs_zero]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

theorem sineSum_eq_zero_of_notMem (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) {y : ℝ}
    (hy : y ∉ Ioc (0:ℝ) L) : sineSum L mode o y = 0 := by
  simp only [sineSum, ite_eq_right hy]

/-- **The sine sum is odd about the window's midpoint.** -/
theorem sineSum_reflect (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) L) :
    sineSum L mode o (L - y) = -sineSum L mode o y := by
  have h1 : L - y ∈ Ioc (0:ℝ) L := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h2 : y ∈ Ioc (0:ℝ) L := ⟨hy.1, hy.2.le⟩
  simp only [sineSum, ite_eq_left h1, ite_eq_left h2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : L ≠ 0 := by linarith [hy.1, hy.2]
  have : Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * (L - y)
      = 2 * π * (mode i) * (L / L) - Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]; ring
  rw [this, div_self hL, mul_one, Cvs.Finite.CosineModeOverlap.sin_two_pi_int_sub]
  ring

/-! ### The overlap of two sine modes -/

theorem sin_mul_sin' (a b : ℝ) :
    Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- **The overlap in the generic case** `m ≠ ±n`. -/
theorem sin_overlap_generic {L : ℝ} (hL : 0 < L) {m n : ℤ} (hmn : m ≠ n) (hmn' : m ≠ -n) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.sin (2 * π * m / L * s) * Real.sin (2 * π * n / L * (s + v))
      = L / 4 * (Cvs.Finite.CosineModeOverlap.K L m n v - Cvs.Finite.CosineModeOverlap.K L m (-n) v) := by
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
  have hint : (fun s => Real.sin (ωm * s) * Real.sin (ωn * (s + v)))
      = fun s => (Real.cos ((ωm - ωn) * s + (-(ωn * v))) - Real.cos ((ωm + ωn) * s + ωn * v)) / 2 := by
    funext s; rw [sin_mul_sin', show ωm * s - ωn * (s + v) = (ωm - ωn) * s + (-(ωn * v)) by ring,
      show ωm * s + ωn * (s + v) = (ωm + ωn) * s + ωn * v by ring]
  have hc1 : Continuous fun s : ℝ => Real.cos ((ωm - ωn) * s + (-(ωn * v))) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  have hc2 : Continuous fun s : ℝ => Real.cos ((ωm + ωn) * s + ωn * v) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  rw [hint, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    Cvs.Finite.CosineModeOverlap.integral_cos_affine _ _ _ hdiff,
    Cvs.Finite.CosineModeOverlap.integral_cos_affine _ _ _ hsum]
  have h1 : (ωm - ωn) * (L - v) + -(ωn * v) = 2 * π * (m - n) - ωm * v := by
    rw [hωm, hωn]; field_simp; ring
  have h2 : (ωm + ωn) * (L - v) + ωn * v = 2 * π * (m + n) - ωm * v := by
    rw [hωm, hωn]; field_simp; ring
  rw [h1, h2]
  have e1 : Real.sin (2 * π * (m - n) - ωm * v) = -Real.sin (ωm * v) := by
    have := Cvs.Finite.CosineModeOverlap.sin_two_pi_int_sub (m - n) (ωm * v); push_cast at this; exact this
  have e2 : Real.sin (2 * π * (m + n) - ωm * v) = -Real.sin (ωm * v) := by
    have := Cvs.Finite.CosineModeOverlap.sin_two_pi_int_sub (m + n) (ωm * v); push_cast at this; exact this
  rw [e1, e2]
  simp only [Real.sin_neg]
  have harg : ∀ k : ℤ, 2 * π * (k : ℝ) * v / L = 2 * π * k / L * v := fun k => by ring
  have hK1 : Cvs.Finite.CosineModeOverlap.K L m n v
      = (Real.sin (ωm * v) - Real.sin (ωn * v)) / (L / 2 * (ωn - ωm)) := by
    simp only [Cvs.Finite.CosineModeOverlap.K, ite_eq_right hmn]
    rw [harg m, harg n, hωm, hωn]
    field_simp
  have hK2 : Cvs.Finite.CosineModeOverlap.K L m (-n) v
      = -((Real.sin (ωm * v) + Real.sin (ωn * v)) / (L / 2 * (ωn + ωm))) := by
    have hmn'' : m ≠ -n := hmn'
    simp only [Cvs.Finite.CosineModeOverlap.K, ite_eq_right hmn'']
    push_cast
    rw [show 2 * π * -(n : ℝ) * v / L = -(2 * π * n / L * v) by ring, Real.sin_neg, harg m,
      sub_neg_eq_add]
    have hden : L / 2 * (ωn + ωm) = π * ((n : ℝ) + m) := by rw [hωm, hωn]; field_simp
    have hden' : π * (-(n : ℝ) - m) = -(π * ((n : ℝ) + m)) := by ring
    rw [hden, hden', div_neg]
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

/-- **The overlap of a sine mode with itself, or with its mirror.** -/
theorem sin_overlap_diag {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ≠ 0) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.sin (2 * π * m / L * s) * Real.sin (2 * π * m / L * (s + v))
      = L / 4 * (Cvs.Finite.CosineModeOverlap.K L m m v - Cvs.Finite.CosineModeOverlap.K L m (-m) v) := by
  set ω : ℝ := 2 * π * m / L with hω
  have hπ : 0 < π := Real.pi_pos
  have hm_r : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hω0 : ω ≠ 0 := by rw [hω]; positivity
  have h2ω : 2 * ω ≠ 0 := by positivity
  have hint : (fun s => Real.sin (ω * s) * Real.sin (ω * (s + v)))
      = fun s => (Real.cos (0 * s + (-(ω * v))) - Real.cos (2 * ω * s + ω * v)) / 2 := by
    funext s; rw [sin_mul_sin', show ω * s - ω * (s + v) = 0 * s + (-(ω * v)) by ring,
      show ω * s + ω * (s + v) = 2 * ω * s + ω * v by ring]
  have hc1 : Continuous fun s : ℝ => Real.cos (0 * s + (-(ω * v))) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  have hc2 : Continuous fun s : ℝ => Real.cos (2 * ω * s + ω * v) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  rw [hint, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    Cvs.Finite.CosineModeOverlap.integral_cos_const, Cvs.Finite.CosineModeOverlap.integral_cos_affine _ _ _ h2ω,
    Real.cos_neg]
  have h2 : 2 * ω * (L - v) + ω * v = 2 * π * (2 * m) - ω * v := by
    rw [hω]; field_simp; ring
  rw [h2]
  have e2 : Real.sin (2 * π * (2 * m) - ω * v) = -Real.sin (ω * v) := by
    have := Cvs.Finite.CosineModeOverlap.sin_two_pi_int_sub (2 * m) (ω * v); push_cast at this; exact this
  rw [e2]
  have hmm : m ≠ -m := by omega
  have harg : 2 * π * (m : ℝ) * v / L = ω * v := by rw [hω]; ring
  have hK1 : Cvs.Finite.CosineModeOverlap.K L m m v = 2 * (1 - v / L) * Real.cos (ω * v) := by
    simp only [Cvs.Finite.CosineModeOverlap.K, ite_true]; rw [harg]
  have hK2 : Cvs.Finite.CosineModeOverlap.K L m (-m) v = -(Real.sin (ω * v) / (π * m)) := by
    simp only [Cvs.Finite.CosineModeOverlap.K, ite_eq_right hmm]
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

theorem sin_overlap_zero (L v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.sin (2 * π * (0:ℤ) / L * s) * Real.sin (2 * π * (0:ℤ) / L * (s + v))
      = L / 4 * (Cvs.Finite.CosineModeOverlap.K L 0 0 v - Cvs.Finite.CosineModeOverlap.K L 0 (-0) v) := by
  simp

/-- The kernel is invariant under negating both modes. -/
theorem K_neg_neg (L : ℝ) (m n : ℤ) (v : ℝ) :
    Cvs.Finite.CosineModeOverlap.K L (-m) (-n) v = Cvs.Finite.CosineModeOverlap.K L m n v := by
  unfold Cvs.Finite.CosineModeOverlap.K
  by_cases hmn : m = n
  · subst hmn; simp only [ite_true]
    push_cast
    rw [show 2 * π * -(m : ℝ) * v / L = -(2 * π * m * v / L) by ring, Real.cos_neg]
  · have h' : -m ≠ -n := fun h => hmn (neg_inj.mp h)
    simp only [ite_eq_right hmn, ite_eq_right h']
    push_cast
    rw [show 2 * π * -(m : ℝ) * v / L = -(2 * π * m * v / L) by ring,
      show 2 * π * -(n : ℝ) * v / L = -(2 * π * n * v / L) by ring, Real.sin_neg, Real.sin_neg,
      show π * (-(n : ℝ) - -(m : ℝ)) = -(π * ((n : ℝ) - m)) by ring, div_neg]
    ring

/-- **The overlap of two window sine modes, in closed form.** -/
theorem sin_overlap_eq {L : ℝ} (hL : 0 < L) (m n : ℤ) (v : ℝ) :
    ∫ s in (0:ℝ)..(L - v), Real.sin (2 * π * m / L * s) * Real.sin (2 * π * n / L * (s + v))
      = L / 4 * (Cvs.Finite.CosineModeOverlap.K L m n v - Cvs.Finite.CosineModeOverlap.K L m (-n) v) := by
  by_cases hmn : m = n
  · subst hmn
    by_cases hm : m = 0
    · subst hm; exact sin_overlap_zero L v
    · exact sin_overlap_diag hL hm v
  · by_cases hmn' : m = -n
    · subst hmn'
      have hn : n ≠ 0 := by intro h; subst h; exact hmn (by simp)
      have := sin_overlap_diag hL hn v
      -- the mirror's integrand is minus the diagonal one, since sine is odd
      have hint : (fun s => Real.sin (2 * π * (-n : ℤ) / L * s) * Real.sin (2 * π * n / L * (s + v)))
          = fun s => -(Real.sin (2 * π * n / L * s) * Real.sin (2 * π * n / L * (s + v))) := by
        funext s; push_cast
        rw [show 2 * π * -(n:ℝ) / L * s = -(2 * π * n / L * s) by ring, Real.sin_neg]
        ring
      rw [hint, intervalIntegral.integral_neg, this, K_neg_neg]
      have hK : Cvs.Finite.CosineModeOverlap.K L (-n) n v = Cvs.Finite.CosineModeOverlap.K L n (-n) v := by
        have := K_neg_neg L n (-n) v
        rw [neg_neg] at this
        exact this
      rw [hK]
      ring
    · exact sin_overlap_generic hL hmn hmn' v

/-! ### The self-convolution of a sine sum -/

/-- **The self-convolution of an odd sine sum is the kernel double sum.** -/
theorem selfConvolution_sineSum [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i)
    {v : ℝ} (hv0 : 0 ≤ v) (hvL : v ≤ L) :
    selfConvolution (sineSum L mode o) v
      = L / 2 * ∑ i, ∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v := by
  rw [sineSum_eq_indicator, Cvs.Finite.ModeSumDeficit.selfConvolution_indicator_eq hv0 hvL]
  have hexp : (fun s => (∑ i, o i * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * s))
      * ∑ j, o j * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j * (s + v)))
      = fun s => ∑ i, ∑ j, o i * o j
          * (Real.sin (2 * π * (mode i) / L * s) * Real.sin (2 * π * (mode j) / L * (s + v))) := by
    funext s
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]; ring
  have hmirror : ∀ i, ∑ j, o i * o j * (L / 4 * (Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v
        - Cvs.Finite.CosineModeOverlap.K L (mode i) (-mode j) v))
      = L / 2 * ∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v := by
    intro i
    have h1 : ∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (-mode j) v
        = -∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v := by
      have := Equiv.sum_comp (Function.Involutive.toPerm neg hinv)
        (fun j => o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v)
      rw [← this, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Function.Involutive.coe_toPerm, hmode, hodd]
      ring
    calc ∑ j, o i * o j * (L / 4 * (Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v
            - Cvs.Finite.CosineModeOverlap.K L (mode i) (-mode j) v))
        = L / 4 * ((∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v)
            - ∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (-mode j) v) := by
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = L / 2 * ∑ j, o i * o j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) v := by
          rw [h1]; ring
  have hcont : ∀ i j, Continuous fun s : ℝ => o i * o j
      * (Real.sin (2 * π * (mode i) / L * s) * Real.sin (2 * π * (mode j) / L * (s + v))) :=
    fun i j => by fun_prop
  rw [hexp, intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ fun j _ => hcont i j).intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, sin_overlap_eq hL]
  exact hmirror i

/-- The sine sum's self-convolution vanishes at lags of the window's length or more. -/
theorem selfConvolution_sineSum_eq_zero {L : ℝ} (mode : ι → ℤ) (o : ι → ℝ) {v : ℝ} (hv : L ≤ v) :
    selfConvolution (sineSum L mode o) v = 0 := by
  unfold selfConvolution
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [sineSum]
  by_cases hs : s ∈ Ioc (0:ℝ) L
  · have : s + v ∉ Ioc (0:ℝ) L := fun h => by linarith [hs.1, h.2]
    simp [this]
  · simp [hs]

/-- The self-convolution on the half-line, through the cut kernel. -/
theorem selfConvolution_sineSum_Kc [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i)
    {v : ℝ} (hv0 : 0 ≤ v) :
    selfConvolution (sineSum L mode o) v
      = L / 2 * ∑ i, ∑ j, o i * o j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v := by
  by_cases hv : v ≤ L
  · rw [selfConvolution_sineSum hL mode hinv hmode hodd hv0 hv]
    simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_le hv]
  · rw [selfConvolution_sineSum_eq_zero mode o (not_le.mp hv).le]
    simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_gt (not_le.mp hv), mul_zero, Finset.sum_const_zero]

/-! ### The Weil form and the norm of a sine sum -/

/-- **The window Weil form on an odd sine sum is `L` times the CvS quadratic form.** -/
theorem weilForm_sineSum_eq_ddMatrix [DecidableEq ι] {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (sineSum L mode o)
      = L * (o ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode k))
          (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode k))
          (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ o)) := by
  rw [Cvs.Finite.ModeSumPairValues.weilForm_of_rep hL P R (measurable_sineSum L mode o)
    (abs_sineSum_le L mode o) (fun _ hs => sineSum_eq_zero_of_notMem L mode o hs)
    (fun _ hv => selfConvolution_sineSum_Kc hL mode hinv hmode hodd hv)]
  simp only [Matrix.mulVec, dotProduct, Cvs.Finite.PairFormDividedDifference.ddMatrix_eq hL P R hinj,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The kernel double sum at lag zero is twice the coefficient norm, for injective modes. -/
theorem double_sum_K_zero [DecidableEq ι] {L : ℝ} {mode : ι → ℤ} (hinj : Function.Injective mode)
    (c : ι → ℝ) :
    L / 2 * ∑ i, ∑ j, c i * c j * Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0 = L * (c ⬝ᵥ c) := by
  have hK : ∀ i j : ι, Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0 = if i = j then 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [Cvs.Finite.CosineModeOverlap.K]
    · have hmn : mode i ≠ mode j := fun h => hij (hinj h)
      simp [Cvs.Finite.CosineModeOverlap.K, hmn, hij]
  simp only [hK, mul_ite, mul_zero, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **The squared norm of an odd sine sum is `L` times the coefficient norm.** -/
theorem selfConvolution_sineSum_zero [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) :
    selfConvolution (sineSum L mode o) 0 = L * (o ⬝ᵥ o) := by
  rw [selfConvolution_sineSum hL mode hinv hmode hodd (le_refl 0) hL.le, double_sum_K_zero hinj]

end Cvs.Finite.OddSectorSineSums
