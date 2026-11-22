import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The pair form is a divided difference: the CvS matrix at any scale

Off the diagonal the cut kernel is `(σₘ − σₙ)/(π(n − m))` and every channel is linear, so
`pairQ m n / 2 = (b m − b n)/(ω m − ω n)`: the window Weil form on a mode sum is `L` times the
quadratic form of `Cvs.Finite.DividedDifferenceCommutator.ddMatrix` in `Cvs.Finite.TruncationZeroFreeOffAxes`'s frequency convention, with `‖modeSum xi‖² = L·xi⬝xi`.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.PairFormDividedDifference

/-! ### The cut sine and the off-diagonal kernel -/

/-- The sine at an integer mode, cut at the window's length. -/
def sigma (L : ℝ) (k : ℤ) (v : ℝ) : ℝ := if v ≤ L then Real.sin (2 * π * k * v / L) else 0

theorem sigma_neg (L : ℝ) (k : ℤ) (v : ℝ) : sigma L (-k) v = -sigma L k v := by
  unfold sigma
  split_ifs
  · push_cast
    rw [show 2 * π * -(k : ℝ) * v / L = -(2 * π * k * v / L) by ring, Real.sin_neg]
  · simp

theorem sigma_zero (L : ℝ) (hL : 0 ≤ L) (k : ℤ) : sigma L k 0 = 0 := by
  simp [sigma, hL]

theorem measurable_sigma (L : ℝ) (k : ℤ) : Measurable (sigma L k) :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

theorem abs_sigma_le_one (L : ℝ) (k : ℤ) (v : ℝ) : |sigma L k v| ≤ 1 := by
  unfold sigma; split_ifs
  · exact Real.abs_sin_le_one _
  · simp

/-- The cut sine is Lipschitz at the origin. -/
theorem abs_sigma_le {L : ℝ} (hL : 0 < L) (k : ℤ) (v : ℝ) :
    |sigma L k v| ≤ 2 * π * |(k : ℝ)| / L * |v| := by
  unfold sigma; split_ifs
  · calc |Real.sin (2 * π * k * v / L)| ≤ |2 * π * k * v / L| := Real.abs_sin_le_abs
      _ = 2 * π * |(k : ℝ)| / L * |v| := by
          rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hL, abs_of_pos Real.pi_pos,
            abs_of_pos (by norm_num : (0:ℝ) < 2)]
          ring
  · simp only [abs_zero]; positivity

/-- **Off the diagonal, the cut kernel is a difference of cut sines.** -/
theorem Kc_off_eq {L : ℝ} {m n : ℤ} (hmn : m ≠ n) (v : ℝ) :
    Cvs.Finite.LevyKernelIncrement.Kc L m n v
      = 1 / (π * ((n : ℝ) - m)) * (sigma L m v - sigma L n v) := by
  unfold Cvs.Finite.LevyKernelIncrement.Kc sigma Cvs.Finite.CosineModeOverlap.K
  split_ifs
  · ring
  · simp

/-! ### The pairing functional -/

/-- **The pairing functional** of a kernel function: the four channels of the window Weil form. -/
def Pair (P R : ℕ) (h : ℝ → ℝ) : ℝ :=
  2 * (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * h x)
    + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * h 0
    + (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (h 0 - h (u / 2)))
    - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 * h (r * Real.log p))

/-- The pair value is the pairing of the cut kernel. -/
theorem pairQ_eq_Pair {L : ℝ} (hL : 0 < L) (P R : ℕ) (m n : ℤ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L m n = Pair P R (Cvs.Finite.LevyKernelIncrement.Kc L m n) := by
  unfold Cvs.Finite.ModeSumPairValues.pairQ Pair Cvs.Finite.ModeSumPairValues.polePair
    Cvs.Finite.LevyChannelDoubleSum.levyPair Cvs.Finite.ModeSumPairValues.primePair
  rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le hL.le]

/-! ### Integrability of the sine channels -/

theorem integrableOn_exp_mul_sigma {L : ℝ} (hL : 0 < L) (k : ℤ) (c : ℝ) :
    IntegrableOn (fun x => Real.exp (c * x) * sigma L k x) (Ioi 0) (volume : Measure ℝ) := by
  have hmeas : Measurable (fun x => Real.exp (c * x) * sigma L k x) :=
    (by fun_prop : Measurable fun x : ℝ => Real.exp (c * x)).mul (measurable_sigma L k)
  have hsplit : Ioi (0:ℝ) = Ioc 0 L ∪ Ioi L := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ L
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · refine (integrableOn_const (C := Real.exp (|c| * L))
      (hs := measure_Ioc_lt_top.ne)).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
    obtain ⟨hu0, huL⟩ := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (c * u) ≤ Real.exp (|c| * L) := by
      apply Real.exp_le_exp.mpr
      calc c * u ≤ |c * u| := le_abs_self _
        _ = |c| * |u| := abs_mul _ _
        _ = |c| * u := by rw [abs_of_pos hu0]
        _ ≤ |c| * L := by gcongr
    calc Real.exp (c * u) * |sigma L k u| ≤ Real.exp (|c| * L) * 1 :=
          mul_le_mul h1 (abs_sigma_le_one L k u) (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|c| * L) := mul_one _
  · refine (integrableOn_zero (s := Ioi L)).congr_fun ?_ measurableSet_Ioi
    intro u hu
    show (0:ℝ) = Real.exp (c * u) * sigma L k u
    have : ¬ u ≤ L := not_le.mpr hu
    simp [sigma, this]

theorem integrableOn_densityU_mul_sigma {L : ℝ} (hL : 0 < L) (k : ℤ) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (sigma L k 0 - sigma L k (u / 2)))
      (Ioi 0) (volume : Measure ℝ) := by
  have hmeas : Measurable (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (sigma L k 0 - sigma L k (u / 2))) :=
    Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
      (measurable_const.sub ((measurable_sigma L k).comp (measurable_id.div_const 2)))
  have hsplit : Ioi (0:ℝ) = Ioc 0 (2 * L) ∪ Ioi (2 * L) := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ 2 * L
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · refine (integrableOn_const (C := (1 + 2 * L) * (2 * π * |(k : ℝ)| / L / 2))
      (hs := measure_Ioc_lt_top.ne)).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
    obtain ⟨hu0, huL⟩ := hu
    have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hdpos, sigma_zero L hL.le, zero_sub, abs_neg]
    -- `densityU u · u ≤ 1 + u` from the exact bound of `Cvs.WeilForm.Archimedean.LevyMeasure`
    have hdu : Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u ≤ 1 + u := by
      have h := Cvs.WeilForm.Archimedean.LevyMeasure.densityU_le hu0
      have he : Real.exp (-(u / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u ≤ (1 + u) * Real.exp (-(u / 4)) / u * u := by gcongr
        _ = (1 + u) * Real.exp (-(u / 4)) := by field_simp
        _ ≤ (1 + u) * 1 := by gcongr
        _ = 1 + u := mul_one _
    have hs := abs_sigma_le hL k (u / 2)
    rw [abs_of_pos (by linarith : (0:ℝ) < u / 2)] at hs
    calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * |sigma L k (u / 2)|
        ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (2 * π * |(k : ℝ)| / L * (u / 2)) := by gcongr
      _ = (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u) * (2 * π * |(k : ℝ)| / L / 2) := by ring
      _ ≤ (1 + u) * (2 * π * |(k : ℝ)| / L / 2) := by gcongr
      _ ≤ (1 + 2 * L) * (2 * π * |(k : ℝ)| / L / 2) := by gcongr
  · refine (integrableOn_zero (s := Ioi (2 * L))).congr_fun ?_ measurableSet_Ioi
    intro u hu
    show (0:ℝ) = Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (sigma L k 0 - sigma L k (u / 2))
    have h1 : ¬ u / 2 ≤ L := not_le.mpr (by simp only [mem_Ioi] at hu; linarith)
    rw [sigma_zero L hL.le]
    simp [sigma, h1]

/-! ### The divided difference -/

/-- **The pairing of the off-diagonal kernel is a difference of sine pairings.** -/
theorem Pair_Kc_off {L : ℝ} (hL : 0 < L) (P R : ℕ) {m n : ℤ} (hmn : m ≠ n) :
    Pair P R (Cvs.Finite.LevyKernelIncrement.Kc L m n)
      = 1 / (π * ((n : ℝ) - m)) * (Pair P R (sigma L m) - Pair P R (sigma L n)) := by
  have hfun : Cvs.Finite.LevyKernelIncrement.Kc L m n
      = fun v => 1 / (π * ((n : ℝ) - m)) * (sigma L m v - sigma L n v) := funext (Kc_off_eq hmn)
  rw [hfun]
  unfold Pair
  -- each channel is linear
  have hpole : (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2))
        * (1 / (π * ((n : ℝ) - m)) * (sigma L m x - sigma L n x)))
      = 1 / (π * ((n : ℝ) - m)) * ((∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2))
          * sigma L m x) - ∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2))
          * sigma L n x) := by
    have hi : ∀ k : ℤ, IntegrableOn (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2))
        * sigma L k x) (Ioi 0) volume := by
      intro k
      refine ((integrableOn_exp_mul_sigma hL k (-(1/2))).add
        (integrableOn_exp_mul_sigma hL k (1/2))).congr_fun ?_ measurableSet_Ioi
      intro x _
      simp only [Pi.add_apply]
      rw [show -(x / 2) = -(1 / 2) * x by ring, show x / 2 = 1 / 2 * x by ring]
      ring
    rw [← integral_sub (hi m) (hi n), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have hlevy : (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (1 / (π * ((n : ℝ) - m)) * (sigma L m 0 - sigma L n 0)
          - 1 / (π * ((n : ℝ) - m)) * (sigma L m (u / 2) - sigma L n (u / 2))))
      = 1 / (π * ((n : ℝ) - m)) * ((∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (sigma L m 0 - sigma L m (u / 2))) - ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (sigma L n 0 - sigma L n (u / 2))) := by
    rw [← integral_sub (integrableOn_densityU_mul_sigma hL m)
      (integrableOn_densityU_mul_sigma hL n), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have hprime : (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 * (1 / (π * ((n : ℝ) - m))
          * (sigma L m (r * Real.log p) - sigma L n (r * Real.log p)))))
      = 1 / (π * ((n : ℝ) - m)) * ((∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
          ∑ r ∈ Finset.Icc 1 R, primePowerWeight p r * (2 * sigma L m (r * Real.log p)))
        - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          primePowerWeight p r * (2 * sigma L n (r * Real.log p))) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hpole, hlevy, hprime]
  ring

/-! ### The CvS matrix in the frequency convention -/

/-- The diagonal of the CvS matrix: half the pair value on the diagonal. -/
def aval (P R : ℕ) (L : ℝ) (k : ℤ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L k k / 2

/-- The `ψ`-values of the CvS matrix: minus the sine pairing, scaled to the frequency. -/
def bval (P R : ℕ) (L : ℝ) (k : ℤ) : ℝ := -(Pair P R (sigma L k)) / L

/-- The pairing is odd under negation of its argument. -/
theorem Pair_neg (P R : ℕ) (h : ℝ → ℝ) :
    Pair P R (fun v => -h v) = -Pair P R h := by
  unfold Pair
  beta_reduce
  have e1 : (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * -h x)
      = -∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * h x := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (-h 0 - -h (u / 2)))
      = -∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (h 0 - h (u / 2)) := by
    rw [← integral_neg]; congr 1; funext u; ring
  have e3 : (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 * -h (r * Real.log p)))
      = -∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 * h (r * Real.log p)) := by
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [e1, e2, e3]
  ring

theorem bval_neg (P R : ℕ) (L : ℝ) (k : ℤ) : bval P R L (-k) = -bval P R L k := by
  unfold bval
  have : sigma L (-k) = fun v => -sigma L k v := funext (sigma_neg L k)
  rw [this, Pair_neg]
  ring

/-- **Half the off-diagonal pair value is the divided difference of `bval` in frequency.** -/
theorem pairQ_off {L : ℝ} (hL : 0 < L) (P R : ℕ) {m n : ℤ} (hmn : m ≠ n) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L m n / 2
      = (bval P R L m - bval P R L n) / (2 * π * m / L - 2 * π * n / L) := by
  rw [pairQ_eq_Pair hL, Pair_Kc_off hL P R hmn]
  unfold bval
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hL0 : L ≠ 0 := hL.ne'
  have hnm : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  have hmn' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hden : 2 * π * m / L - 2 * π * n / L = 2 * π * ((m : ℝ) - n) / L := by ring
  rw [hden]
  field_simp
  ring

/-- **The CvS matrix entry is half the pair value**, for an injective mode map. -/
theorem ddMatrix_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) (i j : ι) :
    Cvs.Finite.DividedDifferenceCommutator.ddMatrix (fun k => aval P R L (mode k)) (fun k => bval P R L (mode k))
        (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) i j
      = Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (mode j) / 2 := by
  by_cases hij : i = j
  · subst hij
    rw [Cvs.Finite.DividedDifferenceCommutator.ddMatrix_diag]; rfl
  · rw [Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off hij]
    have hmn : mode i ≠ mode j := fun h => hij (hinj h)
    rw [pairQ_off hL P R hmn]
    rfl

/-- **The window Weil form on a mode sum is `L` times the CvS quadratic form.** -/
theorem weilForm_modeSum_eq_ddMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)
      = L * (xi ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix (fun k => aval P R L (mode k))
          (fun k => bval P R L (mode k)) (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ xi)) := by
  rw [Cvs.Finite.ModeSumPairValues.weilForm_modeSum hL P R mode hinv hmode hxieven]
  simp only [Matrix.mulVec, dotProduct, ddMatrix_eq hL P R hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The squared norm of a mode sum is `L` times the coefficient norm**, for injective modes. -/
theorem selfConvolution_modeSum_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) 0 = L * (xi ⬝ᵥ xi) := by
  rw [Cvs.Finite.CosineModeOverlap.selfConvolution_modeSum hL mode hinv hmode hxieven (le_refl 0) hL.le]
  have hK : ∀ i j : ι, Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0 = if i = j then 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [Cvs.Finite.CosineModeOverlap.K]
    · have hmn : mode i ≠ mode j := fun h => hij (hinj h)
      simp [Cvs.Finite.CosineModeOverlap.K, hmn, hij]
  simp only [hK, mul_ite, mul_zero, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end Cvs.Finite.PairFormDividedDifference
