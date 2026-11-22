import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.PoleTermLagFunctional
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormReflection
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window Weil form on a mode sum is a double sum over pair values

Each channel of `Cvs.WeilForm.SelfConvolutionFunctional.weilForm` is a linear functional of the self-convolution, which `Cvs.Finite.LevyChannelDoubleSum`
writes as a kernel double sum, so `weilForm P R (modeSum xi) = (L/2) ∑∑ xiᵢ xiⱼ pairQ (mᵢ, mⱼ)`:
Connes–van Suijlekom's quadratic form in real coordinates.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.ModeSumPairValues

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The mode sum is bounded and measurable -/

omit [DecidableEq ι] in
theorem measurable_modeSum (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    Measurable (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) := by
  rw [Cvs.Finite.CosineModeOverlap.modeSum_eq_indicator]
  exact (Finset.measurable_sum _ fun i _ => by fun_prop).indicator measurableSet_Ioc

omit [DecidableEq ι] in
theorem abs_modeSum_le (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (y : ℝ) :
    |Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi y| ≤ ∑ i, |xi i| := by
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum]
  split_ifs
  · calc |∑ i, xi i * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)|
        ≤ ∑ i, |xi i * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |xi i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · rw [abs_zero]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

omit [DecidableEq ι] in
theorem modeSum_eq_zero_of_notMem (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) {y : ℝ}
    (hy : y ∉ Ioc (0:ℝ) L) : Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi y = 0 := by
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, if_neg hy]

omit [DecidableEq ι] in
/-- The self-convolution on the whole line, through the cut kernel at the absolute lag. -/
theorem selfConvolution_abs_of_rep {L : ℝ} {mode : ι → ℤ} {c : ι → ℝ} {f : ℝ → ℝ}
    (hg : ∀ v, 0 ≤ v → selfConvolution f v
      = L / 2 * ∑ i, ∑ j, c i * c j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v) (x : ℝ) :
    selfConvolution f x
      = L / 2 * ∑ i, ∑ j, c i * c j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact hg x hx
  · rw [abs_of_neg hx, ← Cvs.WeilForm.WeilFormReflection.selfConvolution_neg]
    exact hg (-x) (by linarith)

theorem selfConvolution_modeSum_abs {L : ℝ} (hL : 0 < L)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (x : ℝ) :
    selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) x
      = L / 2 * ∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) |x| :=
  selfConvolution_abs_of_rep
    (fun _ hv => Cvs.Finite.LevyChannelDoubleSum.selfConvolution_modeSum_Kc hL mode hinv hmode hxieven hv) x

/-! ### The pole channel -/

/-- The pole pairing of the cut kernel: `∫₀^∞ 2cosh(x/2)·Kc(x) dx`. -/
def polePair (L : ℝ) (m n : ℤ) : ℝ :=
  ∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * Cvs.Finite.LevyKernelIncrement.Kc L m n x

theorem integrableOn_exp_mul_Kc {L : ℝ} (hL : 0 < L) (m n : ℤ) (c : ℝ) :
    IntegrableOn (fun x => Real.exp (c * x) * Cvs.Finite.LevyKernelIncrement.Kc L m n x) (Ioi 0)
      (volume : Measure ℝ) := by
  have hmeas : Measurable (fun x => Real.exp (c * x) * Cvs.Finite.LevyKernelIncrement.Kc L m n x) :=
    (by fun_prop : Measurable fun x : ℝ => Real.exp (c * x)).mul
      (Cvs.Finite.LevyKernelIncrement.measurable_Kc L m n)
  have hsplit : Ioi (0:ℝ) = Ioc 0 L ∪ Ioi L := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ L
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · refine (integrableOn_const (C := Real.exp (|c| * L) * (2 + 2 / π))
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
    have h2 := Cvs.Finite.LevyKernelIncrement.abs_Kc_le hL m n hu0.le (v := u)
    exact mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
  · refine (integrableOn_zero (s := Ioi L)).congr_fun ?_ measurableSet_Ioi
    intro u hu
    show (0:ℝ) = Real.exp (c * u) * Cvs.Finite.LevyKernelIncrement.Kc L m n u
    rw [Cvs.Finite.LevyKernelIncrement.Kc_of_gt hu, mul_zero]

omit [DecidableEq ι] in
/-- **The pole channel of a bounded window function whose self-convolution is the kernel double
sum.** -/
theorem pole_of_rep {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {xi : ι → ℝ} {f : ℝ → ℝ}
    (hm : Measurable f) {C : ℝ} (hb : ∀ s, |f s| ≤ C) (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0)
    (hg : ∀ v, 0 ≤ v → selfConvolution f v
      = L / 2 * ∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v) :
    (∫ s : ℝ, f s * Real.exp (s / 2)) * (∫ s : ℝ, f s * Real.exp (-(s / 2)))
      = L / 2 * ∑ i, ∑ j, xi i * xi j * polePair L (mode i) (mode j) := by
  have h := Cvs.Finite.PoleTermLagFunctional.pairing_exp_bounded hL (1 / 2) hm hb hsupp
  simp only [show ∀ s : ℝ, 1 / 2 * s = s / 2 by intro s; ring] at h
  rw [h]
  -- the integrand as a function of the absolute lag
  set G : ℝ → ℝ := fun x => Real.exp (-(x / 2))
    * (L / 2 * ∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) |x|) with hG
  have hGeq : (fun x => Real.exp (-(x / 2)) * selfConvolution f x) = G := by
    funext x; simp only [hG, selfConvolution_abs_of_rep hg x]
  rw [hGeq]
  -- integrability of `G` on the line
  have hGint : Integrable G (volume : Measure ℝ) := by
    have hmeas : Measurable G := by
      apply (by fun_prop : Measurable fun x : ℝ => Real.exp (-(x / 2))).mul
      apply measurable_const.mul
      apply Finset.measurable_sum; intro i _
      apply Finset.measurable_sum; intro j _
      exact measurable_const.mul ((Cvs.Finite.LevyKernelIncrement.measurable_Kc L _ _).comp measurable_abs)
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Icc (-L) L) ?_ ?_
    · refine (integrableOn_const (C := Real.exp (L / 2)
        * (L / 2 * ∑ i, ∑ j, |xi i * xi j| * (2 + 2 / π)))
        (hs := measure_Icc_lt_top.ne)).mono' hmeas.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => ?_)
      obtain ⟨hx1, hx2⟩ := hx
      rw [Real.norm_eq_abs, hG]
      simp only []
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]
      have h1 : Real.exp (-(x / 2)) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith)
      have h2 : abs (∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) (abs x))
          ≤ ∑ i, ∑ j, |xi i * xi j| * (2 + 2 / π) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (Cvs.Finite.LevyKernelIncrement.abs_Kc_le hL _ _ (abs_nonneg x)) (abs_nonneg _)
      have h3 : 0 ≤ ∑ i, ∑ j, |xi i * xi j| * (2 + 2 / π) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
      exact mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by linarith)) (by positivity)
        (Real.exp_pos _).le
    · intro x hx
      have hxL : L < |x| := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      simp only [hG, Cvs.Finite.LevyKernelIncrement.Kc_of_gt hxL, mul_zero, Finset.sum_const_zero]
  -- split the line at zero and fold the negative half by evenness
  have hneg : ∫ x in Iic (0:ℝ), G x = ∫ x in Ioi (0:ℝ), G (-x) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  rw [← integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hGint, compl_Ioi, hneg,
    ← integral_add hGint.integrableOn (hGint.comp_neg).integrableOn]
  -- the summed integrand, pointwise on the positive half-line
  have hpt : ∀ x ∈ Ioi (0:ℝ), G x + G (-x)
      = ∑ i, ∑ j, L / 2 * (xi i * xi j) * ((Real.exp (-(x / 2)) + Real.exp (x / 2))
          * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) x) := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    simp only [hG, abs_neg, abs_of_pos hx0, neg_div, neg_neg]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : ∀ i j : ι, IntegrableOn (fun x => L / 2 * (xi i * xi j)
      * ((Real.exp (-(x / 2)) + Real.exp (x / 2)) * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) x))
      (Ioi 0) volume := by
    intro i j
    refine (((integrableOn_exp_mul_Kc hL (mode i) (mode j) (-(1/2))).add
      (integrableOn_exp_mul_Kc hL (mode i) (mode j) (1/2))).congr_fun ?_ measurableSet_Ioi).const_mul _
    intro x _
    simp only [Pi.add_apply]
    rw [show -(x / 2) = -(1 / 2) * x by ring, show x / 2 = 1 / 2 * x by ring]
    ring
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, polePair]
  ring

/-- **The pole channel on a mode sum is the double sum of pole pairings.** -/
theorem pole_modeSum {L : ℝ} (hL : 0 < L)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    (∫ s : ℝ, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi s * Real.exp (s / 2))
        * (∫ s : ℝ, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi s * Real.exp (-(s / 2)))
      = L / 2 * ∑ i, ∑ j, xi i * xi j * polePair L (mode i) (mode j) :=
  pole_of_rep hL (measurable_modeSum L mode xi) (abs_modeSum_le L mode xi)
    (fun _ hs => modeSum_eq_zero_of_notMem L mode xi hs)
    (fun _ hv => Cvs.Finite.LevyChannelDoubleSum.selfConvolution_modeSum_Kc hL mode hinv hmode hxieven hv)

/-! ### The prime channel -/

/-- The prime pairing of the cut kernel: the truncated prime side evaluated on `2·Kc`. -/
def primePair (P R : ℕ) (L : ℝ) (m n : ℤ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    primePowerWeight p r * (2 * Cvs.Finite.LevyKernelIncrement.Kc L m n (r * Real.log p))

omit [DecidableEq ι] in
/-- **The prime channel on a mode sum is the double sum of prime pairings.** -/
theorem sum_comm4 {α β : Type*} (S : Finset α) (T : Finset β) (F : α → β → ι → ι → ℝ) :
    ∑ p ∈ S, ∑ r ∈ T, ∑ i, ∑ j, F p r i j = ∑ i, ∑ j, ∑ p ∈ S, ∑ r ∈ T, F p r i j := by
  calc ∑ p ∈ S, ∑ r ∈ T, ∑ i, ∑ j, F p r i j
      = ∑ p ∈ S, ∑ i, ∑ r ∈ T, ∑ j, F p r i j := Finset.sum_congr rfl fun p _ =>
          Finset.sum_comm (s := T) (t := (Finset.univ : Finset ι)) (f := fun r i => ∑ j, F p r i j)
    _ = ∑ i, ∑ p ∈ S, ∑ r ∈ T, ∑ j, F p r i j :=
        Finset.sum_comm (s := S) (t := (Finset.univ : Finset ι))
          (f := fun p i => ∑ r ∈ T, ∑ j, F p r i j)
    _ = ∑ i, ∑ p ∈ S, ∑ j, ∑ r ∈ T, F p r i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_comm (s := T) (t := (Finset.univ : Finset ι)) (f := fun r j => F p r i j)
    _ = ∑ i, ∑ j, ∑ p ∈ S, ∑ r ∈ T, F p r i j := Finset.sum_congr rfl fun i _ =>
          Finset.sum_comm (s := S) (t := (Finset.univ : Finset ι))
            (f := fun p j => ∑ r ∈ T, F p r i j)

omit [DecidableEq ι] in
/-- **The prime channel of a function whose self-convolution is the kernel double sum.** -/
theorem prime_of_rep {L : ℝ} (P R : ℕ) {mode : ι → ℤ} {xi : ι → ℝ} {f : ℝ → ℝ}
    (hg : ∀ v, 0 ≤ v → selfConvolution f v
      = L / 2 * ∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v) :
    primePowerSideTruncated P R (selfConvolution f)
      = L / 2 * ∑ i, ∑ j, xi i * xi j * primePair P R L (mode i) (mode j) := by
  set F : ℕ → ℕ → ι → ι → ℝ := fun p r i j => L / 2 * (xi i * xi j
    * (primePowerWeight p r * (2 * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) (r * Real.log p))))
    with hF
  have hlhs : primePowerSideTruncated P R (selfConvolution f)
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R, ∑ i, ∑ j, F p r i j := by
    unfold primePowerSideTruncated
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun r _ => ?_
    have hp2 : (2:ℝ) ≤ p := by
      have := (Finset.mem_filter.mp hp).2.two_le
      exact_mod_cast this
    have hlog : 0 ≤ (r : ℝ) * Real.log p :=
      mul_nonneg (Nat.cast_nonneg r) (Real.log_nonneg (by linarith))
    rw [Cvs.WeilForm.WeilFormReflection.selfConvolution_neg, hg _ hlog]
    simp only [hF, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrhs : L / 2 * ∑ i, ∑ j, xi i * xi j * primePair P R L (mode i) (mode j)
      = ∑ i, ∑ j, ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R, F p r i j := by
    unfold primePair
    simp only [hF, Finset.mul_sum]
  rw [hlhs, hrhs, sum_comm4]

/-- **The prime channel on a mode sum is the double sum of prime pairings.** -/
theorem prime_modeSum {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    primePowerSideTruncated P R (selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))
      = L / 2 * ∑ i, ∑ j, xi i * xi j * primePair P R L (mode i) (mode j) :=
  prime_of_rep P R
    (fun _ hv => Cvs.Finite.LevyChannelDoubleSum.selfConvolution_modeSum_Kc hL mode hinv hmode hxieven hv)

/-! ### The assembled form -/

/-- **The pair value**: the four channel pairings of the kernel at one pair of modes. -/
def pairQ (P R : ℕ) (L : ℝ) (m n : ℤ) : ℝ :=
  2 * polePair L m n + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * Cvs.Finite.CosineModeOverlap.K L m n 0
    + Cvs.Finite.LevyChannelDoubleSum.levyPair L m n - primePair P R L m n

omit [DecidableEq ι] in
/-- **The window Weil form of a bounded window function whose self-convolution is the kernel
double sum.** -/
theorem weilForm_of_rep {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} {xi : ι → ℝ} {f : ℝ → ℝ}
    (hm : Measurable f) {C : ℝ} (hb : ∀ s, |f s| ≤ C) (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0)
    (hg : ∀ v, 0 ≤ v → selfConvolution f v
      = L / 2 * ∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
      = L / 2 * ∑ i, ∑ j, xi i * xi j * pairQ P R L (mode i) (mode j) := by
  unfold Cvs.WeilForm.SelfConvolutionFunctional.weilForm
  rw [mul_assoc, pole_of_rep hL hm hb hsupp hg, Cvs.Finite.LevyChannelDoubleSum.levy_of_rep hL mode xi hg,
    prime_of_rep P R hg, hg 0 (le_refl 0)]
  simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_le hL.le, pairQ, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The window Weil form on a mode sum is the double sum over pair values.** -/
theorem weilForm_modeSum {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)
      = L / 2 * ∑ i, ∑ j, xi i * xi j * pairQ P R L (mode i) (mode j) :=
  weilForm_of_rep hL P R (measurable_modeSum L mode xi) (abs_modeSum_le L mode xi)
    (fun _ hs => modeSum_eq_zero_of_notMem L mode xi hs)
    (fun _ hv => Cvs.Finite.LevyChannelDoubleSum.selfConvolution_modeSum_Kc hL mode hinv hmode hxieven hv)

end Cvs.Finite.ModeSumPairValues
