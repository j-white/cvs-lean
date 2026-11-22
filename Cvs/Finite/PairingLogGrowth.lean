import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.HatLevyDeficit
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# The pairing grows at most logarithmically in the mode

A bounded cut function whose increment at the origin is Lipschitz with constant `K` has
`|Pair h| ≤ C·c_L + 8C·log(1 + K/2C)`: three channels are bounded by the sup norm, and the
Lévy channel by `∫₀¹ (2/u)·min(2C, Ku) du ≤ 8C·log(1 + K/2C)` plus a tail. On the cut sine and
the cut kernel this bounds `bval k` and `pairQ m n` by `c·(1 + log(1 + |m| + |n|))`.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.PairingLogGrowth

/-- The tail mass of the Lévy density beyond `1`. -/
def tailMass : ℝ := ∫ u in Ioi (1:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u

theorem tailMass_nonneg : 0 ≤ tailMass :=
  setIntegral_nonneg measurableSet_Ioi fun u hu =>
    (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (by linarith [mem_Ioi.mp hu])).le

/-- The prime-power weight mass of the truncation. -/
def primeMass (P R : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R, |primePowerWeight p r|

theorem primeMass_nonneg (P R : ℕ) : 0 ≤ primeMass P R :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The harmonic-mean bound**: `densityU u · |d| ≤ 4CK/(C + Ku)` when `|d| ≤ min(C, Ku)`. -/
theorem levy_pointwise {C K u d : ℝ} (hC : 0 < C) (hK : 0 ≤ K) (hu : 0 < u) (hu1 : u ≤ 1)
    (hd1 : |d| ≤ C) (hd2 : |d| ≤ K * u) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU u * |d| ≤ 4 * C * K / (C + K * u) := by
  have hKu : 0 ≤ K * u := mul_nonneg hK hu.le
  have hden : 0 < C + K * u := by linarith
  have ha : |d| * (K * u) ≤ C * (K * u) := mul_le_mul_of_nonneg_right hd1 hKu
  have hb : |d| * C ≤ K * u * C := mul_le_mul_of_nonneg_right hd2 hC.le
  have h1 : |d| * (C + K * u) ≤ 2 * C * K * u := by nlinarith [ha, hb]
  have h2 : |d| ≤ 2 * C * K * u / (C + K * u) := by rw [le_div_iff₀ hden]; exact h1
  have hρ := Cvs.WeilForm.Archimedean.HatLevyDeficit.densityU_le_two_div hu hu1
  calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * |d| ≤ (2 / u) * (2 * C * K * u / (C + K * u)) :=
        mul_le_mul hρ h2 (abs_nonneg d) (by positivity)
    _ = 4 * C * K / (C + K * u) := by field_simp; ring

/-- **The closed-form integral** `∫₀¹ 4CK/(C + Ku) du = 4C·log(1 + K/C)`. -/
theorem integral_levy_bound {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K) :
    ∫ u in Ioc (0:ℝ) 1, 4 * C * K / (C + K * u) = 4 * C * Real.log (1 + K / C) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hpos : ∀ u ∈ uIcc (0:ℝ) 1, 0 < C + K * u := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    nlinarith [mul_nonneg hK hu.1]
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt (fun u => 4 * C * Real.log (C + K * u))
      (4 * C * K / (C + K * u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u => C + K * u) K u := by
      simpa using ((hasDerivAt_id u).const_mul K).const_add C
    have h2 := (h1.log (hpos u hu).ne').const_mul (4 * C)
    exact h2.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun u => 4 * C * K / (C + K * u)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    have hc : ContinuousOn (fun u : ℝ => C + K * u) (uIcc 0 1) := by fun_prop
    exact (continuousOn_const (c := 4 * C * K)).div₀ hc fun u hu => (hpos u hu).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_one, mul_zero, add_zero]
  rw [← mul_sub, ← Real.log_div (by positivity) hC.ne']
  congr 2
  field_simp

/-- **The Lévy channel of a bounded, Lipschitz-at-zero increment.** -/
theorem abs_levy_le {g : ℝ → ℝ} {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K)
    (hint : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) (Ioi 0))
    (hd : ∀ u, 0 ≤ u → |g 0 - g (u / 2)| ≤ C)
    (hinc : ∀ u, 0 ≤ u → |g 0 - g (u / 2)| ≤ K * u) :
    |∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))|
      ≤ 4 * C * Real.log (1 + K / C) + C * tailMass := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]; intro u hu hu'; exact absurd hu.2 (not_le.mpr hu')
  have hi1 := hint.mono_set (Ioc_subset_Ioi_self : Ioc (0:ℝ) 1 ⊆ Ioi 0)
  have hi2 := hint.mono_set (Ioi_subset_Ioi zero_le_one : Ioi (1:ℝ) ⊆ Ioi 0)
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hi1 hi2]
  have hρ0 : ∀ u, 0 < u → 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u :=
    fun u hu => (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu).le
  -- the near part
  have hA : ‖∫ u in Ioc (0:ℝ) 1, Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))‖
      ≤ ∫ u in Ioc (0:ℝ) 1, 4 * C * K / (C + K * u) := by
    refine norm_integral_le_of_norm_le ?_ ?_
    · have hc : ContinuousOn (fun u : ℝ => 4 * C * K / (C + K * u)) (Icc 0 1) := by
        have hc' : ContinuousOn (fun u : ℝ => C + K * u) (Icc 0 1) := by fun_prop
        refine (continuousOn_const (c := 4 * C * K)).div₀ hc' fun u hu => ?_
        nlinarith [mul_nonneg hK hu.1]
      exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 u hu.1)]
      exact levy_pointwise hC hK hu.1 hu.2 (hd u hu.1.le) (hinc u hu.1.le)
  -- the tail
  have hB : ‖∫ u in Ioi (1:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))‖
      ≤ ∫ u in Ioi (1:ℝ), C * Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
    refine norm_integral_le_of_norm_le
      ((Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU one_pos).const_mul C) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := by linarith [mem_Ioi.mp hu]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 u hu0), mul_comm]
    exact mul_le_mul_of_nonneg_right (hd u hu0.le) (hρ0 u hu0)
  rw [integral_levy_bound hC hK] at hA
  rw [integral_const_mul] at hB
  rw [Real.norm_eq_abs] at hA hB
  calc _ ≤ |∫ u in Ioc (0:ℝ) 1, Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))|
        + |∫ u in Ioi (1:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))| := abs_add_le _ _
    _ ≤ _ := by unfold tailMass; linarith

/-- **The pairing of a bounded cut function is `O(C) + 8C·log(1 + K/2C)`.** -/
theorem abs_Pair_le {L : ℝ} (hL : 0 < L) (P R : ℕ) {g : ℝ → ℝ} {C K : ℝ} (hC : 0 < C)
    (hK : 0 ≤ K) (hbound : ∀ x, 0 ≤ x → |g x| ≤ C) (hzero : ∀ x, L < x → g x = 0)
    (hlevy : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) (Ioi 0))
    (hinc : ∀ u, 0 ≤ u → |g 0 - g (u / 2)| ≤ K * u) :
    |Cvs.Finite.PairFormDividedDifference.Pair P R g|
      ≤ C * (2 * L * (1 + Real.exp (L / 2)) + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0|
          + 2 * tailMass + 2 * primeMass P R)
        + 8 * C * Real.log (1 + K / (2 * C)) := by
  unfold Cvs.Finite.PairFormDividedDifference.Pair
  -- pole channel
  have hpoleb : |∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * g x|
      ≤ C * (L * (1 + Real.exp (L / 2))) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioc_subset_Ioi_self : Ioc (0:ℝ) L ⊆ Ioi 0) (fun x hx => ?_)]
    · have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0:ℝ) L)
        (f := fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * g x)
        (C := (1 + Real.exp (L / 2)) * C) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        (fun x hx => ?_)
      · rw [Real.volume_real_Ioc_of_le hL.le, Real.norm_eq_abs] at h
        linarith [h]
      · rw [Real.norm_eq_abs, abs_mul]
        have h1 : Real.exp (-(x / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1])
        have h2 : Real.exp (x / 2) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith [hx.2])
        have h3 : |Real.exp (-(x / 2)) + Real.exp (x / 2)| ≤ 1 + Real.exp (L / 2) := by
          rw [abs_of_pos (by positivity)]; linarith
        exact mul_le_mul h3 (hbound x hx.1.le) (abs_nonneg _) (by positivity)
    · simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hx
      rw [hzero x (hx.2 hx.1), mul_zero]
  -- arch channel
  have harch : |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * g 0|
      ≤ |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| * C := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbound 0 le_rfl) (abs_nonneg _)
  -- Lévy channel
  have hd : ∀ u, 0 ≤ u → |g 0 - g (u / 2)| ≤ 2 * C := fun u hu => by
    calc |g 0 - g (u / 2)| ≤ |g 0| + |g (u / 2)| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hbound 0 le_rfl, hbound (u / 2) (by linarith)]
  have hlevyb := abs_levy_le (by positivity : (0:ℝ) < 2 * C) hK hlevy hd hinc
  -- prime channel
  have hprime : |∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
      primePowerWeight p r * (2 * g (r * Real.log p))| ≤ 2 * C * primeMass P R := by
    unfold primeMass
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    have hp' : (1:ℝ) ≤ p := by
      have := (Finset.mem_filter.mp hp).2.one_lt
      exact_mod_cast this.le
    have hlog : 0 ≤ (r:ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg r) (Real.log_nonneg hp')
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := hbound _ hlog
    nlinarith [abs_nonneg (primePowerWeight p r), abs_nonneg (g (r * Real.log p))]
  rw [abs_le] at hpoleb harch hlevyb hprime
  rw [abs_le]
  constructor <;> nlinarith [hpoleb.1, hpoleb.2, harch.1, harch.2, hlevyb.1, hlevyb.2,
    hprime.1, hprime.2]

/-- The scale-dependent constant of the pairing bound. -/
def baseConst (L : ℝ) (P R : ℕ) : ℝ :=
  2 * L * (1 + Real.exp (L / 2)) + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 2 * tailMass
    + 2 * primeMass P R

theorem baseConst_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ) : 0 ≤ baseConst L P R := by
  unfold baseConst
  have := tailMass_nonneg
  have := primeMass_nonneg P R
  positivity

/-- **`bval k` grows at most like `log |k|`.** -/
theorem abs_bval_le {L : ℝ} (hL : 0 < L) (P R : ℕ) (k : ℤ) :
    |Cvs.Finite.PairFormDividedDifference.bval P R L k|
      ≤ (baseConst L P R + 8 * Real.log (1 + π * |(k:ℝ)| / (2 * L))) / L := by
  unfold Cvs.Finite.PairFormDividedDifference.bval
  rw [abs_div, abs_neg, abs_of_pos hL]
  refine div_le_div_of_nonneg_right ?_ hL.le
  have hinc : ∀ u, 0 ≤ u → |Cvs.Finite.PairFormDividedDifference.sigma L k 0
      - Cvs.Finite.PairFormDividedDifference.sigma L k (u / 2)| ≤ (π * |(k:ℝ)| / L) * u := by
    intro u hu
    rw [Cvs.Finite.PairFormDividedDifference.sigma_zero L hL.le, zero_sub, abs_neg]
    have := Cvs.Finite.PairFormDividedDifference.abs_sigma_le hL k (u / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)] at this
    calc _ ≤ 2 * π * |(k:ℝ)| / L * (u / 2) := this
      _ = (π * |(k:ℝ)| / L) * u := by ring
  have h := abs_Pair_le hL P R (C := 1) (K := π * |(k:ℝ)| / L) one_pos (by positivity)
    (fun x _ => Cvs.Finite.PairFormDividedDifference.abs_sigma_le_one L k x)
    (fun x hx => by unfold Cvs.Finite.PairFormDividedDifference.sigma; rw [ite_eq_right (not_le.mpr hx)])
    (Cvs.Finite.PairFormDividedDifference.integrableOn_densityU_mul_sigma hL k) hinc
  have e : π * |(k:ℝ)| / L / (2 * 1) = π * |(k:ℝ)| / (2 * L) := by ring
  rw [e] at h
  unfold baseConst
  linarith [h]

/-- The Lipschitz constant of the cut kernel's increment at the origin. -/
def kerLip (L : ℝ) (m n : ℤ) : ℝ := (2 + 1 / π + 2 * π * (|(m:ℝ)| + |(n:ℝ)|)) / L

/-- **The increment of the cut kernel is Lipschitz at the origin, on the whole ray.** -/
theorem abs_Kc_sub_le {L : ℝ} (hL : 0 < L) (m n : ℤ) {u : ℝ} (hu : 0 ≤ u) :
    |Cvs.Finite.LevyKernelIncrement.Kc L m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2)|
      ≤ kerLip L m n * u := by
  have hπ : 0 < π := Real.pi_pos
  rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le (hL.le : (0:ℝ) ≤ L)]
  unfold kerLip
  by_cases hu2 : u / 2 ≤ L
  · rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le hu2]
    have h := Cvs.Finite.KernelLipschitzOrigin.abs_K_sub_le hL m n (u / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)] at h
    refine h.trans ?_
    rw [show (2 / L + 4 * π * (|(m:ℝ)| + |(n:ℝ)|) / L) * (u / 2)
        = (1 + 2 * π * (|(m:ℝ)| + |(n:ℝ)|)) * u / L by field_simp; ring]
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hL.le
    have : 0 ≤ 1 / π := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) hu
  · rw [Cvs.Finite.LevyKernelIncrement.Kc_of_gt (not_le.mp hu2), sub_zero]
    have h := Cvs.Finite.LevyKernelIncrement.abs_K_le hL m n (le_refl (0:ℝ)) hL.le
    have hu2' : 2 * L < u := by linarith [not_le.mp hu2]
    refine h.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    have h1 : 0 ≤ 2 * π * (|(m:ℝ)| + |(n:ℝ)|) * u := by positivity
    have h2 : 1 / π * (2 * L) ≤ 1 / π * u := by
      exact mul_le_mul_of_nonneg_left hu2'.le (by positivity)
    have h3 : 2 / π = 1 / π * 2 := by ring
    nlinarith [h1, h2, h3]

/-- **`pairQ m n` grows at most like `log(|m| + |n|)`.** -/
theorem abs_pairQ_le {L : ℝ} (hL : 0 < L) (P R : ℕ) (m n : ℤ) :
    |Cvs.Finite.ModeSumPairValues.pairQ P R L m n|
      ≤ (2 + 2 / π) * baseConst L P R
        + 8 * (2 + 2 / π) * Real.log (1 + kerLip L m n / (2 * (2 + 2 / π))) := by
  have hπ : 0 < π := Real.pi_pos
  rw [Cvs.Finite.PairFormDividedDifference.pairQ_eq_Pair hL]
  have hlevy : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.LevyKernelIncrement.Kc L m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2))) (Ioi 0) := by
    rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le (hL.le : (0:ℝ) ≤ L)]
    exact Cvs.Finite.LevyKernelIncrement.integrableOn_densityU_mul_K_sub hL m n
  have hbound : ∀ x, 0 ≤ x → |Cvs.Finite.LevyKernelIncrement.Kc L m n x| ≤ 2 + 2 / π :=
    fun x hx => Cvs.Finite.LevyKernelIncrement.abs_Kc_le hL m n hx
  have hK0 : 0 ≤ kerLip L m n := by unfold kerLip; positivity
  have h := abs_Pair_le hL P R (C := 2 + 2 / π) (K := kerLip L m n) (by positivity) hK0 hbound
    (fun x hx => Cvs.Finite.LevyKernelIncrement.Kc_of_gt hx) hlevy
    (fun u hu => abs_Kc_sub_le hL m n hu)
  unfold baseConst at h ⊢
  linarith [h]

/-! ### Affine arguments inside the logarithm -/

/-- `log(1 + a + b·x) ≤ (1 + log(1 + a + b))·(1 + log(1 + x))` for nonnegative `a, b, x`. -/
theorem log_affine_le {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    Real.log (1 + a + b * x) ≤ (1 + Real.log (1 + a + b)) * (1 + Real.log (1 + x)) := by
  have h1 : 1 + a + b * x ≤ (1 + a + b) * (1 + x) := by nlinarith
  have h2 : Real.log (1 + a + b * x) ≤ Real.log ((1 + a + b) * (1 + x)) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (by positivity)] at h2
  have h3 : 0 ≤ Real.log (1 + a + b) := Real.log_nonneg (by linarith)
  have h4 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  nlinarith [mul_nonneg h3 h4]

/-- **`bval` is `O(1 + log(1 + |k|))`**, with a constant depending on the scale only. -/
theorem exists_bval_bound {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ k : ℤ,
      |Cvs.Finite.PairFormDividedDifference.bval P R L k| ≤ c * (1 + Real.log (1 + |(k:ℝ)|)) := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨(baseConst L P R + 8 * (1 + Real.log (1 + 0 + π / (2 * L)))) / L, by
    have := baseConst_nonneg hL P R
    have : 0 ≤ Real.log (1 + 0 + π / (2 * L)) := Real.log_nonneg (by
      have : 0 ≤ π / (2 * L) := by positivity
      linarith)
    positivity, fun k => ?_⟩
  refine (abs_bval_le hL P R k).trans ?_
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hL.le
  have hlog : Real.log (1 + π * |(k:ℝ)| / (2 * L))
      ≤ (1 + Real.log (1 + 0 + π / (2 * L))) * (1 + Real.log (1 + |(k:ℝ)|)) := by
    have := log_affine_le (a := 0) (b := π / (2 * L)) (x := |(k:ℝ)|) le_rfl (by positivity)
      (abs_nonneg _)
    rw [show (1:ℝ) + 0 + π / (2 * L) * |(k:ℝ)| = 1 + π * |(k:ℝ)| / (2 * L) by ring] at this
    exact this
  have h1 : 1 ≤ 1 + Real.log (1 + |(k:ℝ)|) := by
    linarith [Real.log_nonneg (by linarith [abs_nonneg (k:ℝ)] : (1:ℝ) ≤ 1 + |(k:ℝ)|)]
  have hb := baseConst_nonneg hL P R
  nlinarith [hlog, h1, hb]

/-- **`pairQ` is `O(1 + log(1 + |m| + |n|))`**, with a constant depending on the scale only. -/
theorem exists_pairQ_bound {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ m n : ℤ,
      |Cvs.Finite.ModeSumPairValues.pairQ P R L m n|
        ≤ c * (1 + Real.log (1 + (|(m:ℝ)| + |(n:ℝ)|))) := by
  have hπ : 0 < π := Real.pi_pos
  set C0 : ℝ := 2 + 2 / π with hC0
  have hC0p : 0 < C0 := by positivity
  set a : ℝ := (2 + 1 / π) / L / (2 * C0) with ha
  set b : ℝ := 2 * π / L / (2 * C0) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hlogab : 0 ≤ Real.log (1 + a + b) := Real.log_nonneg (by linarith)
  refine ⟨C0 * baseConst L P R + 8 * C0 * (1 + Real.log (1 + a + b)), by
    have := baseConst_nonneg hL P R
    positivity, fun m n => ?_⟩
  refine (abs_pairQ_le hL P R m n).trans ?_
  have hkey : kerLip L m n / (2 * C0) = a + b * (|(m:ℝ)| + |(n:ℝ)|) := by
    rw [ha, hb]; unfold kerLip; field_simp
  rw [hkey, ← add_assoc]
  have hlog := log_affine_le ha0 hb0 (by positivity : (0:ℝ) ≤ |(m:ℝ)| + |(n:ℝ)|)
  have h1 : 1 ≤ 1 + Real.log (1 + (|(m:ℝ)| + |(n:ℝ)|)) := by
    linarith [Real.log_nonneg (by linarith [abs_nonneg (m:ℝ), abs_nonneg (n:ℝ)] :
      (1:ℝ) ≤ 1 + (|(m:ℝ)| + |(n:ℝ)|))]
  have hb' := baseConst_nonneg hL P R
  have h8 : 0 ≤ 8 * C0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog h8, mul_nonneg (mul_nonneg hC0p.le hb') (sub_nonneg.mpr h1)]

end Cvs.Finite.PairingLogGrowth
