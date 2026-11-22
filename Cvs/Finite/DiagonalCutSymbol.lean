import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# The CvS diagonal is the cut symbol plus the derivative of the cut sine pairing

With `sinCut`, `cosCut`, `vcosCut` the cut sine, cosine and `v·cos` at a real frequency, the
diagonal kernel is `2 cosCut − (2/L) vcosCut`, and the sine pairing `ω ↦ Pair (sinCut L ω)` is
differentiable with derivative `Pair (vcosCut L ω)`. So `aval = Pair (cosCut) + (bval)'` at every
frequency: the CvS matrix is the Loewner matrix of `bval` plus the diagonal of the cut symbol.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.DiagonalCutSymbol

/-! ### The cut functions -/

def sinCut (L ω v : ℝ) : ℝ := if v ≤ L then Real.sin (ω * v) else 0
def cosCut (L ω v : ℝ) : ℝ := if v ≤ L then Real.cos (ω * v) else 0
def vcosCut (L ω v : ℝ) : ℝ := if v ≤ L then v * Real.cos (ω * v) else 0

theorem sigma_eq_sinCut (L : ℝ) (k : ℤ) :
    Cvs.Finite.PairFormDividedDifference.sigma L k = sinCut L (2 * π * k / L) := by
  funext v; unfold Cvs.Finite.PairFormDividedDifference.sigma sinCut
  split_ifs <;> [congr 1; rfl]
  ring

theorem Kc_diag_eq (L : ℝ) (k : ℤ) :
    Cvs.Finite.LevyKernelIncrement.Kc L k k
      = fun v => 2 * cosCut L (2 * π * k / L) v + (-(2 / L)) * vcosCut L (2 * π * k / L) v := by
  funext v; unfold Cvs.Finite.LevyKernelIncrement.Kc Cvs.Finite.CosineModeOverlap.K cosCut vcosCut
  simp only [if_true]
  split_ifs
  · have : 2 * π * k * v / L = 2 * π * k / L * v := by ring
    rw [this]; ring
  · ring

theorem measurable_sinCut (L ω : ℝ) : Measurable (sinCut L ω) :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
theorem measurable_cosCut (L ω : ℝ) : Measurable (cosCut L ω) :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
theorem measurable_vcosCut (L ω : ℝ) : Measurable (vcosCut L ω) :=
  Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

theorem sinCut_zero (L ω : ℝ) (hL : 0 ≤ L) : sinCut L ω 0 = 0 := by simp [sinCut, hL]
theorem vcosCut_zero (L ω : ℝ) (hL : 0 ≤ L) : vcosCut L ω 0 = 0 := by simp [vcosCut, hL]
theorem cosCut_zero (L ω : ℝ) (hL : 0 ≤ L) : cosCut L ω 0 = 1 := by simp [cosCut, hL]

theorem sinCut_of_gt {L ω v : ℝ} (h : L < v) : sinCut L ω v = 0 := by simp [sinCut, not_le.mpr h]
theorem cosCut_of_gt {L ω v : ℝ} (h : L < v) : cosCut L ω v = 0 := by simp [cosCut, not_le.mpr h]
theorem vcosCut_of_gt {L ω v : ℝ} (h : L < v) : vcosCut L ω v = 0 := by simp [vcosCut, not_le.mpr h]

theorem abs_sinCut_le_one (L ω v : ℝ) : |sinCut L ω v| ≤ 1 := by
  unfold sinCut; split_ifs
  · exact Real.abs_sin_le_one _
  · simp
theorem abs_cosCut_le_one (L ω v : ℝ) : |cosCut L ω v| ≤ 1 := by
  unfold cosCut; split_ifs
  · exact Real.abs_cos_le_one _
  · simp
theorem abs_vcosCut_le {L ω v : ℝ} (hv : 0 ≤ v) (hL : 0 ≤ L) : |vcosCut L ω v| ≤ L := by
  unfold vcosCut; split_ifs with h
  · rw [abs_mul, abs_of_nonneg hv]
    calc v * |Real.cos (ω * v)| ≤ v * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ ≤ L := by linarith
  · simp [hL]
theorem abs_sinCut_le (L ω v : ℝ) : |sinCut L ω v| ≤ |ω| * |v| := by
  unfold sinCut; split_ifs
  · calc |Real.sin (ω * v)| ≤ |ω * v| := Real.abs_sin_le_abs
      _ = |ω| * |v| := abs_mul _ _
  · simp only [abs_zero]; positivity
theorem abs_vcosCut_le_abs (L ω v : ℝ) : |vcosCut L ω v| ≤ |v| := by
  unfold vcosCut; split_ifs
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · simp

/-! ### Integrability of the cut functions in the pole and Lévy channels -/

/-- A bounded measurable function vanishing beyond `L` is integrable against `e^{cx}` on `(0, ∞)`. -/
theorem integrableOn_exp_mul_cut {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hm : Measurable g) {C : ℝ}
    (hb : ∀ v, 0 ≤ v → |g v| ≤ C) (hz : ∀ v, L < v → g v = 0) (c : ℝ) :
    IntegrableOn (fun x => Real.exp (c * x) * g x) (Ioi 0) (volume : Measure ℝ) := by
  have hmeas : Measurable (fun x => Real.exp (c * x) * g x) :=
    (by fun_prop : Measurable fun x : ℝ => Real.exp (c * x)).mul hm
  have hsplit : Ioi (0:ℝ) = Ioc 0 L ∪ Ioi L := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ L
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · refine (integrableOn_const (C := Real.exp (|c| * L) * C)
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
    exact mul_le_mul h1 (hb u hu0.le) (abs_nonneg _) (Real.exp_pos _).le
  · refine (integrableOn_zero (s := Ioi L)).congr_fun ?_ measurableSet_Ioi
    intro u hu
    show (0:ℝ) = Real.exp (c * u) * g u
    rw [hz u hu, mul_zero]

/-- A cut function with a Lipschitz increment at the origin is integrable against the Lévy
density on `(0, ∞)`. -/
theorem integrableOn_densityU_mul_cut {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hm : Measurable g)
    {K : ℝ} (hinc : ∀ u, 0 ≤ u → u ≤ 2 * L → |g 0 - g (u / 2)| ≤ K * u) {C : ℝ}
    (hb : ∀ u, 0 ≤ u → |g 0 - g (u / 2)| ≤ C) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) (Ioi 0)
      (volume : Measure ℝ) := by
  have hmeas : Measurable (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) :=
    Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
      (measurable_const.sub (hm.comp (measurable_id.div_const 2)))
  have hsplit : Ioi (0:ℝ) = Ioc 0 (2 * L) ∪ Ioi (2 * L) := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ 2 * L
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · refine (integrableOn_const (C := (1 + 2 * L) * K)
      (hs := measure_Ioc_lt_top.ne)).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
    obtain ⟨hu0, huL⟩ := hu
    have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hdpos]
    have hdu : Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u ≤ 1 + u := by
      have h := Cvs.WeilForm.Archimedean.LevyMeasure.densityU_le hu0
      have he : Real.exp (-(u / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u ≤ (1 + u) * Real.exp (-(u / 4)) / u * u := by gcongr
        _ = (1 + u) * Real.exp (-(u / 4)) := by field_simp
        _ ≤ (1 + u) * 1 := by gcongr
        _ = 1 + u := mul_one _
    have hK : 0 ≤ K := by
      have h1 := hinc u hu0.le huL; have h2 := abs_nonneg (g 0 - g (u / 2))
      by_contra hneg; push Not at hneg; nlinarith
    calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * |g 0 - g (u / 2)|
        ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (K * u) := by gcongr; exact hinc u hu0.le huL
      _ = (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u) * K := by ring
      _ ≤ (1 + u) * K := by gcongr
      _ ≤ (1 + 2 * L) * K := by gcongr
  · refine ((Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU (by linarith : (0:ℝ) < 2 * L)).const_mul
      C).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have hu0 : 0 < u := by simp only [mem_Ioi] at hu; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0), mul_comm]
    exact mul_le_mul_of_nonneg_right (hb u hu0.le) (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le

/-! ### Linearity of the pairing on two cut functions -/

theorem Pair_add_smul (P R : ℕ) {L : ℝ} (hL : 0 < L) (a b : ℝ) {f g : ℝ → ℝ}
    (hf1 : IntegrableOn (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * f x) (Ioi 0) volume)
    (hg1 : IntegrableOn (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * g x) (Ioi 0) volume)
    (hf2 : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (f 0 - f (u / 2))) (Ioi 0) volume)
    (hg2 : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) (Ioi 0) volume) :
    Cvs.Finite.PairFormDividedDifference.Pair P R (fun v => a * f v + b * g v)
      = a * Cvs.Finite.PairFormDividedDifference.Pair P R f + b * Cvs.Finite.PairFormDividedDifference.Pair P R g := by
  have _ : 0 < L := hL
  unfold Cvs.Finite.PairFormDividedDifference.Pair
  have hpole : (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * (a * f x + b * g x))
      = a * (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * f x)
        + b * ∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * g x := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf1.const_mul a) (hg1.const_mul b)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have hlevy : (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * ((a * f 0 + b * g 0) - (a * f (u / 2) + b * g (u / 2))))
      = a * (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (f 0 - f (u / 2)))
        + b * ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf2.const_mul a) (hg2.const_mul b)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have hprime : (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 * (a * f (r * Real.log p) + b * g (r * Real.log p))))
      = a * (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          primePowerWeight p r * (2 * f (r * Real.log p)))
        + b * ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          primePowerWeight p r * (2 * g (r * Real.log p)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hpole, hlevy, hprime]
  ring

/-- **The diagonal pair value is the cut symbol less `1/L` times the `v·cos` pairing.** -/
theorem pairQ_diag_eq (P R : ℕ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L k k
      = 2 * Cvs.Finite.PairFormDividedDifference.Pair P R (cosCut L (2 * π * k / L))
        - (2 / L) * Cvs.Finite.PairFormDividedDifference.Pair P R (vcosCut L (2 * π * k / L)) := by
  set ω : ℝ := 2 * π * k / L
  rw [Cvs.Finite.PairFormDividedDifference.pairQ_eq_Pair hL, Kc_diag_eq, Pair_add_smul P R hL]
  · ring
  · refine (integrableOn_exp_mul_cut hL (measurable_cosCut L ω) (C := 1)
      (fun v _ => abs_cosCut_le_one L ω v) (fun v hv => cosCut_of_gt hv) (-(1/2))).add
      (integrableOn_exp_mul_cut hL (measurable_cosCut L ω) (C := 1)
      (fun v _ => abs_cosCut_le_one L ω v) (fun v hv => cosCut_of_gt hv) (1/2)) |>.congr_fun
      ?_ measurableSet_Ioi
    intro x _; simp only [Pi.add_apply]
    rw [show -(x / 2) = -(1 / 2) * x by ring, show x / 2 = 1 / 2 * x by ring]; ring
  · refine (integrableOn_exp_mul_cut hL (measurable_vcosCut L ω) (C := L)
      (fun v hv => abs_vcosCut_le hv hL.le) (fun v hv => vcosCut_of_gt hv) (-(1/2))).add
      (integrableOn_exp_mul_cut hL (measurable_vcosCut L ω) (C := L)
      (fun v hv => abs_vcosCut_le hv hL.le) (fun v hv => vcosCut_of_gt hv) (1/2)) |>.congr_fun
      ?_ measurableSet_Ioi
    intro x _; simp only [Pi.add_apply]
    rw [show -(x / 2) = -(1 / 2) * x by ring, show x / 2 = 1 / 2 * x by ring]; ring
  · -- Lévy: `1 − cos(ωu/2)` is Lipschitz at the origin
    refine integrableOn_densityU_mul_cut hL (measurable_cosCut L ω) (K := |ω| / 2)
      (fun u hu huL => ?_) (C := 2) (fun u hu => ?_)
    · rw [cosCut_zero L ω hL.le]
      have hle : u / 2 ≤ L := by linarith
      simp only [cosCut, if_pos hle]
      calc |1 - Real.cos (ω * (u / 2))| ≤ |ω * (u / 2)| := Cvs.Finite.KernelLipschitzOrigin.abs_one_sub_cos_le _
        _ = |ω| / 2 * u := by rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]; ring
    · calc |cosCut L ω 0 - cosCut L ω (u / 2)| ≤ |cosCut L ω 0| + |cosCut L ω (u / 2)| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (abs_cosCut_le_one _ _ _) (abs_cosCut_le_one _ _ _)
        _ = 2 := by norm_num
  · refine integrableOn_densityU_mul_cut hL (measurable_vcosCut L ω) (K := 1/2)
      (fun u hu _ => ?_) (C := L) (fun u hu => ?_)
    · rw [vcosCut_zero L ω hL.le, zero_sub, abs_neg]
      calc |vcosCut L ω (u / 2)| ≤ |u / 2| := abs_vcosCut_le_abs _ _ _
        _ = 1 / 2 * u := by rw [abs_of_nonneg (by linarith)]; ring
    · rw [vcosCut_zero L ω hL.le, zero_sub, abs_neg]
      exact abs_vcosCut_le (by linarith) hL.le

/-! ### The sine pairing is differentiable in the frequency -/

/-- The cut sine is differentiable in `ω`, with derivative the cut `v·cos`. -/
theorem hasDerivAt_sinCut (L v ω : ℝ) : HasDerivAt (fun ω => sinCut L ω v) (vcosCut L ω v) ω := by
  unfold sinCut vcosCut
  split_ifs
  · have h := (hasDerivAt_mul_const v).sin (x := ω)
    simpa [mul_comm] using h
  · exact hasDerivAt_const _ _

/-- **The pole channel of the cut sine, differentiated in the frequency.** -/
theorem hasDerivAt_pole_sinCut {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    HasDerivAt (fun ω => ∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * sinCut L ω x)
      (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * vcosCut L ω x) ω := by
  have hint : ∀ ω, IntegrableOn (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * sinCut L ω x)
      (Ioi 0) volume := by
    intro ω
    refine ((integrableOn_exp_mul_cut hL (measurable_sinCut L ω) (C := 1)
      (fun v _ => abs_sinCut_le_one L ω v) (fun v hv => sinCut_of_gt hv) (-(1/2))).add
      (integrableOn_exp_mul_cut hL (measurable_sinCut L ω) (C := 1)
      (fun v _ => abs_sinCut_le_one L ω v) (fun v hv => sinCut_of_gt hv) (1/2))).congr_fun
      ?_ measurableSet_Ioi
    intro x _; simp only [Pi.add_apply]
    rw [show -(x / 2) = -(1 / 2) * x by ring, show x / 2 = 1 / 2 * x by ring]; ring
  have hbound : IntegrableOn (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2))
      * (if x ≤ L then L else 0)) (Ioi 0) volume := by
    refine ((integrableOn_exp_mul_cut hL (g := fun x => if x ≤ L then L else 0)
      (Measurable.ite measurableSet_Iic measurable_const measurable_const) (C := L)
      (fun v _ => ?_) (fun v hv => if_neg (not_le.mpr hv)) (-(1/2))).add
      (integrableOn_exp_mul_cut hL (g := fun x => if x ≤ L then L else 0)
      (Measurable.ite measurableSet_Iic measurable_const measurable_const) (C := L)
      (fun v _ => ?_) (fun v hv => if_neg (not_le.mpr hv)) (1/2))).congr_fun
      ?_ measurableSet_Ioi
    · split_ifs
      · rw [abs_of_nonneg hL.le]
      · simp [hL.le]
    · split_ifs
      · rw [abs_of_nonneg hL.le]
      · simp [hL.le]
    · intro x _; simp only [Pi.add_apply]
      rw [show -(x / 2) = -(1 / 2) * x by ring, show x / 2 = 1 / 2 * x by ring]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun ω x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * sinCut L ω x)
    (F' := fun ω x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * vcosCut L ω x)
    (x₀ := ω) (s := Set.univ) (bound := fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2))
      * (if x ≤ L then L else 0)) Filter.univ_mem
    (Filter.Eventually.of_forall fun ω => ((by fun_prop : Measurable fun x : ℝ =>
      Real.exp (-(x / 2)) + Real.exp (x / 2)).mul (measurable_sinCut L ω)).aestronglyMeasurable)
    (hint ω)
    ((by fun_prop : Measurable fun x : ℝ => Real.exp (-(x / 2)) + Real.exp (x / 2)).mul
      (measurable_vcosCut L ω)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx ω' _ => ?_) hbound
    (Filter.Eventually.of_forall fun x ω' _ => (hasDerivAt_sinCut L x ω').const_mul _)
  · exact h.2
  · have hx0 : (0:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold vcosCut
    split_ifs with hxL
    · rw [abs_mul, abs_of_pos hx0]
      calc x * |Real.cos (ω' * x)| ≤ x * 1 := by gcongr; exact Real.abs_cos_le_one _
        _ ≤ L := by linarith
    · simp

/-- **The Lévy channel of the cut sine, differentiated in the frequency.** -/
theorem hasDerivAt_levy_sinCut {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    HasDerivAt (fun ω => ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (sinCut L ω 0 - sinCut L ω (u / 2)))
      (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (vcosCut L ω 0 - vcosCut L ω (u / 2))) ω := by
  have hint : ∀ ω, IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (sinCut L ω 0 - sinCut L ω (u / 2))) (Ioi 0) volume := by
    intro ω
    refine integrableOn_densityU_mul_cut hL (measurable_sinCut L ω) (K := |ω| / 2)
      (fun u hu _ => ?_) (C := 2) (fun u hu => ?_)
    · rw [sinCut_zero L ω hL.le, zero_sub, abs_neg]
      calc |sinCut L ω (u / 2)| ≤ |ω| * |u / 2| := abs_sinCut_le _ _ _
        _ = |ω| / 2 * u := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]; ring
    · calc |sinCut L ω 0 - sinCut L ω (u / 2)| ≤ |sinCut L ω 0| + |sinCut L ω (u / 2)| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (abs_sinCut_le_one _ _ _) (abs_sinCut_le_one _ _ _)
        _ = 2 := by norm_num
  have hbound : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (if u ≤ 2 * L then u / 2 else 0)) (Ioi 0) volume := by
    have := integrableOn_densityU_mul_cut hL (g := fun v => if v ≤ L then -v else 0)
      (Measurable.ite measurableSet_Iic (by fun_prop) measurable_const) (K := 1/2)
      (fun u hu huL => ?_) (C := L) (fun u hu => ?_)
    · refine this.congr_fun (fun u hu => ?_) measurableSet_Ioi
      have hu0 : (0:ℝ) < u := hu
      simp only [hL.le, if_true, neg_zero, zero_sub]
      by_cases h : u ≤ 2 * L
      · rw [if_pos h, if_pos (by linarith : u / 2 ≤ L)]; ring
      · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]; ring
    · simp only [hL.le, if_true, neg_zero, zero_sub]
      rw [if_pos (by linarith : u / 2 ≤ L), neg_neg, abs_of_nonneg (by linarith)]; linarith
    · simp only [hL.le, if_true, neg_zero, zero_sub]
      split_ifs with h
      · rw [neg_neg, abs_of_nonneg (by linarith)]; linarith
      · simp [hL.le]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun ω u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (sinCut L ω 0 - sinCut L ω (u / 2)))
    (F' := fun ω u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (vcosCut L ω 0 - vcosCut L ω (u / 2)))
    (x₀ := ω) (s := Set.univ) (bound := fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (if u ≤ 2 * L then u / 2 else 0)) Filter.univ_mem
    (Filter.Eventually.of_forall fun ω => (Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
      (measurable_const.sub ((measurable_sinCut L ω).comp (measurable_id.div_const 2)))).aestronglyMeasurable)
    (hint ω)
    (Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
      (measurable_const.sub ((measurable_vcosCut L ω).comp (measurable_id.div_const 2)))).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ω' _ => ?_) hbound
    (Filter.Eventually.of_forall fun u ω' _ =>
      ((hasDerivAt_sinCut L 0 ω').sub (hasDerivAt_sinCut L (u / 2) ω')).const_mul _)
  · exact h.2
  · have hu0 : (0:ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0)]
    refine mul_le_mul_of_nonneg_left ?_ (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le
    rw [vcosCut_zero L ω' hL.le, zero_sub, abs_neg]
    unfold vcosCut
    by_cases h : u ≤ 2 * L
    · rw [if_pos (by linarith : u / 2 ≤ L), if_pos h, abs_mul,
        abs_of_pos (by linarith : (0:ℝ) < u / 2)]
      calc u / 2 * |Real.cos (ω' * (u / 2))| ≤ u / 2 * 1 := by gcongr; exact Real.abs_cos_le_one _
        _ = u / 2 := mul_one _
    · rw [if_neg (by intro h'; apply h; linarith), if_neg h]; simp

/-- **The pairing of the cut sine is differentiable in the frequency**, with derivative the
pairing of the cut `v·cos`. -/
theorem hasDerivAt_Pair_sinCut (P R : ℕ) {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    HasDerivAt (fun ω => Cvs.Finite.PairFormDividedDifference.Pair P R (sinCut L ω))
      (Cvs.Finite.PairFormDividedDifference.Pair P R (vcosCut L ω)) ω := by
  unfold Cvs.Finite.PairFormDividedDifference.Pair
  have h1 := hasDerivAt_pole_sinCut hL ω
  have h2 : HasDerivAt (fun ω : ℝ => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * sinCut L ω 0)
      (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * vcosCut L ω 0) ω := by
    have h0 : (fun ω : ℝ => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * sinCut L ω 0)
        = fun _ : ℝ => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * vcosCut L ω 0 := by
      funext ω'; rw [sinCut_zero L ω' hL.le, vcosCut_zero L ω hL.le]
    rw [h0, vcosCut_zero L ω hL.le, mul_zero]; exact hasDerivAt_const _ _
  have h3 := hasDerivAt_levy_sinCut hL ω
  have h4 : HasDerivAt (fun ω : ℝ => ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
        ∑ r ∈ Finset.Icc 1 R, primePowerWeight p r * (2 * sinCut L ω (r * Real.log p)))
      (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
        ∑ r ∈ Finset.Icc 1 R, primePowerWeight p r * (2 * vcosCut L ω (r * Real.log p))) ω :=
    HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun r _ =>
      ((hasDerivAt_sinCut L (r * Real.log p) ω).const_mul 2).const_mul _
  exact (((h1.const_mul 2).add h2).add h3).sub h4

/-- **`aval` is the cut symbol plus the derivative of `bval` in the frequency.** -/
theorem hasDerivAt_bval (P R : ℕ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    HasDerivAt (fun ω => -(Cvs.Finite.PairFormDividedDifference.Pair P R (sinCut L ω)) / L)
      (Cvs.Finite.PairFormDividedDifference.aval P R L k
        - Cvs.Finite.PairFormDividedDifference.Pair P R (cosCut L (2 * π * k / L))) (2 * π * k / L) := by
  have h := ((hasDerivAt_Pair_sinCut P R hL (2 * π * k / L)).neg).div_const L
  have heq : Cvs.Finite.PairFormDividedDifference.aval P R L k
      - Cvs.Finite.PairFormDividedDifference.Pair P R (cosCut L (2 * π * k / L))
      = -(Cvs.Finite.PairFormDividedDifference.Pair P R (vcosCut L (2 * π * k / L))) / L := by
    unfold Cvs.Finite.PairFormDividedDifference.aval
    rw [pairQ_diag_eq P R hL k]
    field_simp
    ring
  rw [heq]
  exact h

theorem bval_eq (P R : ℕ) (L : ℝ) (k : ℤ) :
    Cvs.Finite.PairFormDividedDifference.bval P R L k
      = -(Cvs.Finite.PairFormDividedDifference.Pair P R (sinCut L (2 * π * k / L))) / L := by
  unfold Cvs.Finite.PairFormDividedDifference.bval; rw [sigma_eq_sinCut]

end Cvs.Finite.DiagonalCutSymbol
