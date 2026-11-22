import Mathlib
import Cvs.Finite.CutModePoleChannel
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# The Lévy channel of the cut modes as a series of closed forms, at every scale
With `densityU u = ∑_k e^{−c_k u}`, `c_k = k + 1/4`, dominated convergence writes the Lévy integral of a
cut function as the sum of its Laplace integrals (`hasSum_levy`). For `ω` with `cos ωL = 1`,
`sin ωL = 0`, `ν = ω/2`, `E_k = e^{−2Lc_k}`, `D_k = c_k² + ν²`, the terms are: `1/c − c(1 − E)/D` for the
cosine, `−ν(1 − E)/D` for the sine, and `LcE/D − (c² − ν²)(1 − E)/(2D²)` for the ramp-weighted cosine.
-/

noncomputable section

open Real MeasureTheory Set Filter

namespace Cvs.Finite.CutModeLevySeries

/-- **The Lévy integral is the sum of the Laplace integrals of the density's exponentials.** -/
theorem hasSum_levy {g : ℝ → ℝ} (hm : Measurable g)
    (hint : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) (Ioi 0)) :
    HasSum (fun k : ℕ => ∫ u in Ioi (0:ℝ), Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (g 0 - g (u / 2)))
      (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) := by
  have hgm : Measurable (fun u => g 0 - g (u / 2)) :=
    measurable_const.sub (hm.comp (measurable_id.div_const 2))
  refine hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (bound := fun k u => Real.exp (-((1 / 4 + (k : ℝ)) * u)) * |g 0 - g (u / 2)|) ?_ ?_ ?_ ?_ ?_
  · intro k
    exact ((by fun_prop : Measurable fun u : ℝ => Real.exp (-((1 / 4 + (k : ℝ)) * u))).mul
      hgm).aestronglyMeasurable
  · intro k
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact ((Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu).mul_right _).summable
  · have heq : ∀ u ∈ Ioi (0:ℝ),
        ‖Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))‖
          = ∑' k : ℕ, Real.exp (-((1 / 4 + (k : ℝ)) * u)) * |g 0 - g (u / 2)| := by
      intro u hu
      rw [((Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu).mul_right _).tsum_eq, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu)]
    exact hint.norm.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => heq u hu))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact (Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu).mul_right _

/-- **The Laplace integral of a cut function**: an FTC part on `(0, 2L]` and an exponential tail. -/
theorem expInt_cut {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {f : ℝ → ℝ} (hf : Continuous f)
    {g : ℝ → ℝ} (hg : ∀ v, g v = if v ≤ L then f v else 0) {G : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (Real.exp (-(c * u)) * (f 0 - f (u / 2))) u) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(c * u)) * (g 0 - g (u / 2))
      = G (2 * L) - G 0 + f 0 * (Real.exp (-(c * (2 * L))) / c) := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 (2 * L) ∪ Ioi (2 * L) := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ 2 * L
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  have hdisj : Disjoint (Ioc (0:ℝ) (2 * L)) (Ioi (2 * L)) := by
    rw [Set.disjoint_left]; intro u hu hu'; exact absurd hu.2 (not_le.mpr hu')
  have h1 : EqOn (fun u => Real.exp (-(c * u)) * (g 0 - g (u / 2)))
      (fun u => Real.exp (-(c * u)) * (f 0 - f (u / 2))) (Ioc 0 (2 * L)) := by
    intro u hu
    simp only [hg, if_pos hL.le, if_pos (show u / 2 ≤ L by linarith [hu.2])]
  have h2 : EqOn (fun u => Real.exp (-(c * u)) * (g 0 - g (u / 2)))
      (fun u => f 0 * Real.exp ((-c) * u)) (Ioi (2 * L)) := by
    intro u hu
    have hu' : ¬ u / 2 ≤ L := by have : 2 * L < u := hu; intro h; linarith
    simp only [hg, if_pos hL.le, if_neg hu', sub_zero]
    rw [neg_mul]; ring
  have hc1 : Continuous (fun u => Real.exp (-(c * u)) * (f 0 - f (u / 2))) := by fun_prop
  have hi1 : IntegrableOn (fun u => Real.exp (-(c * u)) * (g 0 - g (u / 2))) (Ioc 0 (2 * L)) :=
    ((hc1.integrableOn_Icc).mono_set Ioc_subset_Icc_self).congr_fun h1.symm measurableSet_Ioc
  have hi2' : IntegrableOn (fun u => f 0 * Real.exp ((-c) * u)) (Ioi (2 * L)) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) (2 * L)).const_mul (f 0)
  have hi2 : IntegrableOn (fun u => Real.exp (-(c * u)) * (g 0 - g (u / 2))) (Ioi (2 * L)) :=
    IntegrableOn.congr_fun hi2' h2.symm measurableSet_Ioi
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hi1 hi2, setIntegral_congr_fun measurableSet_Ioc h1,
    setIntegral_congr_fun measurableSet_Ioi h2, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos hc), ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hG u) (hc1.intervalIntegrable _ _)]
  rw [show (-c) * (2 * L) = -(c * (2 * L)) by ring]
  field_simp

theorem exp_neg_mul_eq (c u : ℝ) : Real.exp ((-c) * u) = Real.exp (-(c * u)) := by rw [neg_mul]

/-- **The cosine's Laplace term.** -/
theorem levyTerm_cosCut {L ω c : ℝ} (hL : 0 < L) (hc : 0 < c) (hs : Real.sin (ω * L) = 0)
    (hcos : Real.cos (ω * L) = 1) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(c * u))
        * (Cvs.Finite.DiagonalCutSymbol.cosCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.cosCut L ω (u / 2))
      = 1 / c - c * (1 - Real.exp (-(c * (2 * L)))) / (c ^ 2 + (ω / 2) ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hD : c ^ 2 + (ω / 2) ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (ω / 2)])
  have hD' : (-c) ^ 2 + (ω / 2) ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (ω / 2)])
  have hc0 : c ≠ 0 := hc.ne'
  rw [expInt_cut hL hc (f := fun v => Real.cos (ω * v)) (by fun_prop) (g := Cvs.Finite.DiagonalCutSymbol.cosCut L ω)
    (fun v => rfl) (G := fun u => -Real.exp ((-c) * u) / c - Cvs.Finite.CutModePoleChannel.Fc (-c) (ω / 2) u)
    (fun u => ?_)]
  · unfold Cvs.Finite.CutModePoleChannel.Fc
    simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero]
    rw [show ω / 2 * (2 * L) = ω * L by ring, hs, hcos, exp_neg_mul_eq]
    field_simp
    ring
  · have h1 : HasDerivAt (fun u => -Real.exp ((-c) * u) / c) (Real.exp ((-c) * u)) u := by
      refine ((Cvs.Finite.CutModePoleChannel.hasDerivAt_exp_mul (-c) u).neg.div_const c).congr_deriv ?_
      field_simp
    have h2 := Cvs.Finite.CutModePoleChannel.hasDerivAt_Fc hD' u
    refine (h1.sub h2).congr_deriv ?_
    rw [exp_neg_mul_eq, show ω * (u / 2) = ω / 2 * u by ring]
    simp only [mul_zero, Real.cos_zero]
    ring

/-- **The sine's Laplace term.** -/
theorem levyTerm_sinCut {L ω c : ℝ} (hL : 0 < L) (hc : 0 < c) (hs : Real.sin (ω * L) = 0)
    (hcos : Real.cos (ω * L) = 1) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(c * u))
        * (Cvs.Finite.DiagonalCutSymbol.sinCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2))
      = -(ω / 2) * (1 - Real.exp (-(c * (2 * L)))) / (c ^ 2 + (ω / 2) ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hD : c ^ 2 + (ω / 2) ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (ω / 2)])
  have hD' : (-c) ^ 2 + (ω / 2) ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (ω / 2)])
  rw [expInt_cut hL hc (f := fun v => Real.sin (ω * v)) (by fun_prop) (g := Cvs.Finite.DiagonalCutSymbol.sinCut L ω)
    (fun v => rfl) (G := fun u => -Cvs.Finite.CutModePoleChannel.Fs (-c) (ω / 2) u) (fun u => ?_)]
  · unfold Cvs.Finite.CutModePoleChannel.Fs
    simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, zero_mul]
    rw [show ω / 2 * (2 * L) = ω * L by ring, hs, hcos, exp_neg_mul_eq]
    field_simp
    ring
  · refine (Cvs.Finite.CutModePoleChannel.hasDerivAt_Fs hD' u).neg.congr_deriv ?_
    rw [exp_neg_mul_eq, show ω * (u / 2) = ω / 2 * u by ring]
    simp only [mul_zero, Real.sin_zero]
    ring

/-- **The ramp-weighted cosine's Laplace term.** -/
theorem levyTerm_vcosCut {L ω c : ℝ} (hL : 0 < L) (hc : 0 < c) (hs : Real.sin (ω * L) = 0)
    (hcos : Real.cos (ω * L) = 1) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(c * u))
        * (Cvs.Finite.DiagonalCutSymbol.vcosCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.vcosCut L ω (u / 2))
      = L * c * Real.exp (-(c * (2 * L))) / (c ^ 2 + (ω / 2) ^ 2)
        - (c ^ 2 - (ω / 2) ^ 2) * (1 - Real.exp (-(c * (2 * L)))) / (2 * (c ^ 2 + (ω / 2) ^ 2) ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hD : c ^ 2 + (ω / 2) ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (ω / 2)])
  have hD' : (-c) ^ 2 + (ω / 2) ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (ω / 2)])
  rw [expInt_cut hL hc (f := fun v => v * Real.cos (ω * v)) (by fun_prop)
    (g := Cvs.Finite.DiagonalCutSymbol.vcosCut L ω) (fun v => rfl)
    (G := fun u => -(1 / 2) * Cvs.Finite.CutModePoleChannel.Fv (-c) (ω / 2) u) (fun u => ?_)]
  · unfold Cvs.Finite.CutModePoleChannel.Fv
    simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, zero_mul, one_mul]
    rw [show ω / 2 * (2 * L) = ω * L by ring, hs, hcos, exp_neg_mul_eq]
    field_simp
    ring
  · refine ((Cvs.Finite.CutModePoleChannel.hasDerivAt_Fv hD' u).const_mul (-(1 / 2))).congr_deriv ?_
    rw [exp_neg_mul_eq, show ω * (u / 2) = ω / 2 * u by ring]
    simp only [mul_zero, Real.cos_zero, zero_mul]
    ring

/-! ### The three series -/

theorem integrableOn_levy_cosCut {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.DiagonalCutSymbol.cosCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.cosCut L ω (u / 2))) (Ioi 0) := by
  refine Cvs.Finite.DiagonalCutSymbol.integrableOn_densityU_mul_cut hL (Cvs.Finite.DiagonalCutSymbol.measurable_cosCut L ω)
    (K := |ω| / 2) (fun u hu hu2 => ?_) (C := 2) (fun u hu => ?_)
  · rw [Cvs.Finite.DiagonalCutSymbol.cosCut_zero L ω hL.le]
    unfold Cvs.Finite.DiagonalCutSymbol.cosCut
    rw [if_pos (by linarith : u / 2 ≤ L)]
    calc |1 - Real.cos (ω * (u / 2))| ≤ |ω * (u / 2)| := Cvs.Finite.KernelLipschitzOrigin.abs_one_sub_cos_le _
      _ = |ω| / 2 * u := by rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]; ring
  · calc |Cvs.Finite.DiagonalCutSymbol.cosCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.cosCut L ω (u / 2)|
        ≤ |Cvs.Finite.DiagonalCutSymbol.cosCut L ω 0| + |Cvs.Finite.DiagonalCutSymbol.cosCut L ω (u / 2)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Cvs.Finite.DiagonalCutSymbol.abs_cosCut_le_one _ _ _)
          (Cvs.Finite.DiagonalCutSymbol.abs_cosCut_le_one _ _ _)
      _ = 2 := by norm_num

theorem integrableOn_levy_sinCut {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.DiagonalCutSymbol.sinCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2))) (Ioi 0) := by
  refine Cvs.Finite.DiagonalCutSymbol.integrableOn_densityU_mul_cut hL (Cvs.Finite.DiagonalCutSymbol.measurable_sinCut L ω)
    (K := |ω| / 2) (fun u hu _ => ?_) (C := 2) (fun u hu => ?_)
  · rw [Cvs.Finite.DiagonalCutSymbol.sinCut_zero L ω hL.le, zero_sub, abs_neg]
    calc |Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2)| ≤ |ω| * |u / 2| := Cvs.Finite.DiagonalCutSymbol.abs_sinCut_le _ _ _
      _ = |ω| / 2 * u := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]; ring
  · calc |Cvs.Finite.DiagonalCutSymbol.sinCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2)|
        ≤ |Cvs.Finite.DiagonalCutSymbol.sinCut L ω 0| + |Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Cvs.Finite.DiagonalCutSymbol.abs_sinCut_le_one _ _ _)
          (Cvs.Finite.DiagonalCutSymbol.abs_sinCut_le_one _ _ _)
      _ = 2 := by norm_num

theorem integrableOn_levy_vcosCut {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.DiagonalCutSymbol.vcosCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.vcosCut L ω (u / 2))) (Ioi 0) := by
  refine Cvs.Finite.DiagonalCutSymbol.integrableOn_densityU_mul_cut hL (Cvs.Finite.DiagonalCutSymbol.measurable_vcosCut L ω)
    (K := 1 / 2) (fun u hu _ => ?_) (C := L) (fun u hu => ?_)
  · rw [Cvs.Finite.DiagonalCutSymbol.vcosCut_zero L ω hL.le, zero_sub, abs_neg]
    calc |Cvs.Finite.DiagonalCutSymbol.vcosCut L ω (u / 2)| ≤ |u / 2| := Cvs.Finite.DiagonalCutSymbol.abs_vcosCut_le_abs _ _ _
      _ = 1 / 2 * u := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]; ring
  · rw [Cvs.Finite.DiagonalCutSymbol.vcosCut_zero L ω hL.le, zero_sub, abs_neg]
    exact Cvs.Finite.DiagonalCutSymbol.abs_vcosCut_le (by linarith) hL.le

/-- The channel exponent `c_k = k + 1/4`. -/
abbrev cq (k : ℕ) : ℝ := 1 / 4 + (k : ℝ)

theorem cq_pos (k : ℕ) : 0 < cq k := by unfold cq; positivity

/-- **The Lévy channel of the cut sine, as a series.** -/
theorem hasSum_levy_sinCut {L ω : ℝ} (hL : 0 < L) (hs : Real.sin (ω * L) = 0) (hcos : Real.cos (ω * L) = 1) :
    HasSum (fun k : ℕ => -(ω / 2) * (1 - Real.exp (-(cq k * (2 * L)))) / (cq k ^ 2 + (ω / 2) ^ 2))
      (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (Cvs.Finite.DiagonalCutSymbol.sinCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2))) := by
  have h := hasSum_levy (Cvs.Finite.DiagonalCutSymbol.measurable_sinCut L ω) (integrableOn_levy_sinCut hL ω)
  rwa [show (fun k : ℕ => ∫ u in Ioi (0:ℝ), Real.exp (-((1 / 4 + (k : ℝ)) * u))
      * (Cvs.Finite.DiagonalCutSymbol.sinCut L ω 0 - Cvs.Finite.DiagonalCutSymbol.sinCut L ω (u / 2)))
      = (fun k : ℕ => -(ω / 2) * (1 - Real.exp (-(cq k * (2 * L)))) / (cq k ^ 2 + (ω / 2) ^ 2))
      from funext fun k => levyTerm_sinCut hL (cq_pos k) hs hcos] at h

end Cvs.Finite.CutModeLevySeries
