import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.StepA.StepACountDischarged
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.ArchimedeanBelowLogTwo
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MatrixPSDCriterion
import Cvs.WeilForm.OnePrimeWindow
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionMaximum
import Cvs.WeilForm.SelfConvolutionWindowEdge
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowSetNonempty
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Continuation of the even CvS section in the scale

A continuous family of bilinear forms on a finite-dimensional space over a preconnected set, PSD at one point and
never PSD-but-singular, is positive definite throughout. `L ↦ MX L N` is continuous on `L > 0`, and for `L ≤ log 2`
the window form is at least `F(L)‖φ‖²`, `F(L) = A₀ + ∫_{2L}^∞ densityU − 4 sinh(L/2) → +∞` as `L → 0⁺`. So RH is
`ExitFree N L_b`: on `[L_b, ∞)` the even section is never PSD and singular, for any `L_b ≤ log 2` with `F(L_b) ≥ 0`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Matrix Cvs.Zeta.Explicit.Weil

namespace Cvs.Route.EvenSectionContinuation
open Cvs.ZeroCounting

/-! ### The continuation lemma -/

section Continuation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A quadratic function positive on the nonzero vectors of a subspace of a finite-dimensional space is coercive
there. -/
theorem exists_coercive [FiniteDimensional ℝ V] (E : Submodule ℝ V) {q : V → ℝ} (hq : Continuous q)
    (hhom : ∀ (t : ℝ) v, q (t • v) = t ^ 2 * q v) (hpos : ∀ v ∈ E, v ≠ 0 → 0 < q v) :
    ∃ c > 0, ∀ v ∈ E, c * ‖v‖ ^ 2 ≤ q v := by
  set K : Set V := Metric.sphere 0 1 ∩ E with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right (Submodule.isClosed_of_finiteDimensional E)
  have hnorm : ∀ v : V, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := fun v hv => by
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne']
  have hscale : ∀ v : V, v ≠ 0 → q v = ‖v‖ ^ 2 * q (‖v‖⁻¹ • v) := fun v hv => by
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [hhom]
    field_simp
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · subst hv0
      have h0 : q 0 = 0 := by simpa using hhom 0 0
      simp [h0]
    · have hmem : ‖v‖⁻¹ • v ∈ K := ⟨hnorm v hv0, E.smul_mem _ hv⟩
      rw [he] at hmem
      exact absurd hmem (notMem_empty _)
  · obtain ⟨v₀, ⟨hv₀, hv₀E⟩, hmin⟩ := hKc.exists_isMinOn hne hq.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      intro h; rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at hv₀; exact zero_ne_one hv₀
    refine ⟨q v₀, hpos v₀ hv₀E hv₀ne, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · subst hv0
      have h0 : q 0 = 0 := by simpa using hhom 0 0
      simp [h0]
    · have h1 : q v₀ ≤ q (‖v‖⁻¹ • v) := hmin ⟨hnorm v hv0, E.smul_mem _ hv⟩
      rw [hscale v hv0]
      nlinarith [sq_nonneg ‖v‖]

/-- **Continuation**: over a preconnected parameter set, a locally uniformly continuous family of continuous
quadratic functions on a finite-dimensional space that is positive semidefinite on a subspace `E` at one point, and
positive definite on `E` wherever it is positive semidefinite on `E`, is positive definite on `E` at every point. -/
theorem posDef_of_exitFree [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) (E : Submodule ℝ V) (q : X → V → ℝ) (hq : ∀ x, Continuous (q x))
    (hhom : ∀ x (t : ℝ) v, q x (t • v) = t ^ 2 * q x v)
    (hunif : ∀ x₀ ∈ s, ∀ ε > 0, ∀ᶠ x in 𝓝[s] x₀, ∀ v, |q x v - q x₀ v| ≤ ε * ‖v‖ ^ 2)
    {a : X} (ha : a ∈ s) (hbase : ∀ v ∈ E, 0 ≤ q a v)
    (hexit : ∀ x ∈ s, (∀ v ∈ E, 0 ≤ q x v) → ∀ v ∈ E, v ≠ 0 → 0 < q x v) :
    ∀ x ∈ s, ∀ v ∈ E, v ≠ 0 → 0 < q x v := by
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hloc : ∀ x : s, ∀ ε > 0, ∀ᶠ y : s in 𝓝 x, ∀ v, |q (y : X) v - q (x : X) v| ≤ ε * ‖v‖ ^ 2 := by
    intro x ε hε
    have h := hunif x x.2 ε hε
    rw [nhdsWithin_eq_map_subtype_coe x.2] at h
    exact Filter.eventually_map.mp h
  set S : Set s := {x | ∀ v ∈ E, 0 ≤ q x v} with hSdef
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    simp only [hSdef, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hx
    obtain ⟨v, hv, hneg⟩ := hx
    have hn : 0 < ‖v‖ ^ 2 + 1 := by positivity
    filter_upwards [hloc x (-q x v / (‖v‖ ^ 2 + 1)) (div_pos (by linarith) hn)] with y hy
    simp only [hSdef, mem_compl_iff, mem_ofPred_eq, not_forall, not_le]
    refine ⟨v, hv, ?_⟩
    have h1 := (abs_le.mp (hy v)).2
    have h2 : -q x v / (‖v‖ ^ 2 + 1) * ‖v‖ ^ 2 < -q x v := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hn]; nlinarith
    linarith
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨c, hc, hcoer⟩ := exists_coercive E (hq x) (hhom x) (hexit x x.2 hx)
    filter_upwards [hloc x c hc] with y hy v hv
    have h1 := (abs_le.mp (hy v)).1
    linarith [hcoer v hv]
  have huniv : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨a, ha⟩, hbase⟩
  intro x hx v hv hv0
  have hxS : (⟨x, hx⟩ : s) ∈ S := huniv ▸ mem_univ _
  exact hexit x hx hxS v hv hv0

variable {ι : Type*} [Fintype ι]

/-- The quadratic form of a matrix is bounded by the sum of its entries' sizes, in the sup norm. -/
theorem abs_quad_le (A : Matrix ι ι ℝ) (v : ι → ℝ) : |v ⬝ᵥ (A *ᵥ v)| ≤ (∑ i, ∑ j, |A i j|) * ‖v‖ ^ 2 := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hv : ∀ k, |v k| ≤ ‖v‖ := fun k => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k
  rw [abs_mul, abs_mul]
  calc |v i| * (|A i j| * |v j|) ≤ ‖v‖ * (|A i j| * ‖v‖) := by gcongr <;> exact hv _
    _ = |A i j| * ‖v‖ ^ 2 := by ring

/-- **Continuation for matrices on a subspace**: an entrywise continuous matrix family, PSD on `E` at one point of a
preconnected set and never PSD-but-singular on `E` there, is positive definite on `E` throughout. -/
theorem posDefOn_of_exitFree {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    (E : Submodule ℝ (ι → ℝ)) {M : X → Matrix ι ι ℝ} (hM : ∀ i j, ContinuousOn (fun x => M x i j) s)
    {a : X} (ha : a ∈ s) (hbase : ∀ ξ ∈ E, 0 ≤ ξ ⬝ᵥ (M a *ᵥ ξ))
    (hexit : ∀ x ∈ s, (∀ ξ ∈ E, 0 ≤ ξ ⬝ᵥ (M x *ᵥ ξ)) → ∀ ξ ∈ E, ξ ≠ 0 → 0 < ξ ⬝ᵥ (M x *ᵥ ξ)) :
    ∀ x ∈ s, ∀ ξ ∈ E, ξ ≠ 0 → 0 < ξ ⬝ᵥ (M x *ᵥ ξ) := by
  refine posDef_of_exitFree hs E (fun x ξ => ξ ⬝ᵥ (M x *ᵥ ξ)) (fun x => ?_) (fun x t ξ => ?_) ?_ ha hbase hexit
  · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  · simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
  · intro x₀ hx₀ ε hε
    have hc : ContinuousOn (fun x => ∑ i, ∑ j, |M x i j - M x₀ i j|) s :=
      continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
        ((hM i j).sub continuousOn_const).abs
    have hsum : Tendsto (fun x => ∑ i, ∑ j, |M x i j - M x₀ i j|) (𝓝[s] x₀) (𝓝 0) := by
      simpa using (hc x₀ hx₀).tendsto
    filter_upwards [hsum.eventually (ge_mem_nhds hε)] with x hx ξ
    have h := abs_quad_le (M x - M x₀) ξ
    simp only [sub_mulVec, dotProduct_sub, Matrix.sub_apply] at h
    exact h.trans (by gcongr)

end Continuation

/-! ### The kernel in the scale -/

/-- The unit-window kernel is continuous in its lag. -/
theorem continuous_K_one (m n : ℤ) : Continuous (Cvs.Finite.CosineModeOverlap.K 1 m n) := by
  unfold Cvs.Finite.CosineModeOverlap.K; split_ifs <;> fun_prop

/-- The kernel at lag zero does not see the scale. -/
theorem K_zero (L : ℝ) (m n : ℤ) : Cvs.Finite.CosineModeOverlap.K L m n 0 = Cvs.Finite.CosineModeOverlap.K 1 m n 0 := by
  simp [Cvs.Finite.CosineModeOverlap.K]

/-- **The cut kernel is the unit kernel at the clamped relative lag**: `Kc_L(v) = K_1(min(v/L, 1))`. -/
theorem Kc_eq_K_one {L : ℝ} (hL : 0 < L) (v : ℝ) (m n : ℤ) :
    Cvs.Finite.LevyKernelIncrement.Kc L m n v = Cvs.Finite.CosineModeOverlap.K 1 m n (min (v / L) 1) := by
  by_cases h : v ≤ L
  · rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le h, min_eq_left ((div_le_one hL).2 h)]
    simp only [Cvs.Finite.CosineModeOverlap.K, div_one]
    split_ifs <;> ring_nf
  · push Not at h
    rw [Cvs.Finite.LevyKernelIncrement.Kc_of_gt h, min_eq_right ((one_le_div hL).2 h.le), Cvs.WeilForm.ArchimedeanBelowLogTwo.K_at_edge one_ne_zero]

/-- The cut kernel at a fixed lag is continuous in the scale. -/
theorem continuousOn_Kc (m n : ℤ) (v : ℝ) :
    ContinuousOn (fun L => Cvs.Finite.LevyKernelIncrement.Kc L m n v) (Ioi 0) := by
  have h1 : ContinuousOn (fun L : ℝ => v / L) (Ioi 0) :=
    continuousOn_const.div continuousOn_id fun L hL => ne_of_gt hL
  have h2 : ContinuousOn (fun L : ℝ => min (v / L) 1) (Ioi 0) :=
    continuous_min.comp_continuousOn (h1.prodMk continuousOn_const)
  exact ((continuous_K_one m n).comp_continuousOn h2).congr fun L hL => Kc_eq_K_one hL v m n

/-- `|K_L(0)| ≤ 2`. -/
theorem abs_K_zero_le (L : ℝ) (m n : ℤ) : |Cvs.Finite.CosineModeOverlap.K L m n 0| ≤ 2 := by
  simp only [Cvs.Finite.CosineModeOverlap.K]; split_ifs <;> simp

/-! ### The channels in the scale -/

/-- **The pole channel is continuous in the scale.** -/
theorem continuousOn_polePair (m n : ℤ) : ContinuousOn (fun L => Cvs.Finite.ModeSumPairValues.polePair L m n) (Ioi 0) := by
  intro L₀ hL₀
  have hL₀' : (0 : ℝ) < L₀ := hL₀
  set w : ℝ → ℝ := fun x => Real.exp (-(x / 2)) + Real.exp (x / 2) with hw
  have hwc : Continuous w := by rw [hw]; fun_prop
  have hw0 : ∀ x, 0 ≤ w x := fun x => by rw [hw]; positivity
  set bound : ℝ → ℝ := (Icc 0 (2 * L₀)).indicator fun x => w x * (2 + 2 / π) with hbound
  have hsub : Ioo (L₀ / 2) (2 * L₀) ⊆ Ioi 0 := fun L hL => lt_trans (by linarith : (0:ℝ) < L₀ / 2) hL.1
  have hcont : ContinuousOn (fun L => ∫ x in Ioi (0:ℝ), w x * Cvs.Finite.LevyKernelIncrement.Kc L m n x) (Ioo (L₀ / 2) (2 * L₀)) := by
    refine continuousOn_of_dominated (bound := bound) (fun L _ => ?_) (fun L hL => ?_) ?_ ?_
    · exact (hwc.measurable.mul (Cvs.Finite.LevyKernelIncrement.measurable_Kc L m n)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      have hL0 : 0 < L := hsub hL
      have hx0 : (0:ℝ) ≤ x := le_of_lt hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x)]
      by_cases hx2 : x ≤ 2 * L₀
      · rw [hbound, indicator_of_mem (show x ∈ Icc 0 (2 * L₀) from ⟨hx0, hx2⟩)]
        exact mul_le_mul_of_nonneg_left (Cvs.Finite.LevyKernelIncrement.abs_Kc_le hL0 m n hx0) (hw0 x)
      · rw [hbound, indicator_of_notMem (fun h : x ∈ Icc 0 (2 * L₀) => hx2 h.2),
          Cvs.Finite.LevyKernelIncrement.Kc_of_gt (by linarith [hL.2]), abs_zero, mul_zero]
    · refine Integrable.restrict ?_
      rw [hbound, integrable_indicator_iff measurableSet_Icc]
      exact (hwc.mul continuous_const).integrableOn_Icc
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        continuousOn_const.mul ((continuousOn_Kc m n x).mono hsub)
  exact ((hcont.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))).continuousWithinAt :
    ContinuousWithinAt (fun L => ∫ x in Ioi (0:ℝ), w x * Cvs.Finite.LevyKernelIncrement.Kc L m n x) (Ioi 0) L₀)

/-- **The Lévy channel is continuous in the scale.** -/
theorem continuousOn_levyPair (m n : ℤ) : ContinuousOn (fun L => Cvs.Finite.LevyChannelDoubleSum.levyPair L m n) (Ioi 0) := by
  intro L₀ hL₀
  have hL₀' : (0 : ℝ) < L₀ := hL₀
  have hπ : 0 < π := Real.pi_pos
  set C : ℝ := 2 / (L₀ / 2) + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / (L₀ / 2) with hC
  have hC0 : 0 ≤ C := by positivity
  set D : ℝ := 2 * (2 + 2 / π) with hD
  set bound : ℝ → ℝ := fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * min (C * (u / 2)) D with hbound
  have hsub : Ioo (L₀ / 2) (2 * L₀) ⊆ Ioi 0 := fun L hL => lt_trans (by linarith : (0:ℝ) < L₀ / 2) hL.1
  have hfun : (fun L => Cvs.Finite.LevyChannelDoubleSum.levyPair L m n) = fun L => ∫ u in Ioi (0:ℝ),
      Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (Cvs.Finite.CosineModeOverlap.K 1 m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2)) := by
    funext L; unfold Cvs.Finite.LevyChannelDoubleSum.levyPair; rw [K_zero]
  rw [hfun]
  have hpt : ∀ L ∈ Ioo (L₀ / 2) (2 * L₀), ∀ u, 0 < u →
      |Cvs.Finite.CosineModeOverlap.K 1 m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2)| ≤ min (C * (u / 2)) D := by
    intro L hL u hu
    have hL0 : 0 < L := hsub hL
    rw [← K_zero L]
    refine le_min ?_ ?_
    · by_cases hv : u / 2 ≤ L
      · rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le hv]
        refine (Cvs.Finite.KernelLipschitzOrigin.abs_K_sub_le hL0 m n (u / 2)).trans ?_
        rw [abs_of_pos (by linarith : (0:ℝ) < u / 2)]
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        have h1 : 2 / L ≤ 2 / (L₀ / 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hL.1.le
        have h2 : 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L ≤ 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / (L₀ / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hL.1.le
        linarith
      · push Not at hv
        rw [Cvs.Finite.LevyKernelIncrement.Kc_of_gt hv, sub_zero]
        refine (abs_K_zero_le L m n).trans ?_
        have h3 : 2 / (L₀ / 2) * (u / 2) ≥ 2 := by
          rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith [hL.1]
        have h4 : 0 ≤ 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / (L₀ / 2) * (u / 2) := by positivity
        rw [hC, add_mul]; linarith
    · refine (abs_sub _ _).trans ?_
      have h1 := Cvs.Finite.LevyKernelIncrement.abs_K_le hL0 m n le_rfl hL0.le
      have h2 := Cvs.Finite.LevyKernelIncrement.abs_Kc_le hL0 m n (by linarith : (0:ℝ) ≤ u / 2)
      rw [hD]; linarith
  have hcont : ContinuousOn (fun L => ∫ u in Ioi (0:ℝ),
      Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (Cvs.Finite.CosineModeOverlap.K 1 m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2))) (Ioo (L₀ / 2) (2 * L₀)) := by
    refine continuousOn_of_dominated (bound := bound) (fun L _ => ?_) (fun L hL => ?_) ?_ ?_
    · exact (Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul (measurable_const.sub
        ((Cvs.Finite.LevyKernelIncrement.measurable_Kc L m n).comp (measurable_id.div_const 2)))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : (0:ℝ) < u := hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0)]
      exact mul_le_mul_of_nonneg_left (hpt L hL u hu0) (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le
    · have hmeas : Measurable bound := Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
        ((measurable_const.mul (measurable_id.div_const 2)).min measurable_const)
      have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
      show IntegrableOn bound (Ioi 0) volume
      rw [hsplit]
      refine IntegrableOn.union ?_ ?_
      · refine (integrableOn_const (C := 3 * C / 2) (hs := measure_Ioc_lt_top.ne)).mono'
          hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
        obtain ⟨hu0, hu1⟩ := hu
        have hd := Cvs.WeilForm.WindowSetNonempty.densityU_mul_le hu0 hu1
        have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
        have hmin : min (C * (u / 2)) D ≤ C * (u / 2) := min_le_left _ _
        have hmin0 : 0 ≤ min (C * (u / 2)) D := le_min (by positivity) (by rw [hD]; positivity)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdpos.le hmin0)]
        calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * min (C * (u / 2)) D
            ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (C * (u / 2)) := mul_le_mul_of_nonneg_left hmin hdpos.le
          _ = (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u) * C / 2 := by ring
          _ ≤ 3 * C / 2 := by gcongr
      · refine ((Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU one_pos).const_mul D).mono'
          hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
        have hu0 : (0:ℝ) < u := lt_trans one_pos hu
        have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
        have hmin0 : 0 ≤ min (C * (u / 2)) D := le_min (by positivity) (by rw [hD]; positivity)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdpos.le hmin0), mul_comm D]
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) hdpos.le
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => continuousOn_const.mul
        (continuousOn_const.sub ((continuousOn_Kc m n (u / 2)).mono hsub))
  exact (hcont.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))).continuousWithinAt

/-- At a fixed truncation the prime channel is continuous in the scale. -/
theorem continuousOn_primePair (P R : ℕ) (m n : ℤ) :
    ContinuousOn (fun L => Cvs.Finite.ModeSumPairValues.primePair P R L m n) (Ioi 0) := by
  unfold Cvs.Finite.ModeSumPairValues.primePair
  exact continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun r _ =>
    continuousOn_const.mul (continuousOn_const.mul
      (continuousOn_Kc m n (r * Real.log p)))

/-- **The prime channel is unchanged past a complete truncation**: `e^L ≤ P ≤ P'`, `L ≤ R log 2`, `R ≤ R'`. -/
theorem primePair_eq_of_complete {L : ℝ} (hL : 0 < L) {P R P' R' : ℕ} (hP : Real.exp L ≤ P)
    (hR : L ≤ R * Real.log 2) (hPP : P ≤ P') (hRR : R ≤ R') (m n : ℤ) :
    Cvs.Finite.ModeSumPairValues.primePair P' R' L m n = Cvs.Finite.ModeSumPairValues.primePair P R L m n := by
  unfold Cvs.Finite.ModeSumPairValues.primePair
  have hzero : ∀ p r : ℕ, p.Prime → L ≤ r * Real.log p →
      primePowerWeight p r * (2 * Cvs.Finite.LevyKernelIncrement.Kc L m n (r * Real.log p)) = 0 := fun p r _ h => by
    rw [Cvs.WeilForm.ArchimedeanBelowLogTwo.Kc_eq_zero_of_le hL.ne' m n h]; ring
  symm
  calc ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 * Cvs.Finite.LevyKernelIncrement.Kc L m n (r * Real.log p))
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R',
        primePowerWeight p r * (2 * Cvs.Finite.LevyKernelIncrement.Kc L m n (r * Real.log p)) := by
        refine Finset.sum_congr rfl fun p hp => Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hRR) ?_
        intro r hr hr'
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hRr : R < r := by
          by_contra h; exact hr' (Finset.mem_Icc.mpr ⟨hr1, not_lt.mp h⟩)
        have h2p : Real.log 2 ≤ Real.log p :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le)
        have hRr' : (R : ℝ) ≤ r := by exact_mod_cast hRr.le
        refine hzero p r hpp ?_
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        nlinarith
    _ = ∑ p ∈ (Finset.range (P' + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R',
        primePowerWeight p r * (2 * Cvs.Finite.LevyKernelIncrement.Kc L m n (r * Real.log p)) := by
        refine Finset.sum_subset (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega))) ?_
        intro p hp hp'
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have hPp : P < p := by
          by_contra h
          exact hp' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩)
        refine Finset.sum_eq_zero fun r hr => hzero p r hpp ?_
        have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hlog : L ≤ Real.log p := by
          rw [Real.le_log_iff_exp_le hp0]
          exact hP.trans (by exact_mod_cast hPp.le)
        have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        nlinarith

/-- **The pair value at the complete truncation is continuous in the scale.** -/
theorem continuousOn_pairQ_complete (m n : ℤ) :
    ContinuousOn (fun L => Cvs.Finite.ModeSumPairValues.pairQ ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m n) (Ioi 0) := by
  intro L₀ hL₀
  have hL₀' : (0 : ℝ) < L₀ := hL₀
  set P₁ := ⌈Real.exp (L₀ + 1)⌉₊
  set R₁ := ⌈(L₀ + 1) / Real.log 2⌉₊
  have hg : ContinuousOn (fun L => Cvs.Finite.ModeSumPairValues.pairQ P₁ R₁ L m n) (Ioi 0) := by
    unfold Cvs.Finite.ModeSumPairValues.pairQ
    exact (((continuousOn_const.mul (continuousOn_polePair m n)).add (continuousOn_const.mul
      (continuousOn_const.congr fun L _ => K_zero L m n))).add (continuousOn_levyPair m n)).sub
      (continuousOn_primePair P₁ R₁ m n)
  have heq : (fun L => Cvs.Finite.ModeSumPairValues.pairQ P₁ R₁ L m n) =ᶠ[𝓝 L₀]
      fun L => Cvs.Finite.ModeSumPairValues.pairQ ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m n := by
    filter_upwards [Ioo_mem_nhds hL₀' (lt_add_one L₀)] with L hL
    unfold Cvs.Finite.ModeSumPairValues.pairQ
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [primePair_eq_of_complete hL.1 (Cvs.WeilForm.MatrixPSDCriterion.complete L).1 (Cvs.WeilForm.MatrixPSDCriterion.complete L).2
      (Nat.ceil_mono (Real.exp_le_exp.2 hL.2.le)) (Nat.ceil_mono (div_le_div_of_nonneg_right hL.2.le hl2.le))]
  exact ((hg.continuousAt (Ioi_mem_nhds hL₀')).congr heq).continuousWithinAt

/-- **The even CvS section is continuous in the scale**, entrywise. -/
theorem continuousOn_MX_apply (N : ℕ) (i j : Cvs.Finite.SymmetricModeSet.Idx N) :
    ContinuousOn (fun L => Cvs.Finite.ParitySectorDefect.MX L N i j) (Ioi 0) :=
  ((continuousOn_pairQ_complete _ _).div_const 2).congr fun _ hL =>
    Cvs.Finite.TruncationQuadraticForm.M_apply hL _ _ (Cvs.Finite.SymmetricModeSet.mode_injective N) i j

/-- **The CvS section is continuous in the scale.** -/
theorem continuousOn_MX (N : ℕ) : ContinuousOn (fun L => Cvs.Finite.ParitySectorDefect.MX L N) (Ioi 0) :=
  continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => continuousOn_MX_apply N i j

/-! ### The floor below `log 2` with the Lévy tail kept -/

/-- The floor constant: `F(L) = A₀ + ∫_{2L}^∞ densityU − 4 sinh(L/2)`. -/
def F (L : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + (∫ u in Ioi (2 * L), Cvs.WeilForm.Archimedean.LevyDensity.densityU u) - 4 * Real.sinh (L / 2)

/-- **The window form on `(0, L]`, `L ≤ log 2`, is at least `F(L)‖φ‖²`**, at every truncation. -/
theorem Q_ge_F {L : ℝ} (hL : 0 < L) (hL2 : L ≤ Real.log 2) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL.le) :
    F L * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) with hfdef
  obtain ⟨hQ, hn⟩ := Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hn' : selfConvolution f 0 = ‖φ‖ ^ 2 := hn
  have hf2 : MemLp f 2 volume := Cvs.WeilForm.WindowRepresentative.memLp_rep _
  have hsupp : ∀ s ∉ Ioc (0:ℝ) L, f s = 0 := Cvs.WeilForm.WindowRepresentative.rep_supp _
  have hsq : Integrable (fun s => f s ^ 2) := hf2.integrable_sq
  have hcross : ∀ u : ℝ, Integrable (fun s => f s * f (s + u)) := fun u =>
    hf2.integrable_mul (hf2.comp_measurePreserving (measurePreserving_add_right volume u))
  have hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  -- the pole term
  have hpole := Cvs.WeilForm.WindowCircleIsometry.neg_sinh_le_poleTerm_rep hL.le φ
  -- the prime term vanishes
  have hprime : Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R f = 0 := by
    unfold Cvs.WeilForm.PoleArchPrimeProblem.primeTerm primePowerSideTruncated
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun r hr => ?_
    have hlag : L ≤ (r : ℝ) * Real.log p := hL2.trans
      (Cvs.WeilForm.ArchimedeanBelowLogTwo.log_two_le_prime_lag (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp hr).1)
    have h0 : 0 ≤ (r : ℝ) * Real.log p := hL.le.trans hlag
    rw [Cvs.WeilForm.OnePrimeWindow.selfConvolution_eq_zero_of_le_abs hsupp (by rwa [abs_of_nonneg h0]),
      Cvs.WeilForm.OnePrimeWindow.selfConvolution_eq_zero_of_le_abs hsupp (by rwa [abs_neg, abs_of_nonneg h0])]
    ring
  -- the Lévy tail past `2L` sees the full energy
  have hnonneg : ∀ u ∈ Ioi (0:ℝ), 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := fun u hu =>
    mul_nonneg (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu).le
      (sub_nonneg.mpr (Cvs.WeilForm.SelfConvolutionMaximum.selfConvolution_le (u / 2) hsq (hcross (u / 2))))
  have htail : (∫ u in Ioi (2 * L), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u)
      = (∫ u in Ioi (2 * L), Cvs.WeilForm.Archimedean.LevyDensity.densityU u) * selfConvolution f 0 := by
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : L ≤ |u / 2| := by
      have : 2 * L < u := hu
      rw [abs_of_pos (by linarith)]; linarith
    simp only [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.OnePrimeWindow.selfConvolution_eq_zero_of_le_abs hsupp hu', sub_zero]
  have hmono : (∫ u in Ioi (2 * L), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u) ≤ ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u :=
    setIntegral_mono_set hdom (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg)
      (Ioi_subset_Ioi (by linarith)).eventuallySubset
  have harch : Cvs.WeilForm.PoleArchPrimeProblem.archTerm f = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
      + ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := rfl
  have hform : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm f + Cvs.WeilForm.PoleArchPrimeProblem.archTerm f - Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R f := by
    show Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) = _
    rw [hQ, Cvs.WeilForm.PoleArchPrimeProblem.weilForm_split]
  rw [hform, hprime, harch, F]
  rw [hn'] at htail ⊢
  nlinarith

/-- `F` is antitone on `(0, ∞)`. -/
theorem F_anti {l L : ℝ} (hl : 0 < l) (hlL : l ≤ L) : F L ≤ F l := by
  unfold F
  have h1 : (∫ u in Ioi (2 * L), Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      ≤ ∫ u in Ioi (2 * l), Cvs.WeilForm.Archimedean.LevyDensity.densityU u :=
    setIntegral_mono_set (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU (by linarith))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
        (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (lt_trans (by linarith : (0:ℝ) < 2 * l) hu)).le)
      (Ioi_subset_Ioi (by linarith)).eventuallySubset
  have h2 : Real.sinh (l / 2) ≤ Real.sinh (L / 2) := Real.sinh_le_sinh.mpr (by linarith)
  linarith

/-- **`F → +∞` as `L → 0⁺`**: the Lévy tail grows like `log(1/L)`. -/
theorem tendsto_F : Tendsto F (𝓝[>] 0) atTop := by
  set c : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 - 4 * Real.sinh (1 / 4) - 1 / 16 - Real.log 2 with hc
  have hlim : Tendsto (fun L => c + -Real.log L) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_left _ c (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1 / 2)] with L hL
  obtain ⟨hL0, hL1⟩ := hL
  have hlow := Cvs.WeilForm.SelfConvolutionWindowEdge.densityU_int_lower (a := 2 * L) (b := 1) (by linarith) (by linarith) le_rfl
  have hsub : (∫ u in Ioc (2 * L) 1, Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      ≤ ∫ u in Ioi (2 * L), Cvs.WeilForm.Archimedean.LevyDensity.densityU u :=
    setIntegral_mono_set (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU (by linarith))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
        (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (lt_trans (by linarith : (0:ℝ) < 2 * L) hu)).le)
      Ioc_subset_Ioi_self.eventuallySubset
  have hlog : Real.log (2 * L) = Real.log 2 + Real.log L := Real.log_mul (by norm_num) hL0.ne'
  have hsinh : Real.sinh (L / 2) ≤ Real.sinh (1 / 4) := Real.sinh_le_sinh.mpr (by linarith)
  rw [Real.log_one, hlog] at hlow
  unfold F
  nlinarith

/-- **Small bases exist**: eventually as `L_b → 0⁺`, `0 < L_b ≤ log 2` and `F(L_b) ≥ 0`. -/
theorem eventually_base : ∀ᶠ L_b in 𝓝[>] (0:ℝ), 0 < L_b ∧ L_b ≤ Real.log 2 ∧ 0 ≤ F L_b := by
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (Real.log_pos (by norm_num : (1:ℝ) < 2)),
    tendsto_F.eventually_ge_atTop 0] with L hL0 hL hF
  exact ⟨hL0, hL.2.le, hF⟩

/-! ### Small scales, the base, and the corner -/

/-- **Small scales**: `G(l) ≥ 0` for `0 < l ≤ L_b`, when `L_b ≤ log 2` and `F(L_b) ≥ 0`. -/
theorem G_nonneg_small {l L_b : ℝ} (hl : 0 < l) (hlb : l ≤ L_b) (hLb2 : L_b ≤ Real.log 2)
    (hF : 0 ≤ F L_b) : 0 ≤ Cvs.Route.OneCellLaplaceTransform.G l := by
  have h := Q_ge_F hl (hlb.trans hLb2) ⌈Real.exp l⌉₊ ⌈l / Real.log 2⌉₊ (Cvs.WeilForm.ReflectionEvenPositivityRH.boxD hl)
  rw [Cvs.WeilForm.ReflectionEvenPositivityRH.Q_boxD hl (Cvs.WeilForm.MatrixPSDCriterion.complete l).1 (Cvs.WeilForm.MatrixPSDCriterion.complete l).2, Cvs.WeilForm.ReflectionEvenPositivityRH.norm_sq_boxD] at h
  have hFl := F_anti hl hlb
  nlinarith

/-- **The base**: at `L_b ≤ log 2` with `F(L_b) ≥ 0` every even CvS section is positive semidefinite. -/
theorem base_even_nonneg {L_b : ℝ} (hLb : 0 < L_b) (hLb2 : L_b ≤ Real.log 2) (hF : 0 ≤ F L_b) (N : ℕ) :
    ∀ ξ ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N), 0 ≤ ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L_b N *ᵥ ξ) := fun _ hξ =>
  Cvs.Route.EvenMatrixSlotPoleRestored.M_even_nonneg_of_Q_evenSub_nonneg hLb _ _
    (fun η _ => (mul_nonneg hF (sq_nonneg _)).trans (Q_ge_F hLb hLb2 _ _ η)) N hξ

/-- The constant mode is even. -/
theorem single_none_mem (N : ℕ) : Pi.single none (1:ℝ) ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N) := by
  intro i
  cases i <;> simp [Cvs.Finite.SymmetricModeSet.negI]

/-- **The corner**: an even-PSD section at `L > 0` gives `G(L) ≥ 0`. -/
theorem G_nonneg_of_evenPSD {L : ℝ} (hL : 0 < L) {N : ℕ}
    (h : ∀ ξ ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N), 0 ≤ ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ ξ)) : 0 ≤ Cvs.Route.OneCellLaplaceTransform.G L := by
  have h1 := h _ (single_none_mem N)
  rw [Cvs.WeilForm.MatrixPSDCriterion.single_quad] at h1
  rw [← Cvs.WeilForm.MatrixPSDCriterion.corner_eq hL (Cvs.WeilForm.MatrixPSDCriterion.complete L).1 (Cvs.WeilForm.MatrixPSDCriterion.complete L).2 (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) (i₀ := none) rfl]
  exact mul_nonneg hL.le h1

/-! ### The open node and RH -/

/-- **No exit on `[L_b, ∞)`**: wherever the even CvS section is positive semidefinite it is positive definite. -/
def ExitFree (N : ℕ) (L_b : ℝ) : Prop :=
  ∀ L : ℝ, L_b ≤ L →
    (∀ ξ ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N), 0 ≤ ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ ξ)) →
    ∀ ξ ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N), ξ ≠ 0 → 0 < ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ ξ)

/-- **Continuation from the base**: under `ExitFree N L_b` the even section is positive definite on `[L_b, ∞)`. -/
theorem evenPosDef_of_exitFree {N : ℕ} {L_b : ℝ} (hLb : 0 < L_b) (hLb2 : L_b ≤ Real.log 2)
    (hF : 0 ≤ F L_b) (h : ExitFree N L_b) :
    ∀ L, L_b ≤ L → ∀ ξ ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N), ξ ≠ 0 → 0 < ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ ξ) :=
  posDefOn_of_exitFree isPreconnected_Ici _
    (fun i j => (continuousOn_MX_apply N i j).mono fun _ hL => lt_of_lt_of_le hLb hL)
    self_mem_Ici (base_even_nonneg hLb hLb2 hF N) h

/-- **`ExitFree` gives RH**, at any base `L_b ≤ log 2` with `F(L_b) ≥ 0`. -/
theorem rh_of_exitFree {N : ℕ} {L_b : ℝ} (hLb : 0 < L_b) (hLb2 : L_b ≤ Real.log 2) (hF : 0 ≤ F L_b)
    (h : ExitFree N L_b) : RiemannHypothesis := by
  refine Cvs.Route.OneCellCriterion.riemannHypothesis_of_G_nonneg fun L hL => ?_
  rcases le_or_gt L L_b with h1 | h1
  · exact G_nonneg_small hL h1 hLb2 hF
  · refine G_nonneg_of_evenPSD hL (N := N) fun ξ hξ => ?_
    by_cases h0 : ξ = 0
    · simp [h0]
    · exact (evenPosDef_of_exitFree hLb hLb2 hF h L h1.le ξ hξ h0).le

/-- **RH gives `ExitFree`** at every positive base. -/
theorem exitFree_of_rh (hRH : RiemannHypothesis) (N : ℕ) {L_b : ℝ} (hLb : 0 < L_b) : ExitFree N L_b :=
  fun L hL _ ξ _ hξ => by
    simpa using (Cvs.StepA.StepACountDischarged.posDef_of_RH hRH (lt_of_lt_of_le hLb hL) N).dotProduct_mulVec_pos hξ

/-- **RH ⟺ `ExitFree N L_b`**, for every `N` and every base `0 < L_b ≤ log 2` with `F(L_b) ≥ 0`. -/
theorem rh_iff_exitFree (N : ℕ) {L_b : ℝ} (hLb : 0 < L_b) (hLb2 : L_b ≤ Real.log 2) (hF : 0 ≤ F L_b) :
    RiemannHypothesis ↔ ExitFree N L_b :=
  ⟨fun hRH => exitFree_of_rh hRH N hLb, rh_of_exitFree hLb hLb2 hF⟩

/-- **RH ⟺ `ExitFree N L_b` for all small `L_b`**, with no side condition. -/
theorem rh_iff_exitFree_nhds (N : ℕ) : RiemannHypothesis ↔ ∀ᶠ L_b in 𝓝[>] (0:ℝ), ExitFree N L_b := by
  refine ⟨fun hRH => eventually_nhdsWithin_of_forall fun L_b hLb => exitFree_of_rh hRH N hLb, fun h => ?_⟩
  obtain ⟨L_b, hE, hLb, hLb2, hF⟩ := (h.and eventually_base).exists
  exact rh_of_exitFree hLb hLb2 hF hE

/-- **At `N = 0` the exit-free condition is the one-cell criterion**: `G` has no zero on `[L_b, ∞)`. -/
theorem exitFree_zero_iff {L_b : ℝ} (hLb : 0 < L_b) :
    ExitFree 0 L_b ↔ ∀ L, L_b ≤ L → Cvs.Route.OneCellLaplaceTransform.G L ≠ 0 := by
  have hc : ∀ L, 0 < L → L * Cvs.Finite.ParitySectorDefect.MX L 0 none none = Cvs.Route.OneCellLaplaceTransform.G L := fun L hL =>
    Cvs.WeilForm.MatrixPSDCriterion.corner_eq hL (Cvs.WeilForm.MatrixPSDCriterion.complete L).1 (Cvs.WeilForm.MatrixPSDCriterion.complete L).2 (Cvs.Finite.SymmetricModeSet.mode_injective 0)
      (Cvs.Finite.SymmetricModeSet.negI_involutive 0) (Cvs.Finite.SymmetricModeSet.mode_negI 0) (i₀ := none) rfl
  have hq : ∀ L (ξ : Cvs.Finite.SymmetricModeSet.Idx 0 → ℝ), ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L 0 *ᵥ ξ) = ξ none ^ 2 * Cvs.Finite.ParitySectorDefect.MX L 0 none none := by
    intro L ξ
    simp [dotProduct, mulVec]; show ξ none * (Cvs.Finite.ParitySectorDefect.MX L 0 none none * ξ none) = _; ring
  constructor
  · intro h L hL hG
    have hL0 : 0 < L := lt_of_lt_of_le hLb hL
    have hM : Cvs.Finite.ParitySectorDefect.MX L 0 none none = 0 := by
      have := hc L hL0; rw [hG] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 hL0.ne'
      · exact h1
    have := h L hL (fun ξ _ => by rw [hq, hM]; simp) _ (single_none_mem 0) (by simp)
    rw [hq, hM] at this; simp at this
  · intro h L hL hpsd ξ _ hξ
    have hL0 : 0 < L := lt_of_lt_of_le hLb hL
    have h1 := hpsd _ (single_none_mem 0)
    rw [hq] at h1; simp at h1
    have hne : Cvs.Finite.ParitySectorDefect.MX L 0 none none ≠ 0 := by
      intro h0; apply h L hL; rw [← hc L hL0, h0, mul_zero]
    have hξ0 : ξ none ≠ 0 := by
      intro h0; apply hξ; funext i; cases i with
      | none => exact h0
      | some k => exact k.1.elim0
    rw [hq]; exact mul_pos (by positivity) (lt_of_le_of_ne h1 (Ne.symm hne))

end Cvs.Route.EvenSectionContinuation
