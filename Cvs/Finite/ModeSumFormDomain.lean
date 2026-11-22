import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# Mode sums and sine sums as form-domain classes

The cosine and sine sums lie in the window set (normalised, Lévy integrand integrable) and give
form-domain classes on which the reflection acts as `+1` and `−1`; so the sine sums are orthogonal
to the even minimiser.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.ModeSumFormDomain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Square integrability and the Lévy integrand -/

/-- A bounded measurable window function is square-integrable. -/
theorem memLp_two_of_bounded {L : ℝ} {f : ℝ → ℝ} (hm : Measurable f) {C : ℝ}
    (hb : ∀ s, |f s| ≤ C) (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0) :
    MemLp f 2 (volume : Measure ℝ) := by
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ioc 0 L) ?_ ?_
  · refine (integrableOn_const (C := C ^ 2) (hs := measure_Ioc_lt_top.ne)).mono'
      (hm.pow_const 2).aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc
        fun s _ => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb s) 2
  · intro s hs; rw [hsupp s hs]; ring

/-- The self-convolution at lag zero is the integral of the square. -/
theorem selfConvolution_zero_eq (f : ℝ → ℝ) : selfConvolution f 0 = ∫ x, f x ^ 2 := by
  unfold selfConvolution
  congr 1; funext x; rw [add_zero]; ring

omit [DecidableEq ι] in
/-- **The Lévy integrand of a kernel-represented function is integrable.** -/
theorem integrableOn_levy_of_rep {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {c : ι → ℝ} {f : ℝ → ℝ}
    (hg : ∀ v, 0 ≤ v → selfConvolution f v
      = L / 2 * ∑ i, ∑ j, c i * c j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) (volume : Measure ℝ) := by
  have hpt : ∀ u ∈ Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u
      = ∑ i, ∑ j, L / 2 * (c i * c j) * (Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0
            - Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) (u / 2))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [hg 0 (le_refl 0), hg (u / 2) (by linarith)]
    simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_le hL.le, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : IntegrableOn (fun u => ∑ i, ∑ j, L / 2 * (c i * c j) * (Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0
        - Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) (u / 2)))) (Ioi 0) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (Cvs.Finite.LevyKernelIncrement.integrableOn_densityU_mul_K_sub hL (mode i) (mode j)).const_mul
        (L / 2 * (c i * c j))
  exact IntegrableOn.congr_fun hint (fun u hu => (hpt u hu).symm) measurableSet_Ioi

/-! ### The cosine sum in the even window set -/

omit [DecidableEq ι] in
theorem modeSum_smul (L : ℝ) (mode : ι → ℤ) (t : ℝ) (xi : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (t • xi)
      = fun y => t * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi y := by
  funext y; simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  · ring

omit [DecidableEq ι] in
/-- The cosine sum is even about the midpoint on the open window. -/
theorem modeSum_reflect (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) L) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi (L - y) = Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi y := by
  have h1 : L - y ∈ Ioc (0:ℝ) L := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h2 : y ∈ Ioc (0:ℝ) L := ⟨hy.1, hy.2.le⟩
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, ite_eq_left h1, ite_eq_left h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : L ≠ 0 := by linarith [hy.1, hy.2]
  have : Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * (L - y)
      = (mode i : ℝ) * (2 * π) * (L / L) - Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]; ring
  rw [this, div_self hL, mul_one, Real.cos_int_mul_two_pi_sub]

/-- A function vanishing off the window agrees a.e. with its reflection whenever it does so on
the open window, up to the sign `ε`. -/
theorem reflect_ae_of_window {L : ℝ} {f : ℝ → ℝ} (ε : ℝ)
    (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0)
    (hrefl : ∀ y ∈ Ioo (0:ℝ) L, f (L - y) = ε * f y) :
    (fun x => f (L - x)) =ᵐ[(volume : Measure ℝ)] fun x => ε * f x := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) ((Set.toFinite ({0, L} : Set ℝ)).measure_zero volume)
  by_contra hx0
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx0
  apply hx
  by_cases hy : x ∈ Ioo (0:ℝ) L
  · exact hrefl x hy
  · have hx1 : x ∉ Ioc (0:ℝ) L := by
      intro h; apply hy; exact ⟨h.1, lt_of_le_of_ne h.2 hx0.2⟩
    have hx2 : L - x ∉ Ioc (0:ℝ) L := by
      intro h; apply hy
      refine ⟨?_, by linarith [h.1]⟩
      have : x ≠ 0 := hx0.1
      have h2 := h.2
      rcases lt_or_gt_of_ne this with h3 | h3
      · linarith
      · exact h3
    rw [hsupp _ hx1, hsupp _ hx2, mul_zero]

/-- **A normalised even cosine sum lies in the even window set.** -/
theorem modeSum_mem_evenWindowSet {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hn : L * (xi ⬝ᵥ xi) = 1) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L := by
  have hg := fun (v : ℝ) (hv : 0 ≤ v) =>
    Cvs.Finite.LevyChannelDoubleSum.selfConvolution_modeSum_Kc hL mode hinv hmode hxieven hv
  refine ⟨⟨memLp_two_of_bounded (Cvs.Finite.ModeSumPairValues.measurable_modeSum L mode xi)
    (Cvs.Finite.ModeSumPairValues.abs_modeSum_le L mode xi)
    (fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L mode xi hs),
    fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L mode xi hs, ?_,
    integrableOn_levy_of_rep hL hg⟩, ?_⟩
  · rw [← selfConvolution_zero_eq,
      Cvs.Finite.PairFormDividedDifference.selfConvolution_modeSum_zero hL hinj hinv hmode hxieven, hn]
  · have := reflect_ae_of_window (f := Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) 1
      (fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L mode xi hs)
      (fun y hy => by rw [modeSum_reflect L mode xi hy, one_mul])
    simpa only [one_mul] using this

/-! ### The sine sum in the window set, odd under reflection -/

/-- **A normalised odd sine sum lies in the window set.** -/
theorem sineSum_mem_windowSet {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i)
    (hn : L * (o ⬝ᵥ o) = 1) :
    Cvs.Finite.OddSectorSineSums.sineSum L mode o ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := by
  have hg := fun (v : ℝ) (hv : 0 ≤ v) =>
    Cvs.Finite.OddSectorSineSums.selfConvolution_sineSum_Kc hL mode hinv hmode hodd hv
  refine ⟨memLp_two_of_bounded (Cvs.Finite.OddSectorSineSums.measurable_sineSum L mode o)
    (Cvs.Finite.OddSectorSineSums.abs_sineSum_le L mode o)
    (fun s hs => Cvs.Finite.OddSectorSineSums.sineSum_eq_zero_of_notMem L mode o hs),
    fun s hs => Cvs.Finite.OddSectorSineSums.sineSum_eq_zero_of_notMem L mode o hs, ?_,
    integrableOn_levy_of_rep hL hg⟩
  rw [← selfConvolution_zero_eq,
    Cvs.Finite.OddSectorSineSums.selfConvolution_sineSum_zero hL hinj hinv hmode hodd, hn]

omit [DecidableEq ι] in
theorem sineSum_reflect_ae (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) :
    (fun x => Cvs.Finite.OddSectorSineSums.sineSum L mode o (L - x))
      =ᵐ[(volume : Measure ℝ)] fun x => -Cvs.Finite.OddSectorSineSums.sineSum L mode o x := by
  have := reflect_ae_of_window (f := Cvs.Finite.OddSectorSineSums.sineSum L mode o) (-1)
    (fun s hs => Cvs.Finite.OddSectorSineSums.sineSum_eq_zero_of_notMem L mode o hs)
    (fun y hy => by rw [Cvs.Finite.OddSectorSineSums.sineSum_reflect L mode o hy]; ring)
  simpa only [neg_one_mul] using this

/-! ### Reflection on the form domain: the odd classes -/

/-- **The reflection of the class of an odd window function is minus the class.** -/
theorem reflD_toDomain_odd {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L)
    (hodd : (fun x => f (L - x)) =ᵐ[(volume : Measure ℝ)] fun x => -f x) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (Cvs.Limit.ModeSumsToMinimiser.toDomain hL hf)
      = -Cvs.Limit.ModeSumsToMinimiser.toDomain hL hf := by
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (Cvs.Limit.ModeSumsToMinimiser.toWindow hf)
  have h2 := (MeasureTheory.Measure.measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
    (Cvs.Limit.ModeSumsToMinimiser.rep_toWindow_ae hf)
  have hneg : ⇑(((-(Cvs.Limit.ModeSumsToMinimiser.toDomain hL hf) : Cvs.WeilForm.FormDomain.formDomain hL)
      : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun x => -f x := by
    have hc : (((-(Cvs.Limit.ModeSumsToMinimiser.toDomain hL hf) : Cvs.WeilForm.FormDomain.formDomain hL)
        : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        = -((Cvs.Limit.ModeSumsToMinimiser.toWindow hf : Cvs.WeilForm.WeilFormOnWindowL2.window L)
          : Lp ℝ 2 (volume : Measure ℝ)) := rfl
    rw [hc]
    filter_upwards [Lp.coeFn_neg ((Cvs.Limit.ModeSumsToMinimiser.toWindow hf : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      : Lp ℝ 2 (volume : Measure ℝ)), Cvs.WeilForm.WindowRepresentative.ae_eq_rep (Cvs.Limit.ModeSumsToMinimiser.toWindow hf),
      Cvs.Limit.ModeSumsToMinimiser.rep_toWindow_ae hf] with x hx hy hz
    have hy' : (⇑((Cvs.Limit.ModeSumsToMinimiser.toWindow hf : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        : Lp ℝ 2 (volume : Measure ℝ))) x
        = Cvs.WeilForm.WindowRepresentative.rep (Cvs.Limit.ModeSumsToMinimiser.toWindow hf) x := hy
    rw [hx, Pi.neg_apply, hy', hz]
  calc ⇑((Cvs.WeilForm.WindowReflectionSymmetry.reflW (Cvs.Limit.ModeSumsToMinimiser.toWindow hf) : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (Cvs.Limit.ModeSumsToMinimiser.toWindow hf)) :=
        Cvs.WeilForm.WindowRepresentative.ae_eq_rep _
    _ =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep (Cvs.Limit.ModeSumsToMinimiser.toWindow hf) (L - x) := h1
    _ =ᵐ[volume] fun x => f (L - x) := h2
    _ =ᵐ[volume] fun x => -f x := hodd
    _ =ᵐ[volume] _ := hneg.symm

/-- The reflection is additive on the form domain. -/
theorem reflD_sub {L : ℝ} (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (φ - ψ)
      = Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ - Cvs.WeilForm.WindowReflectionSymmetry.reflD hL ψ := by
  apply Subtype.ext; apply Subtype.ext
  exact Cvs.WeilForm.WindowReflectionSymmetry.refl_sub L _ _

/-- **An even class is orthogonal to an odd class.** -/
theorem inner_eq_zero_of_even_odd {L : ℝ} (hL : 0 ≤ L) {η v : Cvs.WeilForm.FormDomain.formDomain hL}
    (hη : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL η = η) (hv : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL v = -v) :
    (inner ℝ η v : ℝ) = 0 := by
  have h1 : ‖η + v‖ = ‖η - v‖ := by
    rw [← Cvs.WeilForm.WindowReflectionSymmetry.norm_reflD hL (η - v), reflD_sub, hη, hv]
    exact congrArg norm (sub_neg_eq_add η v).symm
  have h2 := norm_add_sq_real η v
  have h3 := norm_sub_sq_real η v
  rw [h1] at h2
  linarith

end Cvs.Finite.ModeSumFormDomain
