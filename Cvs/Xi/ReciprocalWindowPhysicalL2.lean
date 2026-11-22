import Mathlib
import Cvs.L2a.PlaneCorrelationL2
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.EWindowReciprocalContraction
import Cvs.Xi.ReciprocalBranchSelfAdjoint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The reciprocal window on physical L²

The actual finite reciprocal window defines a selfadjoint contraction on physical
Lebesgue L², with range supported on its integration interval.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace

namespace Cvs.Xi.ReciprocalWindowPhysicalL2
open Cvs.ZeroCounting

open Cvs.Xi.EWindowReciprocalContraction (branch)
open Cvs.Xi.EImageWindowPoisson (window)

/-- Physical Lebesgue `L²`. -/
abbrev Physical := Lp ℝ 2 (volume : Measure ℝ)

private theorem recip_data {b : ℝ} (hb : 0 < b) :
    (∀ θ ∈ Icc b 1, HasDerivWithinAt (fun θ => b / θ) (-b / θ ^ 2) (Icc b 1) θ)
      ∧ InjOn (fun θ => b / θ) (Icc b 1) := by
  constructor
  · simpa only [Nat.cast_one, one_mul] using Cvs.Xi.EImageWindowPoisson.hasDerivWithinAt_recip hb 1
  · simpa only [Nat.cast_one, one_mul] using Cvs.Xi.EImageWindowPoisson.injOn_recip hb (n := 1) (by omega)

/-- A reciprocal branch respects physical almost-everywhere equality. -/
theorem branch_congr_ae {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    {G H : ℝ → ℝ} (hGH : G =ᵐ[volume] H) : branch a n G =ᵐ[volume] branch a n H := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : 0 < (n : ℝ) * a := by positivity
  rw [EventuallyEq, ae_iff] at hGH ⊢
  let S := {u : ℝ | ¬G u = H u} ∩ Icc ((n : ℝ) * a) 1
  have hdiff : DifferentiableOn ℝ (fun u => (n : ℝ) * a / u) S := by
    intro u hu
    exact ((differentiableAt_const ((n : ℝ) * a)).div differentiableAt_id
      (hb.trans_le hu.2.1).ne').differentiableWithinAt
  have hnull : volume ((fun u => (n : ℝ) * a / u) '' S) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff
      (measure_mono_null inter_subset_left hGH)
  refine measure_mono_null (t := (fun u => (n : ℝ) * a / u) '' S) ?_ hnull
  intro θ hθ
  by_cases hmem : θ ∈ Icc ((n : ℝ) * a) 1
  · have hθ0 : 0 < θ := hb.trans_le hmem.1
    have hrec : (n : ℝ) * a / θ ∈ Icc ((n : ℝ) * a) 1 := by
      refine ⟨(le_div_iff₀ hθ0).mpr ?_, (div_le_one hθ0).mpr hmem.1⟩
      nlinarith [hmem.2]
    refine ⟨(n : ℝ) * a / θ, ⟨?_, hrec⟩, ?_⟩
    · intro he
      apply hθ
      simp only [branch, indicator_of_mem hmem, he]
    · field_simp
  · exact False.elim (hθ (by simp [branch, indicator_of_notMem hmem]))

/-- The actual window respects physical almost-everywhere equality. -/
theorem window_congr_ae {a : ℝ} (ha : 0 < a) {G H : ℝ → ℝ} (hGH : G =ᵐ[volume] H) :
    window a G =ᵐ[volume] window a H := by
  rw [Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha, Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha]
  have h := (eventually_all_finset (Finset.Icc 1 ⌊1 / a⌋₊)).mpr
    (fun n hn => branch_congr_ae ha (Finset.mem_Icc.mp hn).1 hGH)
  filter_upwards [h] with θ hθ
  exact Finset.sum_congr rfl hθ

/-- A reciprocal branch of an interval-integrable profile is integrable. -/
theorem integrable_branch_of_integrableOn {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    {G : ℝ → ℝ} (hG : IntegrableOn G (Icc ((n : ℝ) * a) 1)) :
    Integrable (branch a n G) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : 0 < (n : ℝ) * a := by positivity
  have hw : IntegrableOn (fun u => a / u * G u) (Icc ((n : ℝ) * a) 1) :=
    hG.continuousOn_mul (continuousOn_const.div continuousOn_id
      (fun u hu => (hb.trans_le hu.1).ne')) isCompact_Icc
  have hchange := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (recip_data hb).1 (recip_data hb).2 (fun u => a / u * G u))
  rw [Cvs.Xi.EWindowReciprocalContraction.image_recip_Icc hb] at hchange
  have hi := hchange.mp hw
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  refine hi.congr (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
  have hθ0 : 0 < θ := hb.trans_le hθ.1
  simp only [smul_eq_mul]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
  field_simp

/-- The square integral of a reciprocal branch has its exact projection coefficient. -/
theorem integral_branch_sq {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) (G : ℝ → ℝ) :
    ∫ θ, branch a n G θ ^ 2 = a / n * ∫ u in Icc ((n : ℝ) * a) 1, G u ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : 0 < (n : ℝ) * a := by positivity
  rw [show (fun θ => branch a n G θ ^ 2) =
    (Icc ((n : ℝ) * a) 1).indicator (fun θ => (a / θ * G ((n : ℝ) * a / θ)) ^ 2) by
      funext θ
      simp only [branch, indicator_apply]
      split_ifs <;> simp,
    integral_indicator measurableSet_Icc, ← integral_const_mul]
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (recip_data hb).1 (recip_data hb).2 (fun u => a / n * G u ^ 2)
  rw [Cvs.Xi.EWindowReciprocalContraction.image_recip_Icc hb] at hchange
  rw [hchange]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  have hθ0 : 0 < θ := hb.trans_le hθ.1
  simp only [smul_eq_mul]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
  field_simp

/-- Every reciprocal branch of a physical square-integrable profile is square-integrable. -/
theorem memLp_branch {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    {G : ℝ → ℝ} (hG : MemLp G 2 (volume : Measure ℝ)) : MemLp (branch a n G) 2 volume := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : 0 < (n : ℝ) * a := by positivity
  have hi : Integrable (branch a n G) := integrable_branch_of_integrableOn ha hn
    (MemLp.integrable (by norm_num) (hG.restrict _))
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (recip_data hb).1 (recip_data hb).2 (fun u => a / n * G u ^ 2)
  rw [Cvs.Xi.EWindowReciprocalContraction.image_recip_Icc hb] at hchange
  have hs := hchange.mp ((hG.integrable_sq.const_mul (a / n)).restrict)
  rw [show (fun θ => branch a n G θ ^ 2) =
    (Icc ((n : ℝ) * a) 1).indicator (fun θ => (a / θ * G ((n : ℝ) * a / θ)) ^ 2) by
      funext θ
      simp only [branch, indicator_apply]
      split_ifs <;> simp]
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  refine hs.congr (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
  have hθ0 : 0 < θ := hb.trans_le hθ.1
  simp only [smul_eq_mul]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
  field_simp

/-- The actual reciprocal window preserves physical square integrability. -/
theorem memLp_window {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hG : MemLp G 2 volume) :
    MemLp (window a G) 2 volume := by
  rw [Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha]
  exact memLp_finsetSum _ (fun n hn => memLp_branch ha (Finset.mem_Icc.mp hn).1 hG)

/-- The finite reciprocal window preserves physical integrability. -/
theorem integrable_window {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hG : Integrable G) :
    Integrable (window a G) := by
  rw [Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha]
  exact integrable_finsetSum _ fun n hn =>
    integrable_branch_of_integrableOn ha (Finset.mem_Icc.mp hn).1 hG.restrict

private theorem integrable_mul_branch_one {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    {G : ℝ → ℝ} (hG : Integrable G) : Integrable (fun u => G u * branch a n (fun _ => 1) u) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : 0 < (n : ℝ) * a := by positivity
  rw [show (fun u => G u * branch a n (fun _ => 1) u) =
    (Icc ((n : ℝ) * a) 1).indicator (fun u => G u * (a / u)) by
      funext u
      simp [branch, indicator_apply]]
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  have hGr : IntegrableOn G (Icc ((n : ℝ) * a) 1) := hG.restrict
  exact hGr.mul_continuousOn (continuousOn_const.div continuousOn_id
    (fun u hu => (hb.trans_le hu.1).ne')) isCompact_Icc

/-- Integrating the actual reciprocal window transposes its row mass for every integrable profile. -/
theorem integral_window_eq_row_mass {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hG : Integrable G) :
    ∫ θ, window a G θ = ∫ u, G u * window a (fun _ => 1) u := by
  rw [Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha G, Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha (fun _ => 1)]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun n hn =>
    integrable_branch_of_integrableOn ha (Finset.mem_Icc.mp hn).1 hG.restrict),
    integral_finsetSum _ (fun n hn => integrable_mul_branch_one ha (Finset.mem_Icc.mp hn).1 hG)]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [mul_one] using Cvs.Xi.ReciprocalBranchSelfAdjoint.integral_branch_mul ha (Finset.mem_Icc.mp hn).1 G (fun _ => 1)

/-- Every physical square-integrable profile obeys the exact interval contraction bound. -/
theorem integral_window_sq_le_cut {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hG : MemLp G 2 volume) :
    ∫ θ, window a G θ ^ 2 ≤ ∫ u in Icc a 1, G u ^ 2 := by
  have hi := integrable_window ha hG.integrable_sq
  have he : ∫ u, G u ^ 2 * window a (fun _ => 1) u =
      ∫ u in Icc a 1, G u ^ 2 * window a (fun _ => 1) u := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hu, mul_zero]
  calc
    ∫ θ, window a G θ ^ 2 ≤ ∫ θ, window a (fun u => G u ^ 2) θ :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hi
        (ae_of_all _ fun θ => Cvs.Xi.EWindowReciprocalContraction.window_sq_le_window_sq ha G θ)
    _ = ∫ u in Icc a 1, G u ^ 2 * window a (fun _ => 1) u := by
      rw [integral_window_eq_row_mass ha hG.integrable_sq, he]
    _ ≤ ∫ u in Icc a 1, G u ^ 2 := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun u => mul_nonneg (sq_nonneg _) (Cvs.Xi.EWindowReciprocalContraction.window_one_mem_Icc ha u).1)
        hG.integrable_sq.restrict
      exact ae_of_all _ fun u => mul_le_of_le_one_right (sq_nonneg _)
        (Cvs.Xi.EWindowReciprocalContraction.window_one_mem_Icc ha u).2

/-- The actual window's physical pairing is symmetric for every two square-integrable profiles. -/
theorem integral_window_mul {a : ℝ} (ha : 0 < a) {G H : ℝ → ℝ}
    (hG : MemLp G 2 volume) (hH : MemLp H 2 volume) :
    ∫ θ, window a G θ * H θ = ∫ θ, G θ * window a H θ := by
  rw [Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha G, Cvs.Xi.EWindowReciprocalContraction.window_eq_sum_branch ha H]
  simp only [Finset.sum_mul, Finset.mul_sum]
  have hleft : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊,
      Integrable (fun θ => branch a n G θ * H θ) :=
    fun n hn => (memLp_branch ha (Finset.mem_Icc.mp hn).1 hG).integrable_mul hH
  have hright : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊,
      Integrable (fun θ => G θ * branch a n H θ) :=
    fun n hn => hG.integrable_mul (memLp_branch ha (Finset.mem_Icc.mp hn).1 hH)
  rw [integral_finsetSum _ hleft, integral_finsetSum _ hright]
  exact Finset.sum_congr rfl fun n hn => Cvs.Xi.ReciprocalBranchSelfAdjoint.integral_branch_mul ha (Finset.mem_Icc.mp hn).1 G H

/-- The actual reciprocal window as a linear map on physical `L²`. -/
def windowLinear {a : ℝ} (ha : 0 < a) : Physical →ₗ[ℝ] Physical where
  toFun G := (memLp_window ha (Lp.memLp G)).toLp (window a G)
  map_add' G H := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine (window_congr_ae ha (Lp.coeFn_add G H)).trans (ae_of_all _ fun θ => ?_)
    simp only [Pi.add_apply, window, indicator_apply]
    split_ifs
    · exact congrFun (Cvs.Xi.EImageWindowPoisson.eimage_add a (G : ℝ → ℝ) (H : ℝ → ℝ)) θ
    · simp
  map_smul' r G := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have h := window_congr_ae ha (Lp.coeFn_smul r G)
    refine h.trans (ae_of_all _ fun θ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, window, indicator_apply]
    split_ifs
    · exact congrFun (Cvs.Xi.EImageWindowPoisson.eimage_smul a r (G : ℝ → ℝ)) θ
    · simp

theorem coe_windowLinear_ae {a : ℝ} (ha : 0 < a) (G : Physical) :
    (windowLinear ha G : ℝ → ℝ) =ᵐ[volume] window a G :=
  (memLp_window ha (Lp.memLp G)).coeFn_toLp

/-- The actual linear window is a contraction in the physical norm. -/
theorem norm_windowLinear_le {a : ℝ} (ha : 0 < a) (G : Physical) :
    ‖windowLinear ha G‖ ≤ ‖G‖ := by
  have hsq : ‖windowLinear ha G‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
    calc
      ∫ θ, (windowLinear ha G θ) ^ 2 = ∫ θ, window a G θ ^ 2 :=
        integral_congr_ae (by filter_upwards [coe_windowLinear_ae ha G] with θ hθ; rw [hθ])
      _ ≤ ∫ θ in Icc a 1, G θ ^ 2 := integral_window_sq_le_cut ha (Lp.memLp G)
      _ ≤ ∫ θ, G θ ^ 2 := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun _ => sq_nonneg _) (Lp.memLp G).integrable_sq
  nlinarith [norm_nonneg G, norm_nonneg (windowLinear ha G)]

/-- The actual reciprocal window as a bounded physical `L²` operator. -/
def windowOp {a : ℝ} (ha : 0 < a) : Physical →L[ℝ] Physical :=
  (windowLinear ha).mkContinuous 1 (fun G => by simpa using norm_windowLinear_le ha G)

theorem coe_windowOp_ae {a : ℝ} (ha : 0 < a) (G : Physical) :
    (windowOp ha G : ℝ → ℝ) =ᵐ[volume] window a G := coe_windowLinear_ae ha G

/-- The physical reciprocal window operator is selfadjoint. -/
theorem inner_windowOp {a : ℝ} (ha : 0 < a) (G H : Physical) :
    ⟪windowOp ha G, H⟫_ℝ = ⟪G, windowOp ha H⟫_ℝ := by
  rw [Cvs.L2a.PlaneCorrelationL2.inner_eq_integral, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
  calc
    ∫ θ, windowOp ha G θ * H θ = ∫ θ, window a G θ * H θ :=
      integral_congr_ae ((coe_windowOp_ae ha G).mul (EventuallyEq.rfl))
    _ = ∫ θ, G θ * window a H θ := integral_window_mul ha (Lp.memLp G) (Lp.memLp H)
    _ = ∫ θ, G θ * windowOp ha H θ :=
      integral_congr_ae ((EventuallyEq.rfl).mul (coe_windowOp_ae ha H).symm)

/-- Physical `L²` classes supported on the reciprocal window interval. -/
def intervalSpace (a : ℝ) : Submodule ℝ Physical where
  carrier := {G | ∀ᵐ θ ∂volume, θ ∉ Icc a 1 → (G : ℝ → ℝ) θ = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure ℝ))] with θ hθ _
    rw [hθ]
    rfl
  add_mem' := by
    intro G H hG hH
    filter_upwards [hG, hH, Lp.coeFn_add G H] with θ hGθ hHθ hadd hθ
    rw [hadd]
    simp [hGθ hθ, hHθ hθ]
  smul_mem' := by
    intro r G hG
    filter_upwards [hG, Lp.coeFn_smul r G] with θ hGθ hsmul hθ
    rw [hsmul]
    simp [hGθ hθ]

end Cvs.Xi.ReciprocalWindowPhysicalL2
