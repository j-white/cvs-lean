import Mathlib
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.ProlateFamilySpine
import Cvs.WeilForm.TailBridgeCOneWindow
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.EWindowReciprocalContraction
import Cvs.Xi.MobiusReconstruction
import Cvs.Xi.ReciprocalWindowPhysicalL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The actual Möbius inverse on physical L²

The interval cut of the finite Möbius profile is a bounded physical L² map
and gives a right inverse of the reciprocal window on its support space.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped ArithmeticFunction.Moebius

namespace Cvs.Xi.MobiusInversePhysicalL2
open Cvs.ZeroCounting

open Cvs.Xi.ReciprocalWindowPhysicalL2 (Physical intervalSpace windowOp)
open Cvs.Xi.EWindowReciprocalContraction (branch)
open Cvs.Xi.EImageWindowPoisson (window)

/-- The fixed finite Möbius profile restricted to the physical window. -/
def cutProfile (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  (Icc a 1).indicator (Cvs.WeilForm.TailBridgeCOneWindow.profM a F)

/-- A cut reciprocal branch in the fixed Möbius sum. -/
def profileTerm (a : ℝ) (m : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  (Icc a 1).indicator (fun u => (μ m : ℝ) / a * branch (a / m) 1 F u)

/-- Each Möbius summand is its actual reciprocal branch on the window. -/
theorem profileTerm_eq {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m)
    (F : ℝ → ℝ) :
    profileTerm a m F = (Icc a 1).indicator
      (fun u => (μ m : ℝ) * (F (a / (m * u)) / (m * u))) := by
  funext u
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  by_cases hu : u ∈ Icc a 1
  · have hu0 : 0 < u := ha.trans_le hu.1
    have hb : u ∈ Icc (a / m) 1 :=
      ⟨(div_le_self ha.le hm1).trans hu.1, hu.2⟩
    simp only [profileTerm, indicator_of_mem hu, branch, Nat.cast_one, one_mul,
      indicator_of_mem hb]
    rw [show a / m / u = a / ((m : ℝ) * u) by field_simp]
    field_simp
  · simp only [profileTerm, indicator_of_notMem hu]

/-- The cut Möbius profile is the finite sum of its reciprocal branches. -/
theorem cutProfile_eq_sum {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    cutProfile a F = fun u => ∑ m ∈ Finset.Icc 1 ⌊1 / a⌋₊, profileTerm a m F u := by
  funext u
  unfold cutProfile Cvs.WeilForm.TailBridgeCOneWindow.profM
  have he := Finset.sum_congr (s₁ := Finset.Icc 1 ⌊1 / a⌋₊) rfl
    (fun m hm => congrFun (profileTerm_eq ha (Finset.mem_Icc.mp hm).1 F) u)
  rw [he]
  by_cases hu : u ∈ Icc a 1 <;> simp [hu]

/-- Every actual Möbius branch preserves physical square integrability. -/
theorem memLp_profileTerm {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m)
    {F : ℝ → ℝ} (hF : MemLp F 2 volume) : MemLp (profileTerm a m F) 2 volume := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  exact ((Cvs.Xi.ReciprocalWindowPhysicalL2.memLp_branch (div_pos ha hm0) (by omega : 1 ≤ 1) hF).const_mul
    ((μ m : ℝ) / a)).indicator measurableSet_Icc.nullMeasurableSet

/-- The actual cut Möbius profile preserves physical square integrability. -/
theorem memLp_cutProfile {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    MemLp (cutProfile a F) 2 volume := by
  rw [cutProfile_eq_sum ha]
  exact memLp_finsetSum _ fun m hm => memLp_profileTerm ha (Finset.mem_Icc.mp hm).1 hF

/-- The finite Möbius branches respect physical almost-everywhere equality. -/
theorem profileTerm_congr_ae {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m)
    {F G : ℝ → ℝ} (hFG : F =ᵐ[volume] G) :
    profileTerm a m F =ᵐ[volume] profileTerm a m G := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have he := Cvs.Xi.ReciprocalWindowPhysicalL2.branch_congr_ae (div_pos ha hm0) (by omega : 1 ≤ 1) hFG
  filter_upwards [he] with u hu
  by_cases hmem : u ∈ Icc a 1 <;> simp [profileTerm, hmem, hu]

/-- The actual finite Möbius profile respects physical almost-everywhere equality. -/
theorem cutProfile_congr_ae {a : ℝ} (ha : 0 < a) {F G : ℝ → ℝ}
    (hFG : F =ᵐ[volume] G) : cutProfile a F =ᵐ[volume] cutProfile a G := by
  rw [cutProfile_eq_sum ha, cutProfile_eq_sum ha]
  have he := (eventually_all_finset (Finset.Icc 1 ⌊1 / a⌋₊)).mpr
    (fun m hm => profileTerm_congr_ae ha (Finset.mem_Icc.mp hm).1 hFG)
  filter_upwards [he] with u hu
  exact Finset.sum_congr rfl hu

/-- The cut Möbius profile reconstructs every exactly interval-supported function. -/
theorem window_cutProfile {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hsupp : ∀ u ∉ Icc a 1, F u = 0) : window a (cutProfile a F) = F := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · rw [window, indicator_of_mem hθ]
    rw [Cvs.WeilForm.TailBridgeCOneWindow.eimage_congr_Icc ha (H := Cvs.Xi.MobiusReconstruction.mobiusProfile a F) (fun u hu => by
      rw [cutProfile, indicator_of_mem hu, Cvs.WeilForm.TailBridgeCOneWindow.profM_eq_mobius ha hsupp hu.1 hu.2]) hθ.2]
    exact Cvs.Xi.MobiusReconstruction.eimage_mobiusProfile ha hθ.1 hθ.2 F
  · rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ, hsupp θ hθ]

/-- The constructed finite Möbius inverse budget. -/
def profileBudget (a : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊1 / a⌋₊, |(μ m : ℝ) / a| * √(a / m)

private theorem norm_toLp_sq {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    ‖hF.toLp F‖ ^ 2 = ∫ u, F u ^ 2 := by
  rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
  exact integral_congr_ae (by filter_upwards [hF.coeFn_toLp] with u hu; rw [hu])

/-- Every inverse branch has the norm factor supplied by its reciprocal Jacobian. -/
theorem norm_profileTerm_toLp_le {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m)
    {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    ‖(memLp_profileTerm ha hm hF).toLp (profileTerm a m F)‖
      ≤ (|(μ m : ℝ) / a| * √(a / m)) * ‖hF.toLp F‖ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hb := Cvs.Xi.ReciprocalWindowPhysicalL2.memLp_branch (div_pos ha hm0) (by omega : 1 ≤ 1) hF
  have hpoint : ∀ u, profileTerm a m F u ^ 2
      ≤ ((μ m : ℝ) / a) ^ 2 * branch (a / m) 1 F u ^ 2 := by
    intro u
    by_cases hu : u ∈ Icc a 1
    · simp [profileTerm, hu, mul_pow]
    · simp only [profileTerm, indicator_of_notMem hu, zero_pow (by omega : 2 ≠ 0)]
      positivity
  have hi : ∫ u, profileTerm a m F u ^ 2
      ≤ ((μ m : ℝ) / a) ^ 2 * (a / m) * ∫ u, F u ^ 2 := by
    calc
      _ ≤ ∫ u, ((μ m : ℝ) / a) ^ 2 * branch (a / m) 1 F u ^ 2 :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          (hb.integrable_sq.const_mul _) (ae_of_all _ hpoint)
      _ = ((μ m : ℝ) / a) ^ 2 * (a / m) *
          ∫ u in Icc (a / m) 1, F u ^ 2 := by
        rw [integral_const_mul, Cvs.Xi.ReciprocalWindowPhysicalL2.integral_branch_sq (div_pos ha hm0) (by omega : 1 ≤ 1)]
        simp only [Nat.cast_one, div_one, one_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun _ => sq_nonneg _) hF.integrable_sq) (by positivity)
  have hsq : ‖(memLp_profileTerm ha hm hF).toLp (profileTerm a m F)‖ ^ 2
      ≤ ((|(μ m : ℝ) / a| * √(a / m)) * ‖hF.toLp F‖) ^ 2 := by
    rw [norm_toLp_sq, mul_pow, mul_pow, sq_abs, Real.sq_sqrt (by positivity), norm_toLp_sq]
    exact hi
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

private theorem memLp_profileTerm_all {a : ℝ} (ha : 0 < a) (m : ℕ)
    {F : ℝ → ℝ} (hF : MemLp F 2 volume) : MemLp (profileTerm a m F) 2 volume := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have he : profileTerm a 0 F = 0 := by funext u; simp [profileTerm]
    rw [he]
    exact MemLp.zero
  · exact memLp_profileTerm ha hm hF

private def termClass {a : ℝ} (ha : 0 < a) (m : ℕ) (F : Physical) : Physical :=
  (memLp_profileTerm_all ha m (Lp.memLp F)).toLp (profileTerm a m F)

/-- The actual cut Möbius profile as a physical linear map. -/
def profileLinear {a : ℝ} (ha : 0 < a) : Physical →ₗ[ℝ] Physical where
  toFun F := (memLp_cutProfile ha (Lp.memLp F)).toLp (cutProfile a F)
  map_add' F G := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine (cutProfile_congr_ae ha (Lp.coeFn_add F G)).trans (ae_of_all _ fun u => ?_)
    by_cases hu : u ∈ Icc a 1
    · simp only [cutProfile, indicator_of_mem hu, Cvs.WeilForm.TailBridgeCOneWindow.profM, Pi.add_apply,
        add_div, mul_add, Finset.sum_add_distrib]
    · simp [cutProfile, hu]
  map_smul' r F := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    refine (cutProfile_congr_ae ha (Lp.coeFn_smul r F)).trans (ae_of_all _ fun u => ?_)
    by_cases hu : u ∈ Icc a 1
    · simp only [cutProfile, indicator_of_mem hu, Cvs.WeilForm.TailBridgeCOneWindow.profM, Pi.smul_apply,
        smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    · simp [cutProfile, hu]

theorem coe_profileLinear_ae {a : ℝ} (ha : 0 < a) (F : Physical) :
    (profileLinear ha F : ℝ → ℝ) =ᵐ[volume] cutProfile a F :=
  (memLp_cutProfile ha (Lp.memLp F)).coeFn_toLp

private theorem profileLinear_eq_sum {a : ℝ} (ha : 0 < a) (F : Physical) :
    profileLinear ha F = ∑ m ∈ Finset.Icc 1 ⌊1 / a⌋₊, termClass ha m F := by
  apply Lp.ext
  have hs := Lp.coeFn_finsetSum (Finset.Icc 1 ⌊1 / a⌋₊) (fun m => termClass ha m F)
  have he := (eventually_all_finset (Finset.Icc 1 ⌊1 / a⌋₊)).mpr
    (fun m _ => (memLp_profileTerm_all ha m (Lp.memLp F)).coeFn_toLp)
  filter_upwards [coe_profileLinear_ae ha F, hs, he] with u hF hs he
  rw [hF, hs, cutProfile_eq_sum ha]
  simpa only [Finset.sum_apply, termClass] using
    (Finset.sum_congr rfl fun m hm => (he m hm).symm)

/-- The actual finite Möbius inverse has its constructed physical norm bound. -/
theorem norm_profileLinear_le {a : ℝ} (ha : 0 < a) (F : Physical) :
    ‖profileLinear ha F‖ ≤ profileBudget a * ‖F‖ := by
  rw [profileLinear_eq_sum ha]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊1 / a⌋₊, ‖termClass ha m F‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊1 / a⌋₊, (|(μ m : ℝ) / a| * √(a / m)) * ‖F‖ := by
      apply Finset.sum_le_sum
      intro m hm
      simpa only [termClass, Lp.toLp_coeFn] using
        norm_profileTerm_toLp_le ha (Finset.mem_Icc.mp hm).1 (Lp.memLp F)
    _ = _ := by rw [profileBudget, Finset.sum_mul]

/-- The actual cut Möbius inverse as a bounded physical operator. -/
def profileOp {a : ℝ} (ha : 0 < a) : Physical →L[ℝ] Physical :=
  (profileLinear ha).mkContinuous (profileBudget a) (norm_profileLinear_le ha)

theorem coe_profileOp_ae {a : ℝ} (ha : 0 < a) (F : Physical) :
    (profileOp ha F : ℝ → ℝ) =ᵐ[volume] cutProfile a F := coe_profileLinear_ae ha F

/-- The actual Möbius operator is a right inverse on the physical support space. -/
theorem windowOp_profileOp {a : ℝ} (ha : 0 < a) (F : Physical)
    (hF : F ∈ intervalSpace a) : windowOp ha (profileOp ha F) = F := by
  let Fc : ℝ → ℝ := (Icc a 1).indicator (F : ℝ → ℝ)
  have hcut : (F : ℝ → ℝ) =ᵐ[volume] Fc := by
    filter_upwards [hF] with u hu
    by_cases hmem : u ∈ Icc a 1
    · simp [Fc, hmem]
    · simp [Fc, hmem, hu hmem]
  have hsupp : ∀ u ∉ Icc a 1, Fc u = 0 := fun u hu => indicator_of_notMem hu _
  have hinv : window a (cutProfile a Fc) =ᵐ[volume] Fc :=
    ae_of_all _ fun u => congrFun (window_cutProfile ha hsupp) u
  apply Lp.ext
  exact (Cvs.Xi.ReciprocalWindowPhysicalL2.coe_windowOp_ae ha (profileOp ha F)).trans
    ((Cvs.Xi.ReciprocalWindowPhysicalL2.window_congr_ae ha (coe_profileOp_ae ha F)).trans
      ((Cvs.Xi.ReciprocalWindowPhysicalL2.window_congr_ae ha (cutProfile_congr_ae ha hcut)).trans
        (hinv.trans hcut.symm)))

end Cvs.Xi.MobiusInversePhysicalL2
