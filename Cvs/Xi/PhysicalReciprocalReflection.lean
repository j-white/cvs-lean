import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.ConnesWindowCosineComplete
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.CompressedPhysicalPrimeForm
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.EWindowReciprocalContraction
import Cvs.Xi.MangoldtDilationEWindow
import Cvs.Xi.ReciprocalBranchSelfAdjoint
import Cvs.Xi.ReciprocalWindowPhysicalL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Physical reciprocal reflection and the actual even profile

The normalized first reciprocal branch is an interval involution, and
its actual even average has zero centered-logarithm moment.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.Xi.PhysicalReciprocalReflection
open Cvs.ZeroCounting

open Cvs.Xi.MangoldtDilationEWindow (centeredLog)
open Cvs.Xi.EWindowReciprocalContraction (branch)

/-- The physical reciprocal reflection, normalized by its square coefficient. -/
def reciprocal (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun θ => branch a 1 F θ / √a

/-- The physical interval projection. -/
def cut (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := (Icc a 1).indicator F

/-- The actual physical reflection-even average. -/
def evenPhysical (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (cut a F θ + reciprocal a F θ) / 2

theorem reciprocal_of_notMem {a θ : ℝ} (hθ : θ ∉ Icc a 1) (F : ℝ → ℝ) :
    reciprocal a F θ = 0 := by
  simp [reciprocal, branch, indicator_of_notMem hθ]

/-- Reciprocal sampling preserves the physical interval. -/
theorem recip_mem_Icc {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1) :
    a / θ ∈ Icc a 1 := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  refine ⟨(le_div_iff₀ hθ0).mpr ?_, (div_le_one hθ0).mpr hθ.1⟩
  nlinarith [hθ.2]

/-- The normalized branch has the usual physical reciprocal Jacobian factor. -/
theorem reciprocal_apply {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1) (F : ℝ → ℝ) :
    reciprocal a F θ = √a / θ * F (a / θ) := by
  have hs : 0 < √a := sqrt_pos.mpr ha
  simp only [reciprocal, branch, Nat.cast_one, one_mul, indicator_of_mem hθ]
  have hc : a / θ / √a = √a / θ := by
    rw [div_right_comm]
    congr 1
    exact (div_eq_iff hs.ne').mpr (Real.mul_self_sqrt ha.le).symm
  calc
    a / θ * F (a / θ) / √a = (a / θ / √a) * F (a / θ) := by ring
    _ = _ := by rw [hc]

/-- The reciprocal reflection is an involution on the cut-supported functions. -/
theorem reciprocal_sq {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    reciprocal a (reciprocal a F) = cut a F := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    rw [reciprocal_apply ha hθ, reciprocal_apply ha (recip_mem_Icc ha hθ),
      cut, indicator_of_mem hθ, show a / (a / θ) = θ by field_simp]
    field_simp
    rw [Real.sq_sqrt ha.le]
  · rw [reciprocal_of_notMem hθ, cut, indicator_of_notMem hθ]

/-- Cutting a profile before reciprocal reflection does not change its image. -/
theorem reciprocal_cut {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    reciprocal a (cut a F) = reciprocal a F := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · rw [reciprocal_apply ha hθ, reciprocal_apply ha hθ, cut,
      indicator_of_mem (recip_mem_Icc ha hθ)]
  · rw [reciprocal_of_notMem hθ, reciprocal_of_notMem hθ]

theorem reciprocal_add (a : ℝ) (F G : ℝ → ℝ) :
    reciprocal a (fun θ => F θ + G θ) = fun θ => reciprocal a F θ + reciprocal a G θ := by
  funext θ
  simp only [reciprocal, branch, indicator_apply]
  split_ifs <;> ring

theorem reciprocal_smul (a r : ℝ) (F : ℝ → ℝ) :
    reciprocal a (fun θ => r * F θ) = fun θ => r * reciprocal a F θ := by
  funext θ
  simp only [reciprocal, branch, indicator_apply]
  split_ifs <;> ring

/-- The actual average is exactly reciprocal-even. -/
theorem reciprocal_evenPhysical {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    reciprocal a (evenPhysical a F) = evenPhysical a F := by
  have he : evenPhysical a F = fun θ => (1 / 2 : ℝ) * (cut a F θ + reciprocal a F θ) := by
    funext θ
    unfold evenPhysical
    ring
  rw [he, reciprocal_smul, reciprocal_add, reciprocal_cut ha, reciprocal_sq ha]
  funext θ
  ring

/-- The centered log changes sign under reciprocal reflection. -/
theorem reciprocal_centeredLog {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    reciprocal a (fun θ => centeredLog a θ * F θ)
      = fun θ => -(centeredLog a θ * reciprocal a F θ) := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    rw [reciprocal_apply ha hθ, reciprocal_apply ha hθ]
    unfold centeredLog
    rw [Real.log_div ha.ne' hθ0.ne']
    ring
  · simp only [reciprocal_of_notMem hθ, mul_zero, neg_zero]

/-- Reciprocal reflection is selfadjoint in the physical Lebesgue pairing. -/
theorem integral_reciprocal_mul {a : ℝ} (ha : 0 < a) (F G : ℝ → ℝ) :
    ∫ θ, reciprocal a F θ * G θ = ∫ θ, F θ * reciprocal a G θ := by
  have hl : (fun θ => reciprocal a F θ * G θ) =
      fun θ => (1 / √a) * (branch a 1 F θ * G θ) := by
    funext θ
    unfold reciprocal
    ring
  have hr : (fun θ => F θ * reciprocal a G θ) =
      fun θ => (1 / √a) * (F θ * branch a 1 G θ) := by
    funext θ
    unfold reciprocal
    ring
  rw [hl, hr, integral_const_mul, integral_const_mul, Cvs.Xi.ReciprocalBranchSelfAdjoint.integral_branch_mul ha (by omega)]

/-- The normalized reciprocal reflection preserves the physical cut-square norm. -/
theorem integral_reciprocal_sq {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    ∫ θ, reciprocal a F θ ^ 2 = ∫ θ in Icc a 1, F θ ^ 2 := by
  have he : (fun θ => reciprocal a F θ ^ 2) =
      fun θ => (1 / √a) ^ 2 * branch a 1 F θ ^ 2 := by
    funext θ
    unfold reciprocal
    ring
  rw [he, integral_const_mul, Cvs.Xi.ReciprocalWindowPhysicalL2.integral_branch_sq ha (by omega)]
  simp only [Nat.cast_one, one_mul, div_one]
  rw [one_div_pow, Real.sq_sqrt ha.le, ← mul_assoc, one_div_mul_cancel ha.ne', one_mul]

/-- The actual reciprocal reflection preserves physical square integrability. -/
theorem memLp_reciprocal {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    MemLp (reciprocal a F) 2 volume := by
  convert (Cvs.Xi.ReciprocalWindowPhysicalL2.memLp_branch ha (by omega : 1 ≤ 1) hF).const_mul (1 / √a) using 1
  funext θ
  unfold reciprocal
  ring

/-- The actual reflection-even average of a physical L² profile is again in L². -/
theorem memLp_evenPhysical {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    MemLp (evenPhysical a F) 2 volume := by
  have hc : MemLp (cut a F) 2 volume := hF.indicator measurableSet_Icc.nullMeasurableSet
  convert (hc.add (memLp_reciprocal ha hF)).const_mul (1 / 2 : ℝ) using 1
  funext θ
  change (cut a F θ + reciprocal a F θ) / 2 = (1 / 2) * (cut a F θ + reciprocal a F θ)
  ring

/-- The centered-log moment of the actual reciprocal-even average vanishes exactly. -/
theorem integral_centeredLog_evenPhysical_sq {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    ∫ θ, centeredLog a θ * evenPhysical a F θ ^ 2 = 0 := by
  have h := integral_reciprocal_mul ha
    (fun θ => centeredLog a θ * evenPhysical a F θ) (evenPhysical a F)
  rw [reciprocal_centeredLog ha, reciprocal_evenPhysical ha] at h
  have hl : (fun θ => -(centeredLog a θ * evenPhysical a F θ) * evenPhysical a F θ) =
      fun θ => -(centeredLog a θ * evenPhysical a F θ ^ 2) := by funext θ; ring
  have hr : (fun θ => (centeredLog a θ * evenPhysical a F θ) * evenPhysical a F θ) =
      fun θ => centeredLog a θ * evenPhysical a F θ ^ 2 := by funext θ; ring
  rw [hl, hr, integral_neg] at h
  linarith

/-- The actual even average has exact pointwise window support. -/
theorem evenPhysical_of_notMem {a θ : ℝ} (hθ : θ ∉ Icc a 1) (F : ℝ → ℝ) :
    evenPhysical a F θ = 0 := by
  rw [evenPhysical, cut, indicator_of_notMem hθ, reciprocal_of_notMem hθ]
  norm_num

/-- For physical L² input, the vanishing centered-log moment is an integrable moment. -/
theorem integrable_centeredLog_evenPhysical_sq {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    Integrable (fun θ => centeredLog a θ * evenPhysical a F θ ^ 2) := by
  have he : (fun θ => centeredLog a θ * evenPhysical a F θ ^ 2) =
      (Icc a 1).indicator (fun θ => centeredLog a θ * evenPhysical a F θ ^ 2) := by
    funext θ
    by_cases hθ : θ ∈ Icc a 1
    · rw [indicator_of_mem hθ]
    · rw [indicator_of_notMem hθ, evenPhysical_of_notMem hθ, zero_pow (by omega), mul_zero]
  rw [he]
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  have hc : ContinuousOn (centeredLog a) (Icc a 1) :=
    (Real.continuousOn_log.mono (fun θ (hθ : θ ∈ Icc a 1) => (ha.trans_le hθ.1).ne')).sub continuousOn_const
  have hi : IntegrableOn (fun θ => evenPhysical a F θ ^ 2) (Icc a 1) :=
    (memLp_evenPhysical ha hF).integrable_sq.restrict
  exact hi.continuousOn_mul hc isCompact_Icc

/-- Reciprocal membership is equivalent for every positive physical coordinate. -/
theorem recip_mem_Icc_iff {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) :
    a / θ ∈ Icc a 1 ↔ θ ∈ Icc a 1 := by
  constructor
  · intro h
    refine ⟨(div_le_one hθ).mp h.2, ?_⟩
    have hh := (le_div_iff₀ hθ).mp h.1
    nlinarith
  · exact recip_mem_Icc ha

/-- Reciprocal reflection is exactly reflection in the logarithmic coordinate. -/
theorem logScale_reciprocal {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ)
    (hF : ∀ θ ∉ Icc a 1, F θ = 0) (s : ℝ) :
    Cvs.L2a.TailLogScaleTest.logScale (reciprocal a F) s = Cvs.L2a.TailLogScaleTest.logScale F (Real.log a - s) := by
  have hexp : exp (Real.log a - s) = a / exp s := by rw [exp_sub, exp_log ha]
  have hsqrt : √a = exp (Real.log a / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha]
    congr 1
    ring
  have hcoeff : √a * exp (s / 2) / exp s = exp ((Real.log a - s) / 2) := by
    rw [hsqrt, ← exp_add, ← exp_sub]
    congr 1
    ring
  unfold Cvs.L2a.TailLogScaleTest.logScale
  rw [hexp]
  by_cases hθ : exp s ∈ Icc a 1
  · rw [reciprocal_apply ha hθ]
    calc
      (√a / exp s * F (a / exp s)) * exp (s / 2)
        = F (a / exp s) * (√a * exp (s / 2) / exp s) := by ring
      _ = _ := by rw [hcoeff]
  · rw [reciprocal_of_notMem hθ,
      hF _ (fun hm => hθ ((recip_mem_Icc_iff ha (exp_pos s)).mp hm)), zero_mul, zero_mul]

/-- The physical even average is exactly the logarithmic even average. -/
theorem logScale_evenPhysical {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ)
    (hF : ∀ θ ∉ Icc a 1, F θ = 0) (s : ℝ) :
    Cvs.L2a.TailLogScaleTest.logScale (evenPhysical a F) s
      = (Cvs.L2a.TailLogScaleTest.logScale F s + Cvs.L2a.TailLogScaleTest.logScale F (Real.log a - s)) / 2 := by
  have hc : cut a F = F := by
    funext θ
    by_cases hθ : θ ∈ Icc a 1
    · exact indicator_of_mem hθ _
    · rw [cut, indicator_of_notMem hθ, hF _ hθ]
  rw [← logScale_reciprocal ha F hF s]
  unfold Cvs.L2a.TailLogScaleTest.logScale evenPhysical
  rw [hc]
  ring

/-- After shifting to `[0,-log a]`, reciprocal averaging is the actual `evenize`. -/
theorem logScale_evenPhysical_shifted {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ)
    (hF : ∀ θ ∉ Icc a 1, F θ = 0) (s : ℝ) :
    Cvs.L2a.TailLogScaleTest.logScale (evenPhysical a F) (s + Real.log a)
      = Cvs.Approximant.ConnesWindowCosineComplete.evenize (-Real.log a) (fun t => Cvs.L2a.TailLogScaleTest.logScale F (t + Real.log a)) s := by
  rw [logScale_evenPhysical ha F hF]
  unfold Cvs.Approximant.ConnesWindowCosineComplete.evenize
  change (Cvs.L2a.TailLogScaleTest.logScale F (s + Real.log a) + Cvs.L2a.TailLogScaleTest.logScale F (Real.log a - (s + Real.log a))) / 2 =
    (Cvs.L2a.TailLogScaleTest.logScale F (s + Real.log a) + Cvs.L2a.TailLogScaleTest.logScale F ((-Real.log a - s) + Real.log a)) / 2
  rw [show Real.log a - (s + Real.log a) = -s by ring,
    show (-Real.log a - s) + Real.log a = -s by ring]

/-- The actual Connes window averaged in physical reciprocal coordinates. -/
def connesAngularEven (x : ℝ) : ℝ → ℝ :=
  evenPhysical (1 / x) (Cvs.Xi.EImageWindowPoisson.window (1 / x)
    (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1))

/-- The actual physical average represents precisely the Connes even function already in the project. -/
theorem logScale_connesAngularEven {x : ℝ} (hx : 0 < x) (s : ℝ) :
    Cvs.L2a.TailLogScaleTest.logScale (connesAngularEven x) (s - Real.log x) = Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s := by
  have hloga : Real.log (1 / x) = -Real.log x := by rw [one_div, Real.log_inv]
  change Cvs.L2a.TailLogScaleTest.logScale (evenPhysical (1 / x) (Cvs.Xi.EImageWindowPoisson.window (1 / x)
    (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1))) (s - Real.log x) =
    Cvs.Approximant.ConnesWindowCosineComplete.evenize (Real.log x) (fun t => Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x)
      (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)) (t - Real.log x)) s
  simpa only [hloga, neg_neg, sub_eq_add_neg] using
    logScale_evenPhysical_shifted (one_div_pos.mpr hx)
      (Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1))
      (fun θ hθ => Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ) s

/-- The actual reflection-even Connes profile has exactly zero centered-log moment. -/
theorem integral_centeredLog_connesAngularEven_sq {x : ℝ} (hx : 0 < x) :
    ∫ θ, centeredLog (1 / x) θ * connesAngularEven x θ ^ 2 = 0 :=
  integral_centeredLog_evenPhysical_sq (one_div_pos.mpr hx) _

/-- Reciprocal reflection respects physical almost-everywhere equality. -/
theorem reciprocal_congr_ae {a : ℝ} (ha : 0 < a) {F G : ℝ → ℝ} (hFG : F =ᵐ[volume] G) :
    reciprocal a F =ᵐ[volume] reciprocal a G := by
  filter_upwards [Cvs.Xi.ReciprocalWindowPhysicalL2.branch_congr_ae ha (by omega : 1 ≤ 1) hFG] with θ hθ
  unfold reciprocal
  rw [hθ]

/-- The actual reciprocal reflection as a physical L² linear map. -/
def reciprocalLinear {a : ℝ} (ha : 0 < a) : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical →ₗ[ℝ] Cvs.Xi.ReciprocalWindowPhysicalL2.Physical where
  toFun F := (memLp_reciprocal ha (Lp.memLp F)).toLp (reciprocal a F)
  map_add' F G := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine (reciprocal_congr_ae ha (Lp.coeFn_add F G)).trans (ae_of_all _ fun θ => ?_)
    exact congrFun (reciprocal_add a (F : ℝ → ℝ) (G : ℝ → ℝ)) θ
  map_smul' r F := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    refine (reciprocal_congr_ae ha (Lp.coeFn_smul r F)).trans (ae_of_all _ fun θ => ?_)
    exact congrFun (reciprocal_smul a r (F : ℝ → ℝ)) θ

theorem coe_reciprocalLinear_ae {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    (reciprocalLinear ha F : ℝ → ℝ) =ᵐ[volume] reciprocal a F :=
  (memLp_reciprocal ha (Lp.memLp F)).coeFn_toLp

theorem norm_reciprocalLinear_le {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    ‖reciprocalLinear ha F‖ ≤ ‖F‖ := by
  have hsq : ‖reciprocalLinear ha F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
    calc
      ∫ θ, reciprocalLinear ha F θ ^ 2 = ∫ θ, reciprocal a F θ ^ 2 :=
        integral_congr_ae (by filter_upwards [coe_reciprocalLinear_ae ha F] with θ hθ; rw [hθ])
      _ = ∫ θ in Icc a 1, F θ ^ 2 := integral_reciprocal_sq ha _
      _ ≤ ∫ θ, F θ ^ 2 := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun _ => sq_nonneg _) (Lp.memLp F).integrable_sq
  nlinarith [norm_nonneg F, norm_nonneg (reciprocalLinear ha F)]

/-- The actual normalized reciprocal branch as a bounded physical L² map. -/
def reciprocalOp {a : ℝ} (ha : 0 < a) : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical →L[ℝ] Cvs.Xi.ReciprocalWindowPhysicalL2.Physical :=
  (reciprocalLinear ha).mkContinuous 1 (fun F => by simpa using norm_reciprocalLinear_le ha F)

theorem coe_reciprocalOp_ae {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
  (reciprocalOp ha F : ℝ → ℝ) =ᵐ[volume] reciprocal a F := coe_reciprocalLinear_ae ha F

/-- The square of the actual reciprocal operator is the physical interval projection. -/
theorem coe_reciprocalOp_sq_ae {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    (reciprocalOp ha (reciprocalOp ha F) : ℝ → ℝ) =ᵐ[volume] cut a F := by
  have hs : reciprocal a (reciprocal a F) =ᵐ[volume] cut a F :=
    ae_of_all _ fun θ => congrFun (reciprocal_sq ha (F : ℝ → ℝ)) θ
  exact (coe_reciprocalOp_ae ha (reciprocalOp ha F)).trans
    ((reciprocal_congr_ae ha (coe_reciprocalOp_ae ha F)).trans hs)

/-- The actual physical reciprocal-even projection. -/
def evenOp {a : ℝ} (ha : 0 < a) : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical →L[ℝ] Cvs.Xi.ReciprocalWindowPhysicalL2.Physical :=
  (1 / 2 : ℝ) • ((reciprocalOp ha).comp (reciprocalOp ha) + reciprocalOp ha)

/-- The actual operator has the exact cut-plus-reciprocal averaged representative. -/
theorem coe_evenOp_ae {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    (evenOp ha F : ℝ → ℝ) =ᵐ[volume] evenPhysical a F := by
  change (((1 / 2 : ℝ) • (reciprocalOp ha (reciprocalOp ha F) + reciprocalOp ha F)
    : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) : ℝ → ℝ) =ᵐ[volume] evenPhysical a F
  filter_upwards [Lp.coeFn_smul (E := ℝ) (p := 2) (μ := volume) (1 / 2 : ℝ)
      (reciprocalOp ha (reciprocalOp ha F) + reciprocalOp ha F),
    Lp.coeFn_add (reciprocalOp ha (reciprocalOp ha F)) (reciprocalOp ha F),
    coe_reciprocalOp_sq_ae ha F, coe_reciprocalOp_ae ha F] with θ h1 h2 h3 h4
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.add_apply, h3, h4]
  unfold evenPhysical
  ring

/-- Actual physical reflection averaging respects almost-everywhere equality. -/
theorem evenPhysical_congr_ae {a : ℝ} (ha : 0 < a) {F G : ℝ → ℝ}
    (hFG : F =ᵐ[volume] G) : evenPhysical a F =ᵐ[volume] evenPhysical a G := by
  filter_upwards [hFG, reciprocal_congr_ae ha hFG] with θ h1 h2
  by_cases hm : θ ∈ Icc a 1
  · simp only [evenPhysical, cut, indicator_of_mem hm, h1, h2]
  · simp only [evenPhysical, cut, indicator_of_notMem hm, h2]

/-- The actual projection acts on every physical L² representative by its explicit average. -/
theorem evenOp_toLp {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    evenOp ha (hF.toLp F) = (memLp_evenPhysical ha hF).toLp (evenPhysical a F) := by
  apply Lp.ext
  exact (coe_evenOp_ae ha (hF.toLp F)).trans
    ((evenPhysical_congr_ae ha hF.coeFn_toLp).trans (memLp_evenPhysical ha hF).coeFn_toLp.symm)

/-- The actual reciprocal-even projection has interval-supported range. -/
theorem evenOp_mem_intervalSpace {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    evenOp ha F ∈ Cvs.Xi.ReciprocalWindowPhysicalL2.intervalSpace a := by
  filter_upwards [coe_evenOp_ae ha F] with θ hθ hm
  rw [hθ, evenPhysical_of_notMem hm]

/-- The actual projected L² class is fixed by reciprocal reflection. -/
theorem reciprocalOp_evenOp {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    reciprocalOp ha (evenOp ha F) = evenOp ha F := by
  apply Lp.ext
  have he : reciprocal a (evenPhysical a F) =ᵐ[volume] evenPhysical a F :=
    ae_of_all _ fun θ => congrFun (reciprocal_evenPhysical ha (F : ℝ → ℝ)) θ
  exact (coe_reciprocalOp_ae ha (evenOp ha F)).trans
    ((reciprocal_congr_ae ha (coe_evenOp_ae ha F)).trans
      (he.trans (coe_evenOp_ae ha F).symm))

/-- The actual reciprocal-even map is idempotent. -/
theorem evenOp_sq {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    evenOp ha (evenOp ha F) = evenOp ha F := by
  change (1 / 2 : ℝ) •
    (reciprocalOp ha (reciprocalOp ha (evenOp ha F)) + reciprocalOp ha (evenOp ha F)) = _
  simp only [reciprocalOp_evenOp ha F]
  rw [← two_smul ℝ, smul_smul]
  norm_num

/-- The actual reciprocal-even projection is a physical contraction. -/
theorem norm_evenOp_le {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    ‖evenOp ha F‖ ≤ ‖F‖ := by
  change ‖(1 / 2 : ℝ) • (reciprocalOp ha (reciprocalOp ha F) + reciprocalOp ha F)‖ ≤ _
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 : ‖reciprocalOp ha F‖ ≤ ‖F‖ := norm_reciprocalLinear_le ha F
  have h2 : ‖reciprocalOp ha (reciprocalOp ha F)‖ ≤ ‖reciprocalOp ha F‖ :=
    norm_reciprocalLinear_le ha (reciprocalOp ha F)
  have h3 := norm_add_le (reciprocalOp ha (reciprocalOp ha F)) (reciprocalOp ha F)
  nlinarith

/-- The physical reciprocal operator has range in the actual interval support space. -/
theorem reciprocalOp_mem_intervalSpace {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    reciprocalOp ha F ∈ Cvs.Xi.ReciprocalWindowPhysicalL2.intervalSpace a := by
  filter_upwards [coe_reciprocalOp_ae ha F] with θ hθ hmem
  rw [hθ, reciprocal_of_notMem hmem]

/-- On the physical interval space the reciprocal operator is an actual involution. -/
theorem reciprocalOp_sq {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical)
    (hF : F ∈ Cvs.Xi.ReciprocalWindowPhysicalL2.intervalSpace a) : reciprocalOp ha (reciprocalOp ha F) = F := by
  have hc : cut a F =ᵐ[volume] (F : ℝ → ℝ) := by
    filter_upwards [hF] with θ hθ
    by_cases hm : θ ∈ Icc a 1
    · exact indicator_of_mem hm _
    · rw [cut, indicator_of_notMem hm, hθ hm]
  have hs : reciprocal a (reciprocal a F) =ᵐ[volume] cut a F :=
    ae_of_all _ fun θ => congrFun (reciprocal_sq ha (F : ℝ → ℝ)) θ
  apply Lp.ext
  exact (coe_reciprocalOp_ae ha (reciprocalOp ha F)).trans
    ((reciprocal_congr_ae ha (coe_reciprocalOp_ae ha F)).trans
      (hs.trans hc))

/-- The actual reciprocal operator is selfadjoint. -/
theorem inner_reciprocalOp {a : ℝ} (ha : 0 < a) (F G : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    inner ℝ (reciprocalOp ha F) G = inner ℝ F (reciprocalOp ha G) := by
  rw [Cvs.L2a.PlaneCorrelationL2.inner_eq_integral, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
  calc
    ∫ θ, reciprocalOp ha F θ * G θ = ∫ θ, reciprocal a F θ * G θ :=
      integral_congr_ae ((coe_reciprocalOp_ae ha F).mul EventuallyEq.rfl)
    _ = ∫ θ, F θ * reciprocal a G θ := integral_reciprocal_mul ha _ _
    _ = ∫ θ, F θ * reciprocalOp ha G θ :=
      integral_congr_ae (EventuallyEq.rfl.mul (coe_reciprocalOp_ae ha G).symm)

/-- The actual physical reciprocal operator is a selfadjoint continuous linear map. -/
theorem reciprocalOp_isSelfAdjoint {a : ℝ} (ha : 0 < a) : IsSelfAdjoint (reciprocalOp ha) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (inner_reciprocalOp ha)

/-- The reciprocal operator is an isometry on the physical interval space. -/
theorem norm_reciprocalOp_eq {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical)
    (hF : F ∈ Cvs.Xi.ReciprocalWindowPhysicalL2.intervalSpace a) : ‖reciprocalOp ha F‖ = ‖F‖ := by
  have h1 : ‖reciprocalOp ha F‖ ≤ ‖F‖ := norm_reciprocalLinear_le ha F
  have h2 : ‖reciprocalOp ha (reciprocalOp ha F)‖ ≤ ‖reciprocalOp ha F‖ :=
    norm_reciprocalLinear_le ha (reciprocalOp ha F)
  rw [reciprocalOp_sq ha F hF] at h2
  exact le_antisymm h1 h2

/-- The log operator has zero quadratic pairing on the actual reflected L² representative. -/
theorem inner_logOp_evenPhysical {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : MemLp F 2 volume) :
    let E := (memLp_evenPhysical ha hF).toLp (evenPhysical a F)
    inner ℝ (Cvs.WeilForm.CompressedPhysicalPrimeForm.logOp ha E) E = 0 := by
  dsimp only
  rw [Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
  calc
    ∫ θ, Cvs.WeilForm.CompressedPhysicalPrimeForm.logOp ha ((memLp_evenPhysical ha hF).toLp (evenPhysical a F)) θ *
        ((memLp_evenPhysical ha hF).toLp (evenPhysical a F)) θ
      = ∫ θ, Cvs.WeilForm.CompressedPhysicalPrimeForm.cutLog a θ * evenPhysical a F θ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [Cvs.WeilForm.CompressedPhysicalPrimeForm.coe_logOp_ae ha ((memLp_evenPhysical ha hF).toLp (evenPhysical a F)),
          (memLp_evenPhysical ha hF).coeFn_toLp] with θ h1 h2
        rw [h1, h2]
        ring
    _ = ∫ θ, centeredLog a θ * evenPhysical a F θ ^ 2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun θ => by
        change Cvs.WeilForm.CompressedPhysicalPrimeForm.cutLog a θ * evenPhysical a F θ ^ 2 =
          centeredLog a θ * evenPhysical a F θ ^ 2
        by_cases hm : θ ∈ Icc a 1
        · rw [Cvs.WeilForm.CompressedPhysicalPrimeForm.cutLog, indicator_of_mem hm]
        · rw [Cvs.WeilForm.CompressedPhysicalPrimeForm.cutLog, indicator_of_notMem hm, evenPhysical_of_notMem hm,
            zero_pow (by omega), mul_zero, mul_zero]
    _ = 0 := integral_centeredLog_evenPhysical_sq ha F

/-- The actual reciprocal-even projected class has zero centered-log quadratic pairing. -/
theorem inner_logOp_evenOp {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical) :
    inner ℝ (Cvs.WeilForm.CompressedPhysicalPrimeForm.logOp ha (evenOp ha F)) (evenOp ha F) = 0 := by
  have he : evenOp ha F =
      (memLp_evenPhysical ha (Lp.memLp F)).toLp (evenPhysical a F) := by
    apply Lp.ext
    exact (coe_evenOp_ae ha F).trans (memLp_evenPhysical ha (Lp.memLp F)).coeFn_toLp.symm
  rw [he]
  exact inner_logOp_evenPhysical ha (Lp.memLp F)

/-- Reciprocal-fixed classes are exactly fixed by the actual even projection. -/
theorem evenOp_eq_of_reciprocal_fixed {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical)
    (hF : reciprocalOp ha F = F) : evenOp ha F = F := by
  change (1 / 2 : ℝ) • (reciprocalOp ha (reciprocalOp ha F) + reciprocalOp ha F) = F
  rw [hF, hF, ← two_smul ℝ, smul_smul]
  norm_num

/-- The reciprocal fixed-space has exactly zero centered-log energy. -/
theorem inner_logOp_of_reciprocal_fixed {a : ℝ} (ha : 0 < a) (F : Cvs.Xi.ReciprocalWindowPhysicalL2.Physical)
    (hF : reciprocalOp ha F = F) : inner ℝ (Cvs.WeilForm.CompressedPhysicalPrimeForm.logOp ha F) F = 0 := by
  simpa only [evenOp_eq_of_reciprocal_fixed ha F hF] using inner_logOp_evenOp ha F

/-- The actual angular Connes window is in physical L². -/
theorem memLp_connesAngularWindow {x : ℝ} (hx : 0 < x) :
    MemLp (Cvs.Xi.EImageWindowPoisson.window (1 / x)
      (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)) 2 volume := by
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1
  have hGc : ContinuousOn G (Icc 0 1) :=
    (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hGc
  have ha : 0 < 1 / x := one_div_pos.mpr hx
  have hm : Measurable (Cvs.Xi.EImageWindowPoisson.window (1 / x) G) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).indicator measurableSet_Icc
  have hb : ∀ θ, |Cvs.Xi.EImageWindowPoisson.window (1 / x) G θ| ≤ M :=
    Cvs.Approximant.ConnesVectorRealScale.abs_window_le ha fun u hu => by simpa using hM u (Ioc_subset_Icc_self hu)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply Cvs.WeilForm.EImageRadical.integrable_of_bound_support (hm.pow_const 2)
  · intro θ
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb θ) 2
  · intro θ hθ
    rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ, zero_pow (by omega)]

/-- The actual reflection-even Connes profile is in physical L². -/
theorem memLp_connesAngularEven {x : ℝ} (hx : 0 < x) :
    MemLp (connesAngularEven x) 2 volume :=
  memLp_evenPhysical (one_div_pos.mpr hx) (memLp_connesAngularWindow hx)

/-- The actual Connes even moment is integrable as well as identically zero. -/
theorem integrable_centeredLog_connesAngularEven_sq {x : ℝ} (hx : 0 < x) :
    Integrable (fun θ => centeredLog (1 / x) θ * connesAngularEven x θ ^ 2) :=
  integrable_centeredLog_evenPhysical_sq (one_div_pos.mpr hx) (memLp_connesAngularWindow hx)

/-- The actual form-domain even class is represented by the reciprocal physical even profile. -/
theorem coe_even_connesClass_ae_logScale {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (((Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
      : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
      : Lp ℝ 2 volume) =ᵐ[volume]
        fun s => Cvs.L2a.TailLogScaleTest.logScale (connesAngularEven x) (s - Real.log x) := by
  exact (Cvs.Approximant.ConnesWindowCosineComplete.coe_even_connesClass_ae hx).trans
    (ae_of_all _ fun s => (logScale_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) s).symm)

/-- The actual physical Connes even class is the actual reciprocal-even projection of its window. -/
theorem evenOp_connesAngularWindow {x : ℝ} (hx : 0 < x) :
    evenOp (one_div_pos.mpr hx) ((memLp_connesAngularWindow hx).toLp
      (Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)))
      = (memLp_connesAngularEven hx).toLp (connesAngularEven x) :=
  evenOp_toLp (one_div_pos.mpr hx) (memLp_connesAngularWindow hx)

/-- The concrete physical Connes even class has zero centered-log operator energy. -/
theorem inner_logOp_connesAngularEven {x : ℝ} (hx : 0 < x) :
    let E := (memLp_connesAngularEven hx).toLp (connesAngularEven x)
    inner ℝ (Cvs.WeilForm.CompressedPhysicalPrimeForm.logOp (one_div_pos.mpr hx) E) E = 0 :=
  inner_logOp_evenPhysical (one_div_pos.mpr hx) (memLp_connesAngularWindow hx)

end Cvs.Xi.PhysicalReciprocalReflection
