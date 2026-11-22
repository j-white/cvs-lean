import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.SectorGramBoxTransform
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pairing vector of one zero

For `z ∈ ℂ` and `L = log x`, the pairing vector is the form-domain class of `s ↦ ve_z(s − L/2)` on
`[0, L)`, built as `Cvs.Approximant.SpineCouplingTailPairing.wv` of `Cvs.WeilForm.TameClassesFormDense.ofWin`. It is reflection-even, it pairs with a class `u` as
`∫_{−L/2}^{L/2} u(t + L/2) ve_z(t) dt`, and with `γ = Re z`, `y = Im z ≠ 0` its squared norm is
`(sinh(yL)/y − L + L sinc(γL) − (γ sin γL cosh yL + y cos γL sinh yL)/(γ² + y²))/4`.
-/

noncomputable section

open MeasureTheory Real Set Filter
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.ZeroPairingVector
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.StepA.OneZeroParitySectors (ve ue)

/-! ### The profile and the class -/

/-- The pairing profile `s ↦ ve_z(s − log x / 2)`. -/
def pairProf (x : ℕ) (z : ℂ) (s : ℝ) : ℝ := ve z (s - Real.log x / 2)

/-- The pairing profile is `C¹`. -/
theorem contDiff_pairProf (x : ℕ) (z : ℂ) : ContDiff ℝ 1 (pairProf x z) := by
  unfold pairProf ve; fun_prop

/-- The pairing vector: the form-domain class at `x` of `ve_z(· − log x / 2)` on the window. -/
def pairVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) : Dom x :=
  Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_pairProf x z))

/-- **The class of `ofWin x g` is `g` on `[0, log x)`**, pointwise. -/
theorem fv_ofWin {x : ℕ} (hx0 : (0 : ℝ) < x) (g : ℝ → ℝ) (s : ℝ) :
    Cvs.Approximant.SpineCouplingTailPairing.fv x (Cvs.WeilForm.TameClassesFormDense.ofWin x g) s = (Ico 0 (Real.log x)).indicator g s := by
  have hiff : Real.exp (s - Real.log x) ∈ Ico (1 / (x : ℝ)) 1 ↔ s ∈ Ico 0 (Real.log x) := by
    have h1 : 1 / (x : ℝ) = Real.exp (-Real.log x) := by
      rw [Real.exp_neg, Real.exp_log hx0, one_div]
    rw [h1, mem_Ico, mem_Ico, Real.exp_le_exp, ← Real.exp_zero, Real.exp_lt_exp]
    constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
  simp only [Cvs.Approximant.SpineCouplingTailPairing.fv, Cvs.L2a.TailLogScaleTest.logScale, Cvs.WeilForm.TameClassesFormDense.ofWin]
  by_cases hmem : s ∈ Ico 0 (Real.log x)
  · rw [indicator_of_mem (hiff.2 hmem), indicator_of_mem hmem, Real.log_exp, sub_add_cancel,
      ← Real.exp_half, div_mul_cancel₀]
    exact (Real.exp_pos _).ne'
  · rw [indicator_of_notMem (fun h => hmem (hiff.1 h)), indicator_of_notMem hmem, zero_mul]

/-- The pairing vector is a.e. the pairing profile on `[0, log x)`. -/
theorem coe_pairVec_ae {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) :
    (((pairVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] (Ico 0 (Real.log x)).indicator (pairProf x z) :=
  (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans (Eventually.of_forall fun s => fv_ofWin hx0 _ s)

/-- An integral over `[0, L)` is the centred window integral of the shifted integrand. -/
theorem integral_indicator_Ico_eq {L : ℝ} (hL : 0 ≤ L) (F : ℝ → ℝ) :
    ∫ s, (Ico 0 L).indicator F s = ∫ t in -(L / 2)..L / 2, F (t + L / 2) := by
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_comp_add_right]
  congr 1 <;> ring

/-! ### Evenness and pairing -/

/-- **The pairing vector is reflection-even**. -/
theorem pairVec_mem_Ev {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) : pairVec hx0 z ∈ Ev x := by
  show Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (pairVec hx0 z) = pairVec hx0 z
  apply Subtype.ext; apply Subtype.ext
  show Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) (((pairVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
      : Lp ℝ 2 (volume : Measure ℝ))
    = (((pairVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
  apply Lp.ext
  have h2 := (Measure.measurePreserving_sub_left volume (Real.log x)).quasiMeasurePreserving.ae_eq_comp
    (coe_pairVec_ae hx0 z)
  filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) _, h2, coe_pairVec_ae hx0 z,
    (Set.countable_singleton (0 : ℝ)).ae_notMem volume,
    (Set.countable_singleton (Real.log x)).ae_notMem volume] with s h1 h2 h3 h4 h5
  rw [h1, h3]
  simp only [Function.comp_apply] at h2
  rw [h2]
  have h4 : s ≠ 0 := h4
  have h5 : s ≠ Real.log x := h5
  have hmem : Real.log x - s ∈ Ico 0 (Real.log x) ↔ s ∈ Ico 0 (Real.log x) := by
    simp only [mem_Ico]
    constructor
    · rintro ⟨a, b⟩; exact ⟨by linarith, lt_of_le_of_ne (by linarith) h5⟩
    · rintro ⟨a, b⟩; exact ⟨by linarith, by
        rcases lt_or_eq_of_le a with a | a
        · linarith
        · exact absurd a.symm h4⟩
  by_cases hs : s ∈ Ico 0 (Real.log x)
  · rw [indicator_of_mem (hmem.2 hs), indicator_of_mem hs, pairProf, pairProf, ← Cvs.StepA.OneZeroParitySectors.ve_neg]
    congr 1; ring
  · rw [indicator_of_notMem (fun h => hs (hmem.1 h)), indicator_of_notMem hs]

/-- **The pairing of a class with the pairing vector**: for `u` a.e. equal to `f`,
`⟪u, pairVec⟫ = ∫_{−L/2}^{L/2} f(t + L/2) ve_z(t) dt`, `L = log x`. -/
theorem inner_pairVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) (u : Dom x) {f : ℝ → ℝ}
    (hu : (((u : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] f) :
    ⟪u, pairVec hx0 z⟫_ℝ
      = ∫ t in -(Real.log x / 2)..Real.log x / 2, f (t + Real.log x / 2) * ve z t := by
  have h : ⟪u, pairVec hx0 z⟫_ℝ
      = ⟪(((u : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)),
          (((pairVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ :=
    rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral,
    integral_congr_ae (g := (Ico 0 (Real.log x)).indicator (fun s => f s * pairProf x z s)),
    integral_indicator_Ico_eq (Real.log_natCast_nonneg x)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pairProf, add_sub_cancel_right]
  · filter_upwards [hu, coe_pairVec_ae hx0 z] with s h1 h2
    rw [h1, h2]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-! ### The squared norm -/

/-- The squared norm of the pairing vector is `∫_{−L/2}^{L/2} ve_z²`. -/
theorem norm_sq_pairVec_eq_integral {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) :
    ‖pairVec hx0 z‖ ^ 2 = ∫ t in -(Real.log x / 2)..Real.log x / 2, ve z t ^ 2 := by
  have h : ‖pairVec hx0 z‖
      = ‖(((pairVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))‖ := rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral,
    integral_congr_ae (g := (Ico 0 (Real.log x)).indicator (fun s => pairProf x z s ^ 2)),
    integral_indicator_Ico_eq (Real.log_natCast_nonneg x)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pairProf, add_sub_cancel_right]
  · filter_upwards [coe_pairVec_ae hx0 z] with s h2
    rw [h2]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-- `A = ∫ cos 2xt cosh 2yt` over the centred window. -/
def gA (L : ℝ) (z : ℂ) : ℝ := ∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t)

/-- `(x² + y²) A = x sin xL cosh yL + y cos xL sinh yL`. -/
theorem normSq_mul_gA (L : ℝ) (z : ℂ) :
    (z.re ^ 2 + z.im ^ 2) * gA L z
      = z.re * sin (z.re * L) * cosh (z.im * L) + z.im * cos (z.re * L) * sinh (z.im * L) :=
  Cvs.StepA.SectorGramBoxTransform.normSq_mul_integral_cos_cosh L z

/-- `4 ∫ ve_z² = ∫ cosh 2yt − L + L sinc(xL) − A` over the centred window. -/
theorem four_mul_integral_ve_sq (L : ℝ) (z : ℂ) :
    4 * ∫ t in -(L / 2)..L / 2, ve z t ^ 2
      = (∫ t in -(L / 2)..L / 2, cosh (2 * z.im * t)) - L + L * Real.sinc (z.re * L) - gA L z := by
  have hadd := Cvs.StepA.SectorGramBoxTransform.gram_even_add L z
  have hsub := Cvs.StepA.SectorGramBoxTransform.gram_even_sub L z
  rw [Cvs.StepA.SectorGramBoxTransform.integral_cos_two_mul] at hadd
  unfold gA
  linarith

/-- **The squared norm of the pairing vector, exactly**: with `γ = Re z`, `y = Im z ≠ 0`, `L = log x`,
`‖pairVec‖² = (sinh(yL)/y − L + L sinc(γL) − (γ sin γL cosh yL + y cos γL sinh yL)/(γ² + y²))/4`. -/
theorem norm_sq_pairVec {x : ℕ} (hx0 : (0 : ℝ) < x) {z : ℂ} (hy : z.im ≠ 0) :
    ‖pairVec hx0 z‖ ^ 2
      = (sinh (z.im * Real.log x) / z.im - Real.log x + Real.log x * Real.sinc (z.re * Real.log x)
          - (z.re * sin (z.re * Real.log x) * cosh (z.im * Real.log x)
              + z.im * cos (z.re * Real.log x) * sinh (z.im * Real.log x)) / (z.re ^ 2 + z.im ^ 2)) / 4 := by
  set L := Real.log x
  have hn : z.re ^ 2 + z.im ^ 2 ≠ 0 := by positivity
  have h4 := four_mul_integral_ve_sq L z
  have hc := Cvs.StepA.SectorGramBoxTransform.mul_integral_cosh_two_mul L z.im
  have hA := normSq_mul_gA L z
  have hC : ∫ t in -(L / 2)..L / 2, cosh (2 * z.im * t) = sinh (z.im * L) / z.im := by
    rw [eq_div_iff hy, mul_comm]; exact hc
  have hA' : gA L z = (z.re * sin (z.re * L) * cosh (z.im * L) + z.im * cos (z.re * L) * sinh (z.im * L))
      / (z.re ^ 2 + z.im ^ 2) := by
    rw [eq_div_iff hn, mul_comm]; exact hA
  rw [norm_sq_pairVec_eq_integral, ← hC, ← hA']
  linarith

/-- **The pairing vector is nonzero** for `x > 1`, `Re z ≠ 0`, `Im z ≠ 0`. -/
theorem pairVec_ne_zero {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 1 < x) {z : ℂ} (hre : z.re ≠ 0)
    (him : z.im ≠ 0) : pairVec hx0 z ≠ 0 := by
  intro h0
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  set L := Real.log x
  have hnorm := norm_sq_pairVec_eq_integral hx0 z
  have hz : ‖pairVec hx0 z‖ ^ 2 = 0 := by rw [h0]; simp
  rw [hz] at hnorm
  set ε := min (L / 2) (π / |z.re|) with hε
  have ha : 0 < |z.re| := abs_pos.2 hre
  have hε0 : 0 < ε := lt_min (by linarith) (div_pos Real.pi_pos ha)
  have hcont : Continuous fun t => ve z t ^ 2 := by unfold ve; fun_prop
  have hpos : 0 < ∫ t in (0 : ℝ)..ε, ve z t ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) ?_ hε0
    intro t ht
    have ht0 : 0 < t := ht.1
    have htπ : |z.re| * t < π := by
      have : t < π / |z.re| := ht.2.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ ha, mul_comm] at this
    have hsin : sin (z.re * t) ≠ 0 := by
      have hp : 0 < sin (|z.re| * t) := Real.sin_pos_of_pos_of_lt_pi (by positivity) htπ
      rcases abs_choice z.re with e | e
      · rw [e] at hp; exact hp.ne'
      · rw [e, neg_mul, Real.sin_neg] at hp; linarith
    have hsinh : sinh (z.im * t) ≠ 0 := by
      rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero him ht0.ne'
    have hv : ve z t ≠ 0 := mul_ne_zero hsin hsinh
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hv))
  have hmono : (∫ t in (0 : ℝ)..ε, ve z t ^ 2) ≤ ∫ t in -(L / 2)..L / 2, ve z t ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) hε0.le (min_le_left _ _)
      (Eventually.of_forall fun t => sq_nonneg _) (hcont.intervalIntegrable _ _)
  rw [← hnorm] at hmono
  linarith

end Cvs.Route.Visibility.ZeroPairingVector
