import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.NegativeIndexQuadruples
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.ParitySectorNegativeIndex
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.EvenExplicitFormulaTameTests
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormIntegerMeasure
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The closing step of visibility from a share, a Bessel bound and a `b`-side rest

With `b` the pairing vector of a zero `σ`, `P` the projection onto `R₁` and `w = b − Pb`,
`Q(w) ≤ (√(Σ_ρ m_ρ⟪b, U_ρ⟫²) + √(Σ_ρ m_ρ⟪Pb, U_ρ⟫²))² − W_σ‖w‖⁴` with `U_ρ` the class of `ue_ρ(· − L/2)`.
A share bound `‖Pb‖² ≤ (1 − s₀)‖b‖²`, a Bessel bound at `Pb` and a `b`-side rest bound then give
`¬ EvenBulkFloor x 0`, at one `x` and eventually.
-/

noncomputable section

open Real MeasureTheory Filter Set
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.StepA.TopQuadruple (quad quadWeight)
open Cvs.StepA.NegativeIndexQuadruples (InQuad)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.Visibility.VisibilityClosingStep
open Cvs.ZeroCounting

/-! ### The `ue` vector -/

/-- The profile `s ↦ ue_z(s − log x / 2)`. -/
def ueProf (x : ℕ) (z : ℂ) (s : ℝ) : ℝ := ue z (s - Real.log x / 2)

/-- The `ue` profile is `C¹`. -/
theorem contDiff_ueProf (x : ℕ) (z : ℂ) : ContDiff ℝ 1 (ueProf x z) := by
  unfold ueProf ue; fun_prop

/-- The form-domain class at `x` of `ue_z(· − log x / 2)` on the window. -/
def ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) : Dom x :=
  Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_ueProf x z))

/-- The `ue` vector is a.e. the `ue` profile on `[0, log x)`. -/
theorem coe_ueVec_ae {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) :
    (((ueVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] (Ico 0 (Real.log x)).indicator (ueProf x z) :=
  (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans (Eventually.of_forall fun s => Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0 _ s)

/-- For `u` a.e. equal to `f`, `⟪u, ueVec⟫ = ∫_{−L/2}^{L/2} f(t + L/2) ue_z(t) dt`, `L = log x`. -/
theorem inner_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) (u : Dom x) {f : ℝ → ℝ}
    (hu : (((u : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] f) :
    ⟪u, ueVec hx0 z⟫_ℝ
      = ∫ t in -(Real.log x / 2)..Real.log x / 2, f (t + Real.log x / 2) * ue z t := by
  have h : ⟪u, ueVec hx0 z⟫_ℝ
      = ⟪(((u : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)),
          (((ueVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ :=
    rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral,
    integral_congr_ae (g := (Ico 0 (Real.log x)).indicator (fun s => f s * ueProf x z s)),
    Cvs.Route.Visibility.ZeroPairingVector.integral_indicator_Ico_eq (Real.log_natCast_nonneg x)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ueProf, add_sub_cancel_right]
  · filter_upwards [hu, coe_ueVec_ae hx0 z] with s h1 h2
    rw [h1, h2]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-! ### The even explicit formula on even tame classes, as inner products -/

/-- `sqTransform L (cf f)` depends on `f` only up to a.e. equality. -/
theorem sqTransform_congr_ae (L : ℝ) {f f' : ℝ → ℝ} (h : f =ᵐ[volume] f') (ξ : ℂ) :
    Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ = Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f') ξ := by
  simp only [Cvs.Detection.sqTransform, Cvs.WeilForm.WindowFormIntegerMeasure.windowTransform_congr_ae h]

/-- A reflection-even class satisfies `u(L − s) = u(s)` a.e., `L = log x`. -/
theorem refl_coe_ae {x : ℕ} {w : Dom x} (hw : w ∈ Ev x) :
    (fun s => (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)) (Real.log x - s))
      =ᵐ[volume] (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)) := by
  have h : Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
      = (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)) :=
    congrArg (fun u : Dom x => ((u : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)))
      (show Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) w = w from hw)
  have h2 := Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x)
    (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
  rw [h] at h2
  exact h2.symm

/-- The symmetrised centred profile `(F(t + L/2) + F(L/2 − t))/2`. -/
def symProf (L : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := (F (t + L / 2) + F (L / 2 - t)) / 2

/-- The symmetrised profile is even. -/
theorem symProf_neg (L : ℝ) (F : ℝ → ℝ) (t : ℝ) : symProf L F (-t) = symProf L F t := by
  unfold symProf
  rw [show -t + L / 2 = L / 2 - t by ring, show L / 2 - -t = t + L / 2 by ring, add_comm]

/-- **The even explicit formula on an even tame class, as inner products**: for `2 ≤ x`, `w = w_u` with `u` tame
on `[1/x, 1]` and `w` reflection-even, `Q(w) = Σ_ρ m_ρ(⟪w, U_ρ⟫² − ⟪w, V_ρ⟫²)`, the family summable, where
`U_ρ`, `V_ρ` are the `ue` and pairing vectors at `ρ`. -/
theorem Qx_eq_tsum_inner {x : ℕ} (hx : 2 ≤ x) (hx0 : (0 : ℝ) < x) {u : ℝ → ℝ} (hu : Tame u (1 / x) 1)
    {w : Dom x} (hwE : w ∈ Ev x) (hw : w = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) :
    Qx x w = ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * (⟪w, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
          - ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * (⟪w, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
          - ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2) := by
  set L := Real.log x with hL
  set F := Cvs.Approximant.SpineCouplingTailPairing.fv x u with hFdef
  have hFi : Integrable F := Cvs.WeilForm.EvenExplicitFormulaTameTests.integrable_fv hu
  have hcoe : (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] F := by
    subst hw; exact Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hu
  have hrefl : (fun s => F (L - s)) =ᵐ[volume] F := by
    have h2 := (Measure.measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp hcoe
    filter_upwards [h2, refl_coe_ae hwE, hcoe] with s a b c
    simp only [Function.comp_apply] at a
    rw [← a, b, c]
  have hg : F =ᵐ[volume] fun s => symProf L F (s - L / 2) := by
    filter_upwards [hrefl] with s hs
    simp only [symProf, sub_add_cancel, show L / 2 - (s - L / 2) = L - s by ring, hs]
    ring
  have hgi : IntervalIntegrable (symProf L F) volume (-(L / 2)) (L / 2) := by
    have h1 : Integrable fun t => F (t + L / 2) := hFi.comp_add_right (L / 2)
    have h2 : Integrable fun t => F (L / 2 - t) := hFi.comp_sub_left (L / 2)
    exact ((h1.add h2).div_const 2).intervalIntegrable
  have hcg := hcoe.trans hg
  have hterm : ∀ ρ : nonTrivialZeroSet,
      (Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf F) (Cvs.ZeroCounting.zPoint ρ)).re
        = ⟪w, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
          - ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := by
    intro ρ
    rw [sqTransform_congr_ae L hg, Cvs.StepA.OneZeroParitySectors.re_sqTransform_of_even L hgi (symProf_neg L F),
      inner_ueVec hx0 _ w hcg, Cvs.Route.Visibility.ZeroPairingVector.inner_pairVec hx0 _ w hcg]
    rw [← hL]
    simp only [add_sub_cancel_right]
  obtain ⟨h1, h2⟩ := Cvs.WeilForm.TameWindowZeroSum.Q_wv_eq_kernelZeroSide hx hu 0 0
  subst hw
  refine ⟨?_, h2.congr fun ρ => by rw [hterm]⟩
  show Cvs.WeilForm.InfimumAttainedSphere.Q _ _ _ _ = _
  rw [h1, Cvs.ZeroCounting.kernelZeroSide]
  exact tsum_congr fun ρ => by rw [hterm]

/-- The square `⟪w, V_ρ⟫²` is constant on a quadruple. -/
theorem sq_inner_pairVec_quad {x : ℕ} (hx0 : (0 : ℝ) < x) (w : Dom x) {ρ σ : nonTrivialZeroSet}
    (hq : InQuad ρ σ) :
    ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      = ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)⟫_ℝ ^ 2 := by
  rw [Cvs.Route.Visibility.ZeroPairingVector.inner_pairVec hx0 _ w (Filter.EventuallyEq.refl _ _),
    Cvs.Route.Visibility.ZeroPairingVector.inner_pairVec hx0 _ w (Filter.EventuallyEq.refl _ _)]
  rcases Cvs.StepA.ParitySectorNegativeIndex.ve_quad hq with h | h
  · simp_rw [h]
  · simp_rw [h, mul_neg, intervalIntegral.integral_neg, neg_sq]

/-- **The form below the `ue` sum**: under the hypotheses of `Qx_eq_tsum_inner`, if `m_ρ⟪w, U_ρ⟫²` is summable
then `Q(w) ≤ Σ_ρ m_ρ⟪w, U_ρ⟫² − W_σ⟪w, V_σ⟫²` for every zero `σ`. -/
theorem Qx_le_tsum_ue_sub {x : ℕ} (hx : 2 ≤ x) (hx0 : (0 : ℝ) < x) {u : ℝ → ℝ} (hu : Tame u (1 / x) 1)
    {w : Dom x} (hwE : w ∈ Ev x) (hw : w = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (σ : nonTrivialZeroSet)
    (hA : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪w, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2) :
    Qx x w ≤ ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪w, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      - quadWeight σ * ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)⟫_ℝ ^ 2 := by
  obtain ⟨hQ, hS⟩ := Qx_eq_tsum_inner hx hx0 hu hwE hw
  set c : nonTrivialZeroSet → ℝ := fun ρ => ⟪w, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
    with hc
  have hB : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ) * c ρ :=
    (hA.sub hS).congr fun ρ => by simp only [hc]; ring
  have hsplit := Cvs.WeilForm.EvenExplicitFormulaTameTests.tsum_quad_split σ hB fun ρ hq => sq_inner_pairVec_quad hx0 w hq
  have hcompl : 0 ≤ ∑' ρ : ↥((quad σ : Set nonTrivialZeroSet)ᶜ),
      (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) * c ρ :=
    tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hdiff : Qx x w = ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪w, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      - ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ) * c ρ := by
    rw [hQ, ← hA.tsum_sub hB]
    exact tsum_congr fun ρ => by simp only [hc]; ring
  rw [hdiff, hsplit]
  linarith

/-! ### The weighted `ℓ²` triangle inequality -/

/-- `(a − c)² ≤ (1 + t)a² + (1 + 1/t)c²` for `t > 0`. -/
theorem sq_sub_le (a c : ℝ) {t : ℝ} (ht : 0 < t) : (a - c) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + 1 / t) * c ^ 2 := by
  have key : 0 ≤ t * a ^ 2 + c ^ 2 / t + 2 * a * c := by
    have e : t * a ^ 2 + c ^ 2 / t + 2 * a * c = (t * a + c) ^ 2 / t := by
      field_simp; ring
    rw [e]; positivity
  have e2 : (1 + 1 / t) * c ^ 2 = c ^ 2 + c ^ 2 / t := by field_simp
  rw [e2]; nlinarith [key]

/-- If `X ≤ (1 + t)A + (1 + 1/t)C` for all `t > 0`, with `A, C ≥ 0`, then `X ≤ (√A + √C)²`. -/
theorem le_sqrt_add_sqrt_sq {X A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h : ∀ t, 0 < t → X ≤ (1 + t) * A + (1 + 1 / t) * C) : X ≤ (√A + √C) ^ 2 := by
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    rw [Real.sqrt_zero, zero_add, Real.sq_sqrt hC]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have ht : 0 < (C + 1) / ε := by positivity
    have h1 := h _ ht
    have e : (1 + 1 / ((C + 1) / ε)) * C = C + ε * (C / (C + 1)) := by field_simp
    have hle : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    rw [mul_zero, zero_add, e] at h1
    nlinarith
  rcases hC.eq_or_lt with hC0 | hC0
  · subst hC0
    rw [Real.sqrt_zero, add_zero, Real.sq_sqrt hA]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have ht : 0 < ε / (A + 1) := by positivity
    have h1 := h _ ht
    have e : (1 + ε / (A + 1)) * A = A + ε * (A / (A + 1)) := by field_simp
    have hle : A / (A + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    rw [mul_zero, add_zero, e] at h1
    nlinarith
  · have ha := Real.sqrt_pos.2 hA0
    have hc := Real.sqrt_pos.2 hC0
    have h1 := h (√C / √A) (div_pos hc ha)
    have hA' := Real.sq_sqrt hA
    have hC' := Real.sq_sqrt hC
    set a := √A
    set c := √C
    rw [← hA', ← hC'] at h1
    have e : (1 + c / a) * a ^ 2 + (1 + 1 / (c / a)) * c ^ 2 = (a + c) ^ 2 := by
      field_simp
      ring
    linarith

/-- **Weighted `ℓ²` triangle inequality**: for `m ≥ 0` with `m a²`, `m c²` summable, `m (a − c)²` is summable and
`Σ m (a − c)² ≤ (√(Σ m a²) + √(Σ m c²))²`. -/
theorem tsum_mul_sub_sq_le {ι : Type*} {m a c : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    (ha : Summable fun i => m i * a i ^ 2) (hc : Summable fun i => m i * c i ^ 2) :
    (Summable fun i => m i * (a i - c i) ^ 2)
      ∧ ∑' i, m i * (a i - c i) ^ 2 ≤ (√(∑' i, m i * a i ^ 2) + √(∑' i, m i * c i ^ 2)) ^ 2 := by
  have hpt : ∀ t, 0 < t → ∀ i, m i * (a i - c i) ^ 2 ≤ (1 + t) * (m i * a i ^ 2) + (1 + 1 / t) * (m i * c i ^ 2) := by
    intro t ht i
    have := mul_le_mul_of_nonneg_left (sq_sub_le (a i) (c i) ht) (hm i)
    linarith
  have hs : Summable fun i => m i * (a i - c i) ^ 2 :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm i) (sq_nonneg _)) (hpt 1 one_pos)
      ((ha.mul_left _).add (hc.mul_left _))
  refine ⟨hs, le_sqrt_add_sqrt_sq (tsum_nonneg fun i => mul_nonneg (hm i) (sq_nonneg _))
    (tsum_nonneg fun i => mul_nonneg (hm i) (sq_nonneg _)) fun t ht => ?_⟩
  refine (Summable.tsum_le_tsum (hpt t ht) hs ((ha.mul_left _).add (hc.mul_left _))).trans (le_of_eq ?_)
  rw [Summable.tsum_add (ha.mul_left _) (hc.mul_left _), tsum_mul_left, tsum_mul_left]

/-! ### F10: the closing theorem -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (R : Submodule ℝ E)
  [R.HasOrthogonalProjection]

/-- With `w = b − P_R b`: `‖w‖² = ‖b‖² − ‖P_R b‖²` and `⟪w, b⟫ = ‖w‖²`. -/
theorem sub_starProjection_facts (b : E) :
    ‖b - R.starProjection b‖ ^ 2 = ‖b‖ ^ 2 - ‖R.starProjection b‖ ^ 2
      ∧ ⟪b - R.starProjection b, b⟫_ℝ = ‖b - R.starProjection b‖ ^ 2 := by
  have hperp : ⟪b - R.starProjection b, R.starProjection b⟫_ℝ = 0 :=
    R.starProjection_inner_eq_zero b _ (R.starProjection_apply_mem b)
  constructor
  · have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hperp
    rw [sub_add_cancel] at h
    linarith
  · have h : ⟪b - R.starProjection b, (b - R.starProjection b) + R.starProjection b⟫_ℝ
        = ‖b - R.starProjection b‖ ^ 2 := by
      rw [inner_add_right, hperp, add_zero, real_inner_self_eq_norm_sq]
    rwa [sub_add_cancel] at h

/-- `⟪b − P_R b, u⟫ = ⟪b, u⟫ − ⟪P_R b, u⟫`. -/
theorem inner_sub_starProjection (b u : E) :
    ⟪b - R.starProjection b, u⟫_ℝ = ⟪b, u⟫_ℝ - ⟪R.starProjection b, u⟫_ℝ :=
  inner_sub_left _ _ _

end Projection

/-! ### The eventual version -/

/-- `80 ≤ 2πx` for `x ≥ 14`. -/
theorem scale_of_ge {x : ℕ} (hx : 14 ≤ x) : 80 ≤ 2 * π * x := by
  have h : (14 : ℝ) ≤ x := by exact_mod_cast hx
  nlinarith [Real.pi_gt_three]

end Cvs.Route.Visibility.VisibilityClosingStep

end
