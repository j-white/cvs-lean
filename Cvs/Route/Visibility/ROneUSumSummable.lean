import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.EvenExplicitFormulaTameTests
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.ZeroSideSampleMellin
import Cvs.Zeta.ExplicitFormula.EdgeJumpWindowTests
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `U`-sum of every vector of `R₁` is summable at every `x`

For `v` tame on `[1/x, 1]`, `2∫ g ue_z = Re(ctr g z + ctr g (−z))` and `TameWindowZeroSum`'s envelope give
`|⟪w_v, U_z⟫| ≤ e^{L/4}C_v/(1 + |Re z|)` for `|Im z| ≤ ½`, so `Σ_ρ m_ρ⟪w_v, U_ρ⟫²` converges against
`Σ_ρ m_ρ/(1 + γ²)`. The even rungs are such classes and summability is closed under linear combinations, so it
holds on all of `R₁`, in particular at `P_{R₁} b` for every `b`; this is the summability conjunct of `ShareBessel`.
-/

noncomputable section

open Real MeasureTheory Filter
open scoped InnerProductSpace
open Cvs.WeilForm.SelfConvolutionTransform (cf)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Route.L1FloorFromBulkD0 (Dom rung)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo ctr)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (bPerp)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.Visibility.ROneUSumSummable
open Cvs.ZeroCounting

/-! ### The `ue` pairing of a profile through the centred transform -/

/-- `2∫ g ue_z = Re ctr g z + Re ctr g (−z)` on the centred window. -/
theorem two_mul_integral_ue (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (z : ℂ) :
    2 * ∫ t in -(L / 2)..L / 2, g t * ue z t = (ctr L g z).re + (ctr L g (-z)).re := by
  rw [Cvs.StepA.OneZeroParitySectors.ctr_eq L hg z, Cvs.StepA.OneZeroParitySectors.ctr_eq L hg (-z)]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero]
  have hneg : ∀ t, ue (-z) t + vo (-z) t = ue z t - vo z t := fun t => by
    rw [(Cvs.StepA.OneZeroParitySectors.weights_neg z t).1, (Cvs.StepA.OneZeroParitySectors.weights_neg z t).2.2.2]; ring
  simp_rw [hneg]
  have i1 : IntervalIntegrable (fun t => g t * (ue z t + vo z t)) volume (-(L / 2)) (L / 2) :=
    hg.mul_continuousOn (by fun_prop : Continuous fun t => ue z t + vo z t).continuousOn
  have i2 : IntervalIntegrable (fun t => g t * (ue z t - vo z t)) volume (-(L / 2)) (L / 2) :=
    hg.mul_continuousOn (by fun_prop : Continuous fun t => ue z t - vo z t).continuousOn
  rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by ring

/-- `|∫ g ue_z| ≤ (‖ctr g z‖ + ‖ctr g (−z)‖)/2`. -/
theorem abs_integral_ue_le (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (z : ℂ) :
    |∫ t in -(L / 2)..L / 2, g t * ue z t| ≤ (‖ctr L g z‖ + ‖ctr L g (-z)‖) / 2 := by
  have h := two_mul_integral_ue L hg z
  have h1 := Complex.abs_re_le_norm (ctr L g z)
  have h2 := Complex.abs_re_le_norm (ctr L g (-z))
  rw [abs_le]
  constructor <;> nlinarith [abs_le.1 h1, abs_le.1 h2]

/-- For `|Im z| ≤ ½`, `‖ctr g z‖ ≤ e^{L/4}‖W_L(g(· − L/2))(z)‖`. -/
theorem norm_ctr_le {L : ℝ} (hL : 0 ≤ L) (g : ℝ → ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖ctr L g z‖ ≤ Real.exp (L / 4)
      * ‖Cvs.Detection.windowTransform L (cf fun s => g (s - L / 2)) z‖ := by
  rw [Cvs.StepA.OneZeroParitySectors.windowTransform_eq_ctr, norm_mul, Complex.norm_exp, ← mul_assoc, ← Real.exp_add]
  have hre : (-(((L / 2 : ℝ) : ℂ) * z) * Complex.I).re = L / 2 * z.im := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  have h1 : 0 ≤ L / 4 + L / 2 * z.im := by
    have := (abs_le.1 hz).1
    nlinarith
  calc ‖ctr L g z‖ = 1 * ‖ctr L g z‖ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.one_le_exp h1) (norm_nonneg _)

/-! ### The decay of `⟪w_v, U_z⟫` for a tame class -/

/-- **`1/|Re z|` decay of the `ue` pairing**: for `v` tame on `[1/x, 1]` some `C` has
`|⟪w_v, U_z⟫| ≤ C/(1 + |Re z|)` whenever `|Im z| ≤ ½`. -/
theorem exists_abs_inner_ueVec_le {x : ℕ} (hx0 : (0 : ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ 1 / 2 → |⟪Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv, ueVec hx0 z⟫_ℝ| ≤ C / (1 + |z.re|) := by
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  have hα : (1 : ℝ) / x = Real.exp (-L) := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
  have hv' : Tame v (Real.exp (-L)) 1 := hα ▸ hv
  obtain ⟨C, hC⟩ := Cvs.WeilForm.TameWindowZeroSum.exists_envelope_logWin hL hv'
  set F := Cvs.Approximant.SpineCouplingTailPairing.fv x v with hF
  set g : ℝ → ℝ := fun t => F (t + L / 2) with hgdef
  have hgF : (fun s => g (s - L / 2)) = Cvs.WeilForm.ZeroSideSampleMellin.logWin L v := by
    funext s
    show F (s - L / 2 + L / 2) = _
    rw [sub_add_cancel]
    rfl
  have hgi : IntervalIntegrable g volume (-(L / 2)) (L / 2) :=
    ((Cvs.WeilForm.EvenExplicitFormulaTameTests.integrable_fv hv).comp_add_right (L / 2)).intervalIntegrable
  refine ⟨Real.exp (L / 4) * C, fun z hz => ?_⟩
  have hz' : |(-z).im| ≤ 1 / 2 := by rwa [Complex.neg_im, abs_neg]
  have hinner : ⟪Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv, ueVec hx0 z⟫_ℝ = ∫ t in -(L / 2)..L / 2, g t * ue z t :=
    Cvs.Route.Visibility.VisibilityClosingStep.inner_ueVec hx0 z
      (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv)
      (f := Cvs.Approximant.SpineCouplingTailPairing.fv x v)
      (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hv)
  have e1 := norm_ctr_le hL g hz
  have e2 := norm_ctr_le hL g hz'
  rw [hgF] at e1 e2
  have c1 := hC z hz
  have c2 := hC (-z) hz'
  rw [Complex.neg_re, abs_neg] at c2
  have he : 0 ≤ Real.exp (L / 4) := (Real.exp_pos _).le
  have d1 := mul_le_mul_of_nonneg_left c1 he
  have d2 := mul_le_mul_of_nonneg_left c2 he
  rw [hinner, mul_div_assoc]
  calc |∫ t in -(L / 2)..L / 2, g t * ue z t| ≤ (‖ctr L g z‖ + ‖ctr L g (-z)‖) / 2 :=
        abs_integral_ue_le L hgi z
    _ ≤ _ := by linarith

/-! ### Summability of the `U`-sum on `R₁` -/

/-- **The `U`-sum of a tame class converges**: `Σ_ρ m_ρ⟪w_v, U_ρ⟫²` is summable for `v` tame on `[1/x, 1]`. -/
theorem summable_wv {x : ℕ} (hx0 : (0 : ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_abs_inner_ueVec_le hx0 hv
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (fun ρ => ?_) (Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left (C ^ 2))
  have hm : (0 : ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
  have h := hC _ (Cvs.Zeta.ExplicitFormula.EdgeJumpWindowTests.abs_zPoint_im_le ρ)
  have hre : (Cvs.ZeroCounting.zPoint ρ).re = ((ρ : ℂ)).im := Cvs.ZeroCounting.zPoint_re ρ
  rw [hre] at h
  set γ := ((ρ : ℂ)).im
  have hd : 0 < 1 + |γ| := by positivity
  have hsq : ⟪Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 ≤ C ^ 2 / (1 + |γ|) ^ 2 := by
    rw [← div_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hle : C ^ 2 / (1 + |γ|) ^ 2 ≤ C ^ 2 * (1 / (1 + γ ^ 2)) := by
    rw [mul_one_div]
    refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
    nlinarith [sq_abs γ, abs_nonneg γ]
  calc (Cvs.Criterion.divisorWeight ρ : ℝ) * ⟪Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * (C ^ 2 * (1 / (1 + γ ^ 2))) :=
        mul_le_mul_of_nonneg_left (hsq.trans hle) hm
    _ = _ := by ring

/-- The `U`-sum at a vector `v`, as a predicate. -/
def USummable {x : ℕ} (hx0 : (0 : ℝ) < x) (v : Dom x) : Prop :=
  Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
    * ⟪v, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2

/-- `⟪v + w, u⟫² ≤ 2⟪v, u⟫² + 2⟪w, u⟫²`. -/
theorem sq_inner_add_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w u : E) :
    ⟪v + w, u⟫_ℝ ^ 2 ≤ 2 * ⟪v, u⟫_ℝ ^ 2 + 2 * ⟪w, u⟫_ℝ ^ 2 := by
  rw [inner_add_left]
  nlinarith [sq_nonneg (⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ)]

/-- `USummable` is closed under addition, by `(a + b)² ≤ 2a² + 2b²`. -/
theorem USummable.add {x : ℕ} {hx0 : (0 : ℝ) < x} {v w : Dom x} (hv : USummable hx0 v)
    (hw : USummable hx0 w) : USummable hx0 (v + w) := by
  unfold USummable at *
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (fun ρ => ?_) ((hv.mul_left 2).add (hw.mul_left 2))
  have hm : (0 : ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
  have h := mul_le_mul_of_nonneg_left (sq_inner_add_le v w (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))) hm
  linarith

/-- `USummable` is closed under scalar multiples. -/
theorem USummable.smul {x : ℕ} {hx0 : (0 : ℝ) < x} {v : Dom x} (hv : USummable hx0 v) (c : ℝ) :
    USummable hx0 (c • v) :=
  (hv.mul_left (c ^ 2)).congr fun ρ => by simp only [real_inner_smul_left]; ring

/-- `USummable` at `0`. -/
theorem uSummable_zero {x : ℕ} (hx0 : (0 : ℝ) < x) : USummable hx0 (0 : Dom x) := by
  simp [USummable, summable_zero]

/-- **Each even rung has a summable `U`-sum.** -/
theorem uSummable_rung {x : ℕ} (hx0 : (0 : ℝ) < x) (j : Cvs.Approximant.SpineSubspace.SF x) : USummable hx0 (rung x j) := by
  by_cases hx : 80 ≤ 2 * π * x
  · have h : rung x j = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.StepA.LowEigenvalueCountSpine.tame_evenWin hx (Pi.single j 1)) :=
      Cvs.StepA.LowEigenvalueCountSpine.evenPart_spineMap_eq_wv hx _
    rw [USummable, h]
    exact summable_wv hx0 _
  · have h : rung x j = 0 := by
      rw [Cvs.Approximant.D0FloorEvenRungShare.rung_eq, Cvs.Approximant.SpineSubspace.spineMap, dite_eq_right hx, LinearMap.zero_apply, map_zero]
    rw [h]
    exact uSummable_zero hx0

/-- **Every vector of `R₁` has a summable `U`-sum.** -/
theorem uSummable_of_mem_R1 {x : ℕ} (hx0 : (0 : ℝ) < x) {v : Dom x} (hv : v ∈ R1 x) :
    USummable hx0 v := by
  induction hv using Submodule.span_induction with
  | mem _ h => obtain ⟨j, rfl⟩ := h; exact uSummable_rung hx0 j
  | zero => exact uSummable_zero hx0
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact h.smul c

/-- **Summability at `P_{R₁} b`**: for every `x > 0` and every `b`, `Σ_ρ m_ρ⟪P_{R₁}b, U_ρ⟫²` is summable. -/
theorem summable_starProjection_R1 {x : ℕ} (hx0 : (0 : ℝ) < x) (b : Dom x) :
    Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪(R1 x).starProjection b, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 :=
  uSummable_of_mem_R1 hx0 ((R1 x).starProjection_apply_mem b)

/-- **The summability conjunct of `ShareBessel` at `b⊥`**, at every `x` and so eventually. -/
theorem eventually_summable_bPerp (S : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) :
    ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪(R1 x).starProjection (bPerp hx0 S σ), ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 :=
  Eventually.of_forall fun _ hx0 => summable_starProjection_R1 hx0 _

end Cvs.Route.Visibility.ROneUSumSummable

end
