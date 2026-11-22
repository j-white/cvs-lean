import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.CriticalStripOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundConnesAngle
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.JointGapFloorNearPositivity
import Cvs.Route.JointGapStripLimit
import Cvs.StepA.StepACountDischarged
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The angle bound from a floor and near-positivity; RH ⟺ the angle bound given a floor

The joint gap at `K` bounds the squared sine by `1/K` (`Cvs.Route.JointGapStripLimit.one_sub_inner_sq_le` on the even
subspace). An even form at least `−s` with a floor `μ > q = v⬝Mv` on an even hyperplane gives
`(q + s)/(μ + s)`; under RH `s = 0`, so a floor at Connes' vectors makes RH equivalent to the bound.
-/

noncomputable section

open Filter Matrix
open scoped InnerProductSpace

namespace Cvs.Route.AngleBoundFromFloor
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Limit.SpineWithoutSimplicity (ground groundLam ground_spec)
open Cvs.Route.GroundRouteJointGap (evenSub Meven)
open Cvs.Route.GroundConnesAngle (SinSqClose)

/-- **The angle bound is monotone in its bound.** -/
theorem sinSqClose_mono {P R N : ℕ} {L ε ε' : ℝ} {v : Idx N → ℝ} (h : SinSqClose P R L N ε v)
    (hε : ε ≤ ε') : SinSqClose P R L N ε' v :=
  let ⟨hL, h⟩ := h; ⟨hL, h.trans hε⟩

/-- **The joint gap at `K` bounds the squared sine by `1/K`.** -/
theorem sinSqClose_one_div_of_jointGap {P R N : ℕ} {L K : ℝ} (hK : 0 < K) {v : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hgap : Cvs.Route.GroundRouteJointGap.JointGap P R L N K v) : SinSqClose P R L N (1 / K) v := by
  obtain ⟨hL, μ, kt, hlt, hfloor, hj⟩ := hgap
  obtain ⟨hge, hg1, -, hgeig, -⟩ := ground_spec P R hL N
  have hunit : ∀ f : evenSub N, WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))
      ⬝ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) = 1 → ‖f‖ = 1 := by
    intro f hf
    have h := Cvs.Route.GroundRouteJointGap.norm_sq_evenSub f
    rw [hf] at h
    exact (pow_left_inj₀ (norm_nonneg f) zero_le_one two_ne_zero).mp (by rw [h, one_pow])
  let θ' : evenSub N := ⟨WithLp.toLp 2 (ground P R L hL N), hge⟩
  let v' : evenSub N := ⟨WithLp.toLp 2 v, hve⟩
  let k' : evenSub N := ⟨WithLp.toLp 2 (Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) kt),
    Cvs.Finite.TruncationQuadraticForm.evenPart_even (Cvs.Finite.SymmetricModeSet.negI_involutive N) kt⟩
  have hθeig : Meven P R hL N θ' = groundLam P R L hL N • θ' := by
    refine Subtype.ext (WithLp.ofLp_injective 2 ?_)
    rw [Cvs.Route.GroundRouteJointGap.ofLp_Meven]
    exact hgeig
  have hperp : ∀ f : evenSub N, ⟪k', f⟫_ℝ = 0 →
      μ * ‖f‖ ^ 2 ≤ ⟪Meven P R hL N f, f⟫_ℝ := by
    intro f hf
    rw [Cvs.Route.GroundRouteJointGap.inner_evenSub] at hf
    rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub, Cvs.Route.GroundRouteJointGap.inner_evenSub,
      Cvs.Route.GroundRouteJointGap.ofLp_Meven,
      dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ _)]
    refine hfloor _ f.2 ?_
    rw [← Cvs.Route.GroundRouteJointGap.evenPart_dotProduct (Cvs.Finite.SymmetricModeSet.negI_involutive N) kt f.2]
    exact hf
  have hjoint : K * (⟪Meven P R hL N v', v'⟫_ℝ - groundLam P R L hL N)
      ≤ μ - groundLam P R L hL N := by
    rw [Cvs.Route.GroundRouteJointGap.inner_evenSub, Cvs.Route.GroundRouteJointGap.ofLp_Meven,
      dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ _)]
    exact hj
  have h := Cvs.Route.JointGapStripLimit.one_sub_inner_sq_le (Cvs.Route.GroundRouteJointGap.isSymmetric_Meven P R hL N)
    (hunit θ' hg1) hθeig hlt hperp (hunit v' hv1) hK hjoint
  rw [Cvs.Route.GroundRouteJointGap.inner_evenSub] at h
  refine ⟨hL, ?_⟩
  simpa [θ', v', dotProduct_comm] using h

/-- **The angle bound from a floor and near-positivity**: with the even form at least `−s`, a floor
`μ` on an even hyperplane and `q = v⬝Mv < μ`, the squared sine is at most `(q + s)/(μ + s)`. -/
theorem sinSqClose_of_floor_nearPos {P R N : ℕ} {L μ s : ℝ} (hL : 0 < L) (kt v : Idx N → ℝ)
    (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hneg : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) →
      -s * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hqμ : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) < μ) :
    SinSqClose P R L N
      ((v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) + s) / (μ + s)) v := by
  set q := v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) with hq
  have hqs : 0 ≤ q + s := by
    have h := hneg v hve
    rw [hv1] at h
    linarith
  have hμs : 0 < μ + s := by linarith
  have hJ : ∀ K : ℝ, 1 ≤ K → K * (q + s) ≤ μ + s →
      Cvs.Route.GroundRouteJointGap.JointGap P R L N K v := fun K hK hKμ =>
    Cvs.Route.JointGapFloorNearPositivity.jointGap_of_floor_nearPos hL kt v hve hv1 hfloor hneg hK hqμ
      (by linarith)
  rcases hqs.lt_or_eq with hpos | hzero
  · have hK1 : 1 ≤ (μ + s) / (q + s) := by
      rw [le_div_iff₀ hpos]; linarith
    have hKq : (μ + s) / (q + s) * (q + s) = μ + s := div_mul_cancel₀ _ hpos.ne'
    have h := sinSqClose_one_div_of_jointGap (by linarith) hve hv1 (hJ _ hK1 hKq.le)
    rwa [one_div_div] at h
  · rw [← hzero, zero_div]
    refine ⟨hL, ?_⟩
    by_contra hc
    rw [not_le] at hc
    set t := 1 - (ground P R L hL N ⬝ᵥ v) ^ 2 with ht
    have ht1 : t ≤ 1 := by rw [ht]; nlinarith [sq_nonneg (ground P R L hL N ⬝ᵥ v)]
    have hK1 : 1 ≤ 2 / t := by rw [le_div_iff₀ hc]; linarith
    obtain ⟨_, h⟩ := sinSqClose_one_div_of_jointGap (K := 2 / t) (by positivity)
      hve hv1 (hJ _ hK1 (by rw [← hzero, mul_zero]; exact hμs.le))
    have h' : t ≤ 1 / (2 / t) := h
    rw [one_div_div] at h'
    linarith

/-- **Under RH a floor alone gives the angle bound**: at the canonical truncation the even form is
positive, so a floor `μ > q` on an even hyperplane gives squared sine at most `q/μ`. -/
theorem sinSqClose_of_floor_of_RH (hRH : RiemannHypothesis) {L μ : ℝ} (hL : 0 < L) {N : ℕ}
    (kt v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ f))
    (hqμ : v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v) < μ) :
    SinSqClose ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L N
      (v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v) / μ) v := by
  have hpd := Cvs.StepA.StepACountDischarged.posDef_of_RH hRH hL N
  have hneg : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) →
      -0 * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ f) := by
    intro f _
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    · have h := hpd.dotProduct_mulVec_pos hf
      simp only [star_trivial] at h
      linarith
  have h := sinSqClose_of_floor_nearPos hL kt v hve hv1 hfloor hneg hqμ
  simpa only [add_zero] using h

/-- **The floor at Connes' vector**: an even-hyperplane floor `μ` of the canonical window form with
`K q ≤ μ` and `q < μ`, `q` the Rayleigh value of `v`. -/
def ConnesFloor (L : ℝ) (N : ℕ) (K : ℝ) (v : Idx N → ℝ) : Prop :=
  ∃ (μ : ℝ) (kt : Idx N → ℝ),
    (∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ f)) ∧
    K * (v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v)) ≤ μ ∧
    v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v) < μ

/-- **Under RH the floor at `K` gives the angle bound at `1/K`.** -/
theorem sinSqClose_of_connesFloor_of_RH (hRH : RiemannHypothesis) {L K : ℝ} (hL : 0 < L)
    (hK : 0 < K) {N : ℕ} {v : Idx N → ℝ} (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hF : ConnesFloor L N K v) :
    SinSqClose ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L N (1 / K) v := by
  obtain ⟨μ, kt, hfloor, hKμ, hqμ⟩ := hF
  have hq0 : 0 ≤ v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v) := by
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
    have h := (Cvs.StepA.StepACountDischarged.posDef_of_RH hRH hL N).dotProduct_mulVec_pos hv0
    simp only [star_trivial] at h
    exact h.le
  have hμ : 0 < μ := lt_of_le_of_lt hq0 hqμ
  refine sinSqClose_mono (sinSqClose_of_floor_of_RH hRH hL kt v hve hv1 hfloor hqμ) ?_
  rw [div_le_div_iff₀ hμ hK]
  nlinarith

/-- **RH ⟺ the angle bound, given the floor**: for a truncation eventually at least `⌈x^{1/4}⌉` with
the floor at `K = √x log x` against Connes' vectors for arbitrarily large `x`, RH holds iff the angle
bound at `2/(√x log x)` does for arbitrarily large `x`. -/
theorem riemannHypothesis_iff_frequently_sinSqClose_of_connesFloor (N : ℝ → ℕ)
    (hN : ∀ᶠ x in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x)
    (hF : ∃ᶠ x in atTop, ConnesFloor (Real.log x) (N x) (√x * Real.log x)
      (Cvs.Approximant.ConnesVectorRealScale.connesVec N x)) :
    RiemannHypothesis ↔ ∃ᶠ x in atTop,
      SinSqClose ⌈Real.exp (Real.log x)⌉₊ ⌈Real.log x / Real.log 2⌉₊ (Real.log x) (N x)
        (2 / (√x * Real.log x)) (Cvs.Approximant.ConnesVectorRealScale.connesVec N x) := by
  obtain ⟨hve, hv1, -⟩ := Cvs.Route.JointGapAtConnesVectors.stripApproximable_connesVec_of_threshold_le N hN
  constructor
  · intro hRH
    refine (hF.and_eventually (eventually_gt_atTop 1)).mono fun x hx => ?_
    have hL : 0 < Real.log x := Real.log_pos hx.2
    have hK : 0 < √x * Real.log x := mul_pos (Real.sqrt_pos.mpr (by linarith [hx.2])) hL
    refine sinSqClose_mono (sinSqClose_of_connesFloor_of_RH hRH hL hK (hve x) (hv1 x) hx.1) ?_
    exact div_le_div_of_nonneg_right (by norm_num) hK.le
  · intro h
    exact Cvs.Route.GroundConnesAngle.riemannHypothesis_of_frequently_sinSq_connes_two_div
      (fun x => ⌈Real.exp (Real.log x)⌉₊) (fun x => ⌈Real.log x / Real.log 2⌉₊) ⟨N, hN, h⟩

end Cvs.Route.AngleBoundFromFloor
