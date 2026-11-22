import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Route.GroundRouteJointGap
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.MergedLowerBoundPositivity
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The joint gap from a residual and a codimension-one floor

For a unit trial with Rayleigh value `q < μ`, the residual satisfies
`(q − lam₁)(μ − q) ≤ ‖Tv − qv‖²`; a scaled residual bound supplies the joint gap.
-/

noncomputable section

namespace Cvs.Route.JointGapFromResidual
open Cvs.ZeroCounting

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The shifted product is a residual square plus the shifted quadratic form. -/
theorem shifted_product_eq (T : E →ₗ[ℝ] E) (w : E) (lam μ : ℝ) :
    ⟪T w - lam • w, T w - μ • w⟫_ℝ
      = ‖T w - μ • w‖ ^ 2 + (μ - lam) * (⟪T w, w⟫_ℝ - μ * ‖w‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm w (T w)]
  ring

/-- A symmetric operator with a floor above a unit eigenvector satisfies the sharp Temple product inequality. -/
theorem residual_sq_ge {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {θ v : E} {lam μ : ℝ}
    (hθ : ‖θ‖ = 1) (hθeig : T θ = lam • θ) (hlamμ : lam ≤ μ)
    (hgap : ∀ w : E, ⟪w, θ⟫_ℝ = 0 → μ * ‖w‖ ^ 2 ≤ ⟪T w, w⟫_ℝ)
    (hv : ‖v‖ = 1) :
    (⟪T v, v⟫_ℝ - lam) * (μ - ⟪T v, v⟫_ℝ)
      ≤ ‖T v - ⟪T v, v⟫_ℝ • v‖ ^ 2 := by
  let a : ℝ := ⟪v, θ⟫_ℝ
  let w : E := v - a • θ
  have hθθ : ⟪θ, θ⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hθ]
    norm_num
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hwθ : ⟪w, θ⟫_ℝ = 0 := by
    simp only [w, inner_sub_left, real_inner_smul_left, hθθ, mul_one, a]
    ring
  have hTwθ : ⟪T w, θ⟫_ℝ = 0 := by
    rw [hT w θ, hθeig, real_inner_smul_right, hwθ, mul_zero]
  have hθw : ⟪θ, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hwθ
  have hθTw : ⟪θ, T w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hTwθ
  have hsplit : v = a • θ + w := by
    simp only [w]
    abel
  have hprod : ⟪T v - lam • v, T v - μ • v⟫_ℝ
      = ⟪T w - lam • w, T w - μ • w⟫_ℝ := by
    rw [hsplit]
    simp only [map_add, map_smul, hθeig, smul_add, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hθθ, hwθ, hTwθ, hθw, hθTw]
    ring
  have hnonneg : 0 ≤ ⟪T v - lam • v, T v - μ • v⟫_ℝ := by
    rw [hprod, shifted_product_eq]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (sub_nonneg.mpr hlamμ) (sub_nonneg.mpr (hgap w hwθ)))
  have hprod_expand : ⟪T v - lam • v, T v - μ • v⟫_ℝ
      = ⟪T v, T v⟫_ℝ - (lam + μ) * ⟪T v, v⟫_ℝ + lam * μ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hvv]
    rw [real_inner_comm v (T v)]
    ring
  have hres_expand : ‖T v - ⟪T v, v⟫_ℝ • v‖ ^ 2
      = ⟪T v, T v⟫_ℝ - ⟪T v, v⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hvv]
    rw [real_inner_comm v (T v)]
    ring
  rw [hprod_expand] at hnonneg
  rw [hres_expand]
  nlinarith

/-- A codimension-one floor and a scaled residual bound supply the joint Rayleigh gap without a sign condition on the ground level. -/
theorem joint_of_perp_residual {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {θ kt v : E}
    {lam μ K : ℝ} (hθ : ‖θ‖ = 1) (hθeig : T θ = lam • θ)
    (hlamq : lam ≤ ⟪T v, v⟫_ℝ) (hqμ : ⟪T v, v⟫_ℝ < μ)
    (hperp : ∀ f : E, ⟪kt, f⟫_ℝ = 0 → μ * ‖f‖ ^ 2 ≤ ⟪T f, f⟫_ℝ)
    (hv : ‖v‖ = 1) (hK : 1 ≤ K)
    (hres : (K - 1) * ‖T v - ⟪T v, v⟫_ℝ • v‖ ^ 2 ≤ (μ - ⟪T v, v⟫_ℝ) ^ 2) :
    K * (⟪T v, v⟫_ℝ - lam) ≤ μ - lam := by
  have hθ0 : θ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hθ
    exact zero_ne_one hθ
  have hlamμ : lam < μ := hlamq.trans_lt hqμ
  have hgap := Cvs.Upstream.MergedLowerBoundPositivity.hgap_of_perp hT hθ0 hθeig hlamμ hperp
  have ht := residual_sq_ge hT hθ hθeig hlamμ.le hgap hv
  have hmul := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hK)
  have hδ : 0 < μ - ⟪T v, v⟫_ℝ := sub_pos.mpr hqμ
  have hsharp : (K - 1) * (⟪T v, v⟫_ℝ - lam) ≤ μ - ⟪T v, v⟫_ℝ := by
    apply le_of_mul_le_mul_right _ hδ
    nlinarith [hres]
  linarith

open Matrix
open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive mode_injective)
open Cvs.Limit.SpineWithoutSimplicity (ground groundLam ground_spec)
open Cvs.Route.GroundRouteJointGap (evenSub Meven inner_evenSub norm_sq_evenSub ofLp_Meven isSymmetric_Meven)

/-- The squared coefficient norm of a finite window trial's Rayleigh residual. -/
def residualSq (P R : ℕ) (L : ℝ) (N : ℕ) (v : Idx N → ℝ) : ℝ :=
  let M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)
  let q := v ⬝ᵥ (M *ᵥ v)
  (M *ᵥ v - q • v) ⬝ᵥ (M *ᵥ v - q • v)

/-- An even unit trial below a codimension-one floor supplies `JointGap` when its arithmetic residual satisfies the scaled square bound. -/
theorem jointGap_of_residual {P R N : ℕ} {L K μ : ℝ} (hL : 0 < L)
    (kt v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hqμ : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) < μ) (hK : 1 ≤ K)
    (hres : (K - 1) * residualSq P R L N v
      ≤ (μ - v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v)) ^ 2) :
    Cvs.Route.GroundRouteJointGap.JointGap P R L N K v := by
  obtain ⟨hge, hg1, hgmin, hgeig, -⟩ := ground_spec P R hL N
  have hunit : ∀ f : evenSub N, WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))
      ⬝ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) = 1 → ‖f‖ = 1 := by
    intro f hf
    have h := norm_sq_evenSub f
    rw [hf] at h
    exact (pow_left_inj₀ (norm_nonneg f) zero_le_one two_ne_zero).mp (by rw [h, one_pow])
  let θ' : evenSub N := ⟨WithLp.toLp 2 (ground P R L hL N), hge⟩
  let v' : evenSub N := ⟨WithLp.toLp 2 v, hve⟩
  let k' : evenSub N := ⟨WithLp.toLp 2 (Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) kt),
    Cvs.Finite.TruncationQuadraticForm.evenPart_even (negI_involutive N) kt⟩
  let q := v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v)
  have hq : ⟪Meven P R hL N v', v'⟫_ℝ = q := by
    rw [inner_evenSub, ofLp_Meven, dotProduct_comm]
  have hlamq : groundLam P R L hL N ≤ q := by
    have h := hgmin v hve
    simpa only [hv1, mul_one] using h
  have hθeig : Meven P R hL N θ' = groundLam P R L hL N • θ' := by
    refine Subtype.ext (WithLp.ofLp_injective 2 ?_)
    rw [ofLp_Meven]
    exact hgeig
  have hperp : ∀ f : evenSub N, ⟪k', f⟫_ℝ = 0 →
      μ * ‖f‖ ^ 2 ≤ ⟪Meven P R hL N f, f⟫_ℝ := by
    intro f hf
    rw [inner_evenSub] at hf
    rw [norm_sq_evenSub, inner_evenSub, ofLp_Meven, dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ _)]
    refine hfloor _ f.2 ?_
    rw [← Cvs.Route.GroundRouteJointGap.evenPart_dotProduct (negI_involutive N) kt f.2]
    exact hf
  have hres' : (K - 1) * ‖Meven P R hL N v' - ⟪Meven P R hL N v', v'⟫_ℝ • v'‖ ^ 2
      ≤ (μ - ⟪Meven P R hL N v', v'⟫_ℝ) ^ 2 := by
    rw [hq, norm_sq_evenSub]
    change (K - 1) * residualSq P R L N v ≤ (μ - q) ^ 2
    exact hres
  have hj := joint_of_perp_residual (isSymmetric_Meven P R hL N)
    (hunit θ' hg1) hθeig (by rw [hq]; exact hlamq) (by rw [hq]; exact hqμ)
    hperp (hunit v' hv1) hK hres'
  rw [hq] at hj
  exact ⟨hL, μ, kt, hlamq.trans_lt hqμ, hfloor, hj⟩

end Cvs.Route.JointGapFromResidual
