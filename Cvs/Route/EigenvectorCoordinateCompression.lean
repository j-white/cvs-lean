import Mathlib
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Route.AngleBoundFromFloor
import Cvs.Route.GroundConnesAngle
import Cvs.Route.GroundRouteJointGap
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.QuadrupleParitySectors
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
# The eigenvector coordinate along a unit vector, through the compression to its hyperplane

For symmetric `T`, unit `v`, `C` the compression of `T` to `vᗮ`, `r` the `vᗮ`-part of `T v`
and `T θ = l θ`: `(C − l)(Pθ) = −⟪v, θ⟫ r`, so `⟪v, θ⟫²(1 + ‖(C − l)⁻¹ r‖²) = ‖θ‖²` and
`⟪T v, v⟫ − l = ⟪(C − l)⁻¹ r, r⟫`. On the even window matrix a floor on `vᗮ` above `q` gives
`SinSqClose`, and `SinSqClose` at `ε` gives `ConnesFloor` at `ρ²(1 − ε)/ε`.
-/

noncomputable section

open scoped InnerProductSpace

namespace Cvs.Route.EigenvectorCoordinateCompression
open Cvs.ZeroCounting

/-! ### The compression to a hyperplane -/

section Compression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperplane `vᗮ`. -/
abbrev perp (v : E) : Submodule ℝ E := (ℝ ∙ v)ᗮ

/-- The compression `C = P T P` of `T` to `vᗮ`, `P` the orthogonal projection onto `vᗮ`. -/
def compr (T : E →ₗ[ℝ] E) (v : E) : Module.End ℝ (perp v) :=
  (perp v).orthogonalProjectionOnto.toLinearMap ∘ₗ T ∘ₗ (perp v).subtype

/-- The residual `r = P(T v)`, the part of `T v` in `vᗮ`. -/
def resid (T : E →ₗ[ℝ] E) (v : E) : perp v := (perp v).orthogonalProjectionOnto (T v)

/-- `C y = P(T y)`. -/
theorem compr_apply (T : E →ₗ[ℝ] E) (v : E) (y : perp v) :
    compr T v y = (perp v).orthogonalProjectionOnto (T y) := rfl

/-- A vector of `vᗮ` is orthogonal to `v`. -/
theorem inner_perp (v : E) (y : perp v) : ⟪v, (y : E)⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2

/-- For unit `v`, `r = T v − ⟪v, T v⟫ v`. -/
theorem coe_resid (T : E →ₗ[ℝ] E) {v : E} (hv : ‖v‖ = 1) :
    (resid T v : E) = T v - ⟪v, T v⟫_ℝ • v := by
  rw [resid, Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hv]

/-- `⟪C y, z⟫ = ⟪T y, z⟫` on `vᗮ`. -/
theorem inner_compr (T : E →ₗ[ℝ] E) (v : E) (y z : perp v) :
    ⟪compr T v y, z⟫_ℝ = ⟪T y, (z : E)⟫_ℝ := by
  rw [compr_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

/-- `⟪r, z⟫ = ⟪T v, z⟫` on `vᗮ`. -/
theorem inner_resid (T : E →ₗ[ℝ] E) (v : E) (z : perp v) :
    ⟪resid T v, z⟫_ℝ = ⟪T v, (z : E)⟫_ℝ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right _ _

/-- The compression of a symmetric map is symmetric. -/
theorem isSymmetric_compr {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (v : E) :
    (compr T v).IsSymmetric := by
  intro y z
  rw [real_inner_comm (compr T v z) y, inner_compr, inner_compr, hT]
  exact real_inner_comm _ _

/-- For unit `v`, `θ = ⟪v, θ⟫ v + Pθ`. -/
theorem eq_inner_smul_add {v : E} (hv : ‖v‖ = 1) (θ : E) :
    θ = ⟪v, θ⟫_ℝ • v + ((perp v).orthogonalProjectionOnto θ : E) := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hv]
  abel

/-- For unit `v`, `‖θ‖² = ⟪v, θ⟫² + ‖Pθ‖²`. -/
theorem norm_sq_eq_inner_sq_add {v : E} (hv : ‖v‖ = 1) (θ : E) :
    ‖θ‖ ^ 2 = ⟪v, θ⟫_ℝ ^ 2 + ‖(perp v).orthogonalProjectionOnto θ‖ ^ 2 := by
  conv_lhs => rw [eq_inner_smul_add hv θ]
  rw [norm_add_sq_real, real_inner_smul_left, inner_perp, norm_smul, hv, Real.norm_eq_abs,
    mul_one, sq_abs, Submodule.coe_norm]
  ring

/-- For `u ∈ vᗮ` with `T u = μ u + c v` and unit `v`, `C u = μ u`. -/
theorem compr_eq_smul_of_eq {T : E →ₗ[ℝ] E} {v : E} (hv : ‖v‖ = 1) {u : perp v} {μ c : ℝ}
    (hu : T u = μ • (u : E) + c • v) : compr T v u = μ • u := by
  refine Subtype.ext ?_
  rw [compr_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val, Submodule.starProjection_unit_singleton ℝ hv, hu,
    inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_perp,
    real_inner_self_eq_norm_sq, hv, Submodule.coe_smul]
  module

end Compression

/-! ### The eigenvector equation on the hyperplane -/

section Schur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The eigenvector equation on `vᗮ`**: `T θ = l θ` gives `(C − l)(Pθ) = −⟪v, θ⟫ r`. -/
theorem compr_sub_smul_proj {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ) :
    compr T v ((perp v).orthogonalProjectionOnto θ) - l • (perp v).orthogonalProjectionOnto θ
      = -(⟪v, θ⟫_ℝ • resid T v) := by
  set P := (perp v).orthogonalProjectionOnto
  have h1 : P (T θ) = ⟪v, θ⟫_ℝ • resid T v + compr T v (P θ) := by
    conv_lhs => rw [eq_inner_smul_add hv θ]
    rw [map_add, map_smul, map_add, map_smul]
    rfl
  have h2 : P (T θ) = l • P θ := by rw [hθ, map_smul]
  calc compr T v (P θ) - l • P θ = P (T θ) - ⟪v, θ⟫_ℝ • resid T v - l • P θ := by
        rw [h1]; abel
    _ = -(⟪v, θ⟫_ℝ • resid T v) := by rw [h2]; abel

/-- **The Rayleigh value along `v`**: `T θ = l θ` gives `⟪v, θ⟫(⟪T v, v⟫ − l) = −⟪Pθ, r⟫`. -/
theorem inner_mul_sub_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ) :
    ⟪v, θ⟫_ℝ * (⟪T v, v⟫_ℝ - l) = -⟪(perp v).orthogonalProjectionOnto θ, resid T v⟫_ℝ := by
  have h1 : ⟪θ, T v⟫_ℝ = l * ⟪v, θ⟫_ℝ := by
    rw [← hT, hθ, real_inner_smul_left, real_inner_comm]
  have h2 : ⟪(perp v).orthogonalProjectionOnto θ, resid T v⟫_ℝ
      = ⟪((perp v).orthogonalProjectionOnto θ : E), T v⟫_ℝ :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
  have h3 : ⟪θ, T v⟫_ℝ
      = ⟪v, θ⟫_ℝ * ⟪v, T v⟫_ℝ + ⟪((perp v).orthogonalProjectionOnto θ : E), T v⟫_ℝ := by
    conv_lhs => rw [eq_inner_smul_add hv θ]
    rw [inner_add_left, real_inner_smul_left]
  rw [h2, ← real_inner_comm (T v) v]
  linear_combination h1 - h3

/-- If `l` is not an eigenvalue of `C` and `(C − l) z = r`, then `Pθ = −⟪v, θ⟫ z`. -/
theorem proj_eq_neg_smul {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1) (hθ : T θ = l • θ)
    (hinj : Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l))
    {z : perp v} (hz : compr T v z - l • z = resid T v) :
    (perp v).orthogonalProjectionOnto θ = -(⟪v, θ⟫_ℝ • z) := by
  apply hinj
  simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, map_neg, map_smul]
  rw [compr_sub_smul_proj hv hθ, hz]

/-- If `l` is not an eigenvalue of `C`, an eigenvector `θ ≠ 0` at `l` has `⟪v, θ⟫ ≠ 0`. -/
theorem inner_ne_zero {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1) (hθ : T θ = l • θ)
    (hinj : Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l))
    (hθ0 : θ ≠ 0) : ⟪v, θ⟫_ℝ ≠ 0 := by
  intro ha
  have h := compr_sub_smul_proj hv hθ
  rw [ha, zero_smul, neg_zero] at h
  have hP : (perp v).orthogonalProjectionOnto θ = 0 := hinj (by
    simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, map_zero]
    exact h)
  have hd := eq_inner_smul_add hv θ
  rw [ha, hP, zero_smul, zero_add, Submodule.coe_zero] at hd
  exact hθ0 hd

/-- **The tangent identity**: if `l` is not an eigenvalue of `C` and `(C − l) z = r`, then
`⟪v, θ⟫²(1 + ‖z‖²) = ‖θ‖²`. -/
theorem inner_sq_mul_one_add_norm_sq {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ)
    (hinj : Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l))
    {z : perp v} (hz : compr T v z - l • z = resid T v) :
    ⟪v, θ⟫_ℝ ^ 2 * (1 + ‖z‖ ^ 2) = ‖θ‖ ^ 2 := by
  rw [norm_sq_eq_inner_sq_add hv θ, proj_eq_neg_smul hv hθ hinj hz, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **The Rayleigh identity**: under the hypotheses of the tangent identity and `θ ≠ 0`,
`⟪T v, v⟫ − l = ⟪z, r⟫`. -/
theorem inner_self_sub_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ)
    (hinj : Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l))
    {z : perp v} (hz : compr T v z - l • z = resid T v) (hθ0 : θ ≠ 0) :
    ⟪T v, v⟫_ℝ - l = ⟪z, resid T v⟫_ℝ := by
  have h := inner_mul_sub_eq hT hv hθ
  rw [proj_eq_neg_smul hv hθ hinj hz, inner_neg_left, real_inner_smul_left, neg_neg] at h
  exact mul_left_cancel₀ (inner_ne_zero hv hθ hinj hθ0) h

/-- For a unit eigenvector, `1 − ⟪v, θ⟫² = ‖z‖²/(1 + ‖z‖²)`. -/
theorem one_sub_inner_sq_eq {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1)
    (hθ : T θ = l • θ)
    (hinj : Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l))
    {z : perp v} (hz : compr T v z - l • z = resid T v) :
    1 - ⟪v, θ⟫_ℝ ^ 2 = ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) := by
  have h := inner_sq_mul_one_add_norm_sq hv hθ hinj hz
  rw [hθ1, one_pow] at h
  rw [eq_div_iff (by positivity)]
  linear_combination -h

/-! ### The resolvent form -/

/-- The Schur vector `(C − l)⁻¹ r`. -/
def schurVec (T : E →ₗ[ℝ] E) (v : E) (l : ℝ) : perp v :=
  Ring.inverse (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l) (resid T v)

/-- Outside the spectrum of `C`, `C − l` is a unit. -/
theorem isUnit_compr_sub {T : E →ₗ[ℝ] E} {v : E} {l : ℝ} (hl : l ∉ spectrum ℝ (compr T v)) :
    IsUnit (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l) := by
  have h := (spectrum.notMem_iff.mp hl).neg
  rwa [neg_sub] at h

/-- Outside the spectrum of `C`, `C − l` is injective. -/
theorem injective_compr_sub {T : E →ₗ[ℝ] E} {v : E} {l : ℝ} (hl : l ∉ spectrum ℝ (compr T v)) :
    Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l) :=
  ((Module.End.isUnit_iff _).mp (isUnit_compr_sub hl)).1

/-- Outside the spectrum of `C`, `(C − l)(C − l)⁻¹ r = r`. -/
theorem compr_sub_smul_schurVec {T : E →ₗ[ℝ] E} {v : E} {l : ℝ}
    (hl : l ∉ spectrum ℝ (compr T v)) :
    compr T v (schurVec T v l) - l • schurVec T v l = resid T v := by
  have h := congrArg (fun f : Module.End ℝ (perp v) => f (resid T v))
    (Ring.mul_inverse_cancel _ (isUnit_compr_sub hl))
  simpa [schurVec, Module.algebraMap_end_apply] using h

/-- **The Schur identity**: for `l` outside the spectrum of `C`, `Pθ = −⟪v, θ⟫ (C − l)⁻¹ r`. -/
theorem proj_eq_neg_smul_schurVec {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ) (hl : l ∉ spectrum ℝ (compr T v)) :
    (perp v).orthogonalProjectionOnto θ = -(⟪v, θ⟫_ℝ • schurVec T v l) :=
  proj_eq_neg_smul hv hθ (injective_compr_sub hl) (compr_sub_smul_schurVec hl)

/-- **The tangent identity**: for `l` outside the spectrum of `C`,
`⟪v, θ⟫²(1 + ‖(C − l)⁻¹ r‖²) = ‖θ‖²`. -/
theorem inner_sq_mul_one_add_norm_sq_schurVec {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ) (hl : l ∉ spectrum ℝ (compr T v)) :
    ⟪v, θ⟫_ℝ ^ 2 * (1 + ‖schurVec T v l‖ ^ 2) = ‖θ‖ ^ 2 :=
  inner_sq_mul_one_add_norm_sq hv hθ (injective_compr_sub hl) (compr_sub_smul_schurVec hl)

/-- **The tangent identity, normalised**: for `θ ≠ 0` and `l` outside the spectrum of `C`,
`⟪v, θ⟫² ‖θ‖⁻² (1 + ‖(C − l)⁻¹ r‖²) = 1`. -/
theorem inner_sq_mul_inv_mul_eq_one {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ : T θ = l • θ) (hl : l ∉ spectrum ℝ (compr T v)) (hθ0 : θ ≠ 0) :
    ⟪v, θ⟫_ℝ ^ 2 * (‖θ‖ ^ 2)⁻¹ * (1 + ‖schurVec T v l‖ ^ 2) = 1 := by
  have h := inner_sq_mul_one_add_norm_sq_schurVec hv hθ hl
  have hθn : ‖θ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hθ0)
  rw [mul_right_comm, h, mul_inv_cancel₀ hθn]

/-- **The Rayleigh identity**: for `θ ≠ 0` and `l` outside the spectrum of `C`,
`⟪T v, v⟫ − l = ⟪(C − l)⁻¹ r, r⟫`. -/
theorem inner_self_sub_eq_schurVec {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E} {l : ℝ}
    (hv : ‖v‖ = 1) (hθ : T θ = l • θ) (hl : l ∉ spectrum ℝ (compr T v)) (hθ0 : θ ≠ 0) :
    ⟪T v, v⟫_ℝ - l = ⟪schurVec T v l, resid T v⟫_ℝ :=
  inner_self_sub_eq hT hv hθ (injective_compr_sub hl) (compr_sub_smul_schurVec hl) hθ0

/-- For a unit eigenvector at `l` outside the spectrum of `C`,
`1 − ⟪v, θ⟫² = ‖(C − l)⁻¹ r‖²/(1 + ‖(C − l)⁻¹ r‖²)`. -/
theorem one_sub_inner_sq_eq_schurVec {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1)
    (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ) (hl : l ∉ spectrum ℝ (compr T v)) :
    1 - ⟪v, θ⟫_ℝ ^ 2 = ‖schurVec T v l‖ ^ 2 / (1 + ‖schurVec T v l‖ ^ 2) :=
  one_sub_inner_sq_eq hv hθ1 hθ (injective_compr_sub hl) (compr_sub_smul_schurVec hl)

/-- **The angle**: for `θ ≠ 0` at `l` outside the spectrum of `C`,
`tan² ∠(v, θ) = ‖(C − l)⁻¹ r‖²`. -/
theorem tan_angle_sq {T : E →ₗ[ℝ] E} {v θ : E} {l : ℝ} (hv : ‖v‖ = 1) (hθ : T θ = l • θ)
    (hl : l ∉ spectrum ℝ (compr T v)) (hθ0 : θ ≠ 0) :
    Real.tan (InnerProductGeometry.angle v θ) ^ 2 = ‖schurVec T v l‖ ^ 2 := by
  have h := inner_sq_mul_one_add_norm_sq_schurVec hv hθ hl
  have ha := inner_ne_zero hv hθ (injective_compr_sub hl) hθ0
  have hθn : ‖θ‖ ≠ 0 := norm_ne_zero_iff.mpr hθ0
  have hc : Real.cos (InnerProductGeometry.angle v θ) = ⟪v, θ⟫_ℝ / ‖θ‖ := by
    rw [InnerProductGeometry.cos_angle, hv, one_mul]
  have hs : Real.sin (InnerProductGeometry.angle v θ) ^ 2 = 1 - (⟪v, θ⟫_ℝ / ‖θ‖) ^ 2 := by
    rw [← hc, ← Real.sin_sq_add_cos_sq (InnerProductGeometry.angle v θ)]
    ring
  rw [Real.tan_eq_sin_div_cos, div_pow, hs, hc]
  field_simp
  linear_combination -h

end Schur

/-! ### A floor on the hyperplane -/

section Floor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A floor `μ` of `T` on `vᗮ` gives `(μ − l)‖y‖² ≤ ⟪y, (C − l) y⟫` on `vᗮ`. -/
theorem sub_mul_norm_sq_le_inner {T : E →ₗ[ℝ] E} {v : E} {l μ : ℝ}
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) (y : perp v) :
    (μ - l) * ‖y‖ ^ 2 ≤ ⟪y, compr T v y - l • y⟫_ℝ := by
  have h := hfloor y
  rw [inner_sub_right, real_inner_smul_right, real_inner_comm, inner_compr,
    real_inner_self_eq_norm_sq]
  linarith

/-- A floor `μ > l` of `T` on `vᗮ` makes `C − l` injective. -/
theorem injective_of_floor {T : E →ₗ[ℝ] E} {v : E} {l μ : ℝ}
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) (hlμ : l < μ) :
    Function.Injective (compr T v - algebraMap ℝ (Module.End ℝ (perp v)) l) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hy' : compr T v y - l • y = 0 := by
    simpa only [LinearMap.sub_apply, Module.algebraMap_end_apply] using hy
  have h := sub_mul_norm_sq_le_inner (l := l) hfloor y
  rw [hy', inner_zero_right] at h
  have hn : ‖y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖y‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hn (sq_nonneg _)))

/-- In finite dimension a floor `μ > l` of `T` on `vᗮ` puts `l` outside the spectrum of `C`. -/
theorem notMem_spectrum_of_floor [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {v : E} {l μ : ℝ}
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) (hlμ : l < μ) :
    l ∉ spectrum ℝ (compr T v) := by
  rw [spectrum.notMem_iff]
  have hinj := injective_of_floor hfloor hlμ
  have hu := (Module.End.isUnit_iff _).mpr ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have h := hu.neg
  rwa [neg_sub] at h

/-- **The tangent bound from a floor**: for symmetric `T`, a floor `μ` of `T` on `vᗮ` and
`T θ = l θ`, `(μ − l)(‖θ‖² − ⟪v, θ⟫²) ≤ ⟪v, θ⟫²(⟪T v, v⟫ − l)`. -/
theorem sub_mul_le_inner_sq_mul {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E} {l μ : ℝ}
    (hv : ‖v‖ = 1) (hθ : T θ = l • θ)
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) :
    (μ - l) * (‖θ‖ ^ 2 - ⟪v, θ⟫_ℝ ^ 2) ≤ ⟪v, θ⟫_ℝ ^ 2 * (⟪T v, v⟫_ℝ - l) := by
  have h := sub_mul_norm_sq_le_inner (l := l) hfloor ((perp v).orthogonalProjectionOnto θ)
  rw [compr_sub_smul_proj hv hθ, inner_neg_right, real_inner_smul_right] at h
  have hR := inner_mul_sub_eq hT hv hθ
  have key : -(⟪v, θ⟫_ℝ * ⟪(perp v).orthogonalProjectionOnto θ, resid T v⟫_ℝ)
      = ⟪v, θ⟫_ℝ ^ 2 * (⟪T v, v⟫_ℝ - l) := by
    linear_combination (-⟪v, θ⟫_ℝ) * hR
  have hN : ‖θ‖ ^ 2 - ⟪v, θ⟫_ℝ ^ 2 = ‖(perp v).orthogonalProjectionOnto θ‖ ^ 2 := by
    rw [norm_sq_eq_inner_sq_add hv θ]; ring
  rw [hN, ← key]
  exact h

/-- For a floor `μ` of `T` on `vᗮ` and `(C − l) z = r`, `(μ − l)‖z‖² ≤ ⟪z, r⟫`. -/
theorem sub_mul_norm_sq_le_inner_resid {T : E →ₗ[ℝ] E} {v : E} {l μ : ℝ}
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) {z : perp v}
    (hz : compr T v z - l • z = resid T v) :
    (μ - l) * ‖z‖ ^ 2 ≤ ⟪z, resid T v⟫_ℝ := by
  have h := sub_mul_norm_sq_le_inner (l := l) hfloor z
  rwa [hz] at h

/-- **Comparison of Schur vectors**: for a floor `μ` of `T` on `vᗮ`, `l ≤ l' < μ` and
`(C − l) z = (C − l') w`, `‖z‖ ≤ ‖w‖`. -/
theorem norm_le_norm_of_floor {T : E →ₗ[ℝ] E} {v : E} {l l' μ : ℝ}
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) (hll' : l ≤ l') (hl'μ : l' < μ)
    {z w : perp v} (hzw : compr T v z - l • z = compr T v w - l' • w) : ‖z‖ ≤ ‖w‖ := by
  set d := w - z with hd
  have hCd : compr T v d - l' • d = (l' - l) • z := by
    rw [hd, map_sub, smul_sub, sub_smul]
    linear_combination (norm := module) -hzw
  have h := sub_mul_norm_sq_le_inner (l := l') hfloor d
  rw [hCd, real_inner_smul_right] at h
  have hw : w = z + d := by rw [hd]; abel
  have hsq : ‖w‖ ^ 2 = ‖z‖ ^ 2 + 2 * ⟪z, d⟫_ℝ + ‖d‖ ^ 2 := by rw [hw, norm_add_sq_real]
  have hkey : 0 ≤ 2 * ⟪z, d⟫_ℝ + ‖d‖ ^ 2 := by
    rcases hll'.lt_or_eq with hlt | heq
    · have h0 : 0 ≤ (l' - l) * ⟪d, z⟫_ℝ :=
        le_trans (mul_nonneg (by linarith) (sq_nonneg _)) h
      have hzd : 0 ≤ ⟪d, z⟫_ℝ := by
        by_contra hneg
        nlinarith [not_le.mp hneg]
      rw [real_inner_comm]
      nlinarith [sq_nonneg ‖d‖]
    · rw [heq, sub_self, zero_mul] at h
      have hd0 : ‖d‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖d‖]
      have hd0' : d = 0 :=
        norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hd0 (sq_nonneg _)))
      rw [hd0', inner_zero_right, norm_zero]
      norm_num
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

/-- **A floor on `vᗮ` above `q` bounds the angle**: in finite dimension, for a floor
`μ > q = ⟪T v, v⟫` of `T` on `vᗮ` and a unit eigenvector `θ` at `l ≤ q`,
`1 − ⟪v, θ⟫² ≤ ‖(C − q)⁻¹ r‖²/(1 + ‖(C − q)⁻¹ r‖²)`. -/
theorem one_sub_inner_sq_le_floorPerp [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {v θ : E}
    {l μ : ℝ} (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ)
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) (hlq : l ≤ ⟪T v, v⟫_ℝ)
    (hqμ : ⟪T v, v⟫_ℝ < μ) :
    1 - ⟪v, θ⟫_ℝ ^ 2
      ≤ ‖schurVec T v ⟪T v, v⟫_ℝ‖ ^ 2 / (1 + ‖schurVec T v ⟪T v, v⟫_ℝ‖ ^ 2) := by
  have hl := notMem_spectrum_of_floor hfloor (hlq.trans_lt hqμ)
  have hq := notMem_spectrum_of_floor hfloor hqμ
  rw [one_sub_inner_sq_eq_schurVec hv hθ1 hθ hl]
  have hle : ‖schurVec T v l‖ ≤ ‖schurVec T v ⟪T v, v⟫_ℝ‖ :=
    norm_le_norm_of_floor hfloor hlq hqμ
      (by rw [compr_sub_smul_schurVec hl, compr_sub_smul_schurVec hq])
  have h2 : ‖schurVec T v l‖ ^ 2 ≤ ‖schurVec T v ⟪T v, v⟫_ℝ‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **A floor on `vᗮ` above `q` bounds the angle** by `ε`: under the hypotheses of
`one_sub_inner_sq_le_floorPerp`, `‖(C − q)⁻¹ r‖² ≤ ε/(1 − ε)` with `ε < 1` gives
`1 − ⟪v, θ⟫² ≤ ε`. -/
theorem one_sub_inner_sq_le_of_floorPerp [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {v θ : E}
    {l μ ε : ℝ} (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ)
    (hfloor : ∀ y : perp v, μ * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ) (hlq : l ≤ ⟪T v, v⟫_ℝ)
    (hqμ : ⟪T v, v⟫_ℝ < μ) (hε1 : ε < 1)
    (hfp : ‖schurVec T v ⟪T v, v⟫_ℝ‖ ^ 2 ≤ ε / (1 - ε)) :
    1 - ⟪v, θ⟫_ℝ ^ 2 ≤ ε := by
  refine (one_sub_inner_sq_le_floorPerp hv hθ1 hθ hfloor hlq hqμ).trans ?_
  set x := ‖schurVec T v ⟪T v, v⟫_ℝ‖ ^ 2
  have hx : 0 ≤ x := sq_nonneg _
  rw [le_div_iff₀ (by linarith)] at hfp
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Floor

/-! ### An eigenvector of the compression -/

section Overlap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The coordinate on an eigenvector of `C`**: for symmetric `T`, `T θ = l θ` and `C u = μ u`,
`⟪v, θ⟫⟪u, r⟫ = −(μ − l)⟪u, Pθ⟫`. -/
theorem inner_mul_inner_resid_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E} {l μ : ℝ}
    (hv : ‖v‖ = 1) (hθ : T θ = l • θ) {u : perp v} (hu : compr T v u = μ • u) :
    ⟪v, θ⟫_ℝ * ⟪u, resid T v⟫_ℝ = -((μ - l) * ⟪u, (perp v).orthogonalProjectionOnto θ⟫_ℝ) := by
  have h := congrArg (fun y => ⟪u, y⟫_ℝ) (compr_sub_smul_proj hv hθ)
  simp only [inner_sub_right, inner_neg_right, real_inner_smul_right] at h
  rw [← isSymmetric_compr hT v, hu, real_inner_smul_left] at h
  linear_combination h

/-- **The overlap bound**: for symmetric `T`, `T θ = l θ` and `C u = μ u`,
`⟪v, θ⟫²⟪u, r⟫² ≤ (μ − l)²‖u‖²(‖θ‖² − ⟪v, θ⟫²)`. -/
theorem inner_sq_mul_inner_resid_sq_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E}
    {l μ : ℝ} (hv : ‖v‖ = 1) (hθ : T θ = l • θ) {u : perp v} (hu : compr T v u = μ • u) :
    ⟪v, θ⟫_ℝ ^ 2 * ⟪u, resid T v⟫_ℝ ^ 2
      ≤ (μ - l) ^ 2 * ‖u‖ ^ 2 * (‖θ‖ ^ 2 - ⟪v, θ⟫_ℝ ^ 2) := by
  have h := inner_mul_inner_resid_eq hT hv hθ hu
  have hN := norm_sq_eq_inner_sq_add hv θ
  have hcs := real_inner_mul_inner_self_le u ((perp v).orthogonalProjectionOnto θ)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hsq : ⟪v, θ⟫_ℝ ^ 2 * ⟪u, resid T v⟫_ℝ ^ 2
      = (μ - l) ^ 2 * (⟪u, (perp v).orthogonalProjectionOnto θ⟫_ℝ
        * ⟪u, (perp v).orthogonalProjectionOnto θ⟫_ℝ) := by
    rw [← mul_pow, h]; ring
  rw [hsq, hN, add_sub_cancel_left, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)

/-- **The angle condition forces a floor**: for symmetric `T`, a unit eigenvector `θ` at `l`, a
unit `u` with `C u = μ u` and `1 − ⟪v, θ⟫² ≤ ε`, `(1 − ε)⟪u, r⟫² ≤ ε(μ − l)²`. -/
theorem one_sub_mul_inner_resid_sq_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E}
    {l μ ε : ℝ} (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ) {u : perp v}
    (hu1 : ‖u‖ = 1) (hu : compr T v u = μ • u) (hε : 1 - ⟪v, θ⟫_ℝ ^ 2 ≤ ε) :
    (1 - ε) * ⟪u, resid T v⟫_ℝ ^ 2 ≤ ε * (μ - l) ^ 2 := by
  have h := inner_sq_mul_inner_resid_sq_le hT hv hθ hu
  rw [hθ1, hu1, one_pow, mul_one] at h
  have h1 : (1 - ε) * ⟪u, resid T v⟫_ℝ ^ 2 ≤ ⟪v, θ⟫_ℝ ^ 2 * ⟪u, resid T v⟫_ℝ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h2 : (μ - l) ^ 2 * (1 - ⟪v, θ⟫_ℝ ^ 2) ≤ (μ - l) ^ 2 * ε :=
    mul_le_mul_of_nonneg_left hε (sq_nonneg _)
  linarith

/-- From `(1 − ε)a² ≤ ε(μ − l)²` with `0 ≤ l ≤ μ`, `0 < μ`, `0 < q` and `0 < ε`:
`a²/(μ q) · (1 − ε)/ε · q ≤ μ`. -/
theorem rho_sq_mul_le_of {a l μ q ε : ℝ} (h : (1 - ε) * a ^ 2 ≤ ε * (μ - l) ^ 2) (hl0 : 0 ≤ l)
    (hlμ : l ≤ μ) (hμ : 0 < μ) (hq : 0 < q) (hε0 : 0 < ε) :
    a ^ 2 / (μ * q) * ((1 - ε) / ε) * q ≤ μ := by
  have hsq : (μ - l) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h' : (1 - ε) * a ^ 2 ≤ ε * μ ^ 2 := h.trans (mul_le_mul_of_nonneg_left hsq hε0.le)
  have hlhs : a ^ 2 / (μ * q) * ((1 - ε) / ε) * q = (1 - ε) * a ^ 2 / (ε * μ) := by
    field_simp
  rw [hlhs, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The angle condition forces a floor**, in the paper's normalisation: with `0 ≤ l < μ`,
`q = ⟪T v, v⟫ > 0`, `0 < ε` and `ρ² = ⟪u, r⟫²/(μ q)`, `ρ²(1 − ε)/ε · q ≤ μ`. -/
theorem rho_sq_mul_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v θ : E} {l μ ε : ℝ}
    (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ) {u : perp v} (hu1 : ‖u‖ = 1)
    (hu : compr T v u = μ • u) (hl0 : 0 ≤ l) (hlμ : l < μ) (hq : 0 < ⟪T v, v⟫_ℝ) (hε0 : 0 < ε)
    (hε : 1 - ⟪v, θ⟫_ℝ ^ 2 ≤ ε) :
    ⟪u, resid T v⟫_ℝ ^ 2 / (μ * ⟪T v, v⟫_ℝ) * ((1 - ε) / ε) * ⟪T v, v⟫_ℝ ≤ μ := by
  exact rho_sq_mul_le_of (one_sub_mul_inner_resid_sq_le hT hv hθ1 hθ hu1 hu hε) hl0 hlμ.le
    (hl0.trans_lt hlμ) hq hε0

end Overlap

/-! ### Positive maps -/

section Positive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cauchy–Schwarz for a positive map**: `⟪u, T w⟫² ≤ ⟪T u, u⟫⟪T w, w⟫`. -/
theorem inner_sq_le_of_isPositive {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (u w : E) :
    ⟪u, T w⟫_ℝ ^ 2 ≤ ⟪T u, u⟫_ℝ * ⟪T w, w⟫_ℝ := by
  have hd := discrim_le_zero (a := ⟪T w, w⟫_ℝ) (b := 2 * ⟪u, T w⟫_ℝ) (c := ⟪T u, u⟫_ℝ)
    fun t => by
      have h := hT.inner_nonneg_left (u + t • w)
      have hs : ⟪T u, w⟫_ℝ = ⟪u, T w⟫_ℝ := hT.isSymmetric u w
      have hc : ⟪T w, u⟫_ℝ = ⟪u, T w⟫_ℝ := real_inner_comm _ _
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hs, hc] at h
      linarith
  rw [discrim] at hd
  nlinarith

/-- For positive `T` and `⟪T u, u⟫ = μ‖u‖²`, `⟪u, T w⟫² ≤ μ‖u‖²⟪T w, w⟫`. -/
theorem inner_sq_le_of_rayleigh {T : E →ₗ[ℝ] E} (hT : T.IsPositive) {u : E} {μ : ℝ}
    (hu : ⟪T u, u⟫_ℝ = μ * ‖u‖ ^ 2) (w : E) :
    ⟪u, T w⟫_ℝ ^ 2 ≤ μ * ‖u‖ ^ 2 * ⟪T w, w⟫_ℝ := by
  rw [← hu]
  exact inner_sq_le_of_isPositive hT u w

/-- **The overlap is at most one**: for positive `T` and `C u = μ u`, `⟪u, r⟫² ≤ μ‖u‖²⟪T v, v⟫`. -/
theorem inner_resid_sq_le {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (v : E) {u : perp v} {μ : ℝ}
    (hu : compr T v u = μ • u) :
    ⟪u, resid T v⟫_ℝ ^ 2 ≤ μ * ‖u‖ ^ 2 * ⟪T v, v⟫_ℝ := by
  have hr : ⟪u, resid T v⟫_ℝ = ⟪(u : E), T v⟫_ℝ := by
    rw [real_inner_comm, inner_resid, real_inner_comm]
  have hTu : ⟪T u, (u : E)⟫_ℝ = μ * ‖(u : E)‖ ^ 2 := by
    rw [← inner_compr, hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rfl
  rw [hr]
  exact inner_sq_le_of_rayleigh hT hTu v

end Positive

/-! ### The even window matrix -/

section Window

open Matrix
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Limit.SpineWithoutSimplicity (ground groundLam ground_spec)
open Cvs.Route.GroundRouteJointGap (evenSub Meven)
open Cvs.Route.GroundConnesAngle (SinSqClose)

/-- `⌈log x / log 2⌉₊ = ⌈log₂ x⌉` for every natural `x`. -/
theorem natCeil_log_div_log_two_eq_clog (x : ℕ) : ⌈Real.log x / Real.log 2⌉₊ = Nat.clog 2 x := by
  have h := Real.natCeil_logb_natCast 2 x
  simpa [Real.logb] using h

/-- At `L = log x` the canonical matrix is `Cvs.Finite.TruncationQuadraticForm.M x ⌈log₂ x⌉ (log x)`. -/
theorem MX_log_natCast {x : ℕ} (hx : 0 < x) (N : ℕ) :
    Cvs.Finite.ParitySectorDefect.MX (Real.log x) N
      = Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) := by
  rw [Cvs.Finite.ParitySectorDefect.MX, Cvs.StepA.OddBottomGapCriterion.ceil_exp_log_natCast hx,
    natCeil_log_div_log_two_eq_clog]

/-- An even vector on `Idx N` as an element of the even sector. -/
def evenVec {N : ℕ} {v : Idx N → ℝ} (hve : ∀ i, v (negI N i) = v i) : evenSub N :=
  ⟨WithLp.toLp 2 v, hve⟩

/-- `⟪evenVec f, evenVec g⟫ = f⬝g`. -/
theorem inner_evenVec {N : ℕ} {f g : Idx N → ℝ} (hf : ∀ i, f (negI N i) = f i)
    (hg : ∀ i, g (negI N i) = g i) : ⟪evenVec hf, evenVec hg⟫_ℝ = f ⬝ᵥ g := by
  rw [Cvs.Route.GroundRouteJointGap.inner_evenSub]
  rfl

/-- A unit even vector is a unit vector of the even sector. -/
theorem norm_evenVec {N : ℕ} {v : Idx N → ℝ} (hve : ∀ i, v (negI N i) = v i)
    (hv1 : v ⬝ᵥ v = 1) : ‖evenVec hve‖ = 1 := by
  have h : ‖evenVec hve‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_evenVec, hv1]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by rw [h, one_pow])

/-- `⟪Meven v, v⟫ = v⬝Mv` on an even vector. -/
theorem inner_Meven_evenVec (P R : ℕ) {L : ℝ} (hL : 0 < L) {N : ℕ} {v : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i) :
    ⟪Meven P R hL N (evenVec hve), evenVec hve⟫_ℝ
      = v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) := by
  rw [Cvs.Route.GroundRouteJointGap.inner_evenSub, Cvs.Route.GroundRouteJointGap.ofLp_Meven, dotProduct_comm]
  rfl

/-- The ground state is an eigenvector of the even compression `Meven` at `λ₁`. -/
theorem Meven_ground (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Meven P R hL N (evenVec (ground_spec P R hL N).1)
      = groundLam P R L hL N • evenVec (ground_spec P R hL N).1 :=
  Subtype.ext (WithLp.ofLp_injective 2 (by
    rw [Cvs.Route.GroundRouteJointGap.ofLp_Meven]
    exact (ground_spec P R hL N).2.2.2.1))

/-- An even floor on `vᗮ` in matrix form is a floor of `Meven` on the hyperplane of `evenVec v`. -/
theorem floor_of_dotProduct {P R N : ℕ} {L μ : ℝ} (hL : 0 < L) {v : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → v ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (y : perp (evenVec hve)) :
    μ * ‖y‖ ^ 2 ≤ ⟪Meven P R hL N (y : evenSub N), (y : evenSub N)⟫_ℝ := by
  have hvf : v ⬝ᵥ WithLp.ofLp ((y : evenSub N) : EuclideanSpace ℝ (Idx N)) = 0 := by
    have h := inner_perp (evenVec hve) y
    rw [Cvs.Route.GroundRouteJointGap.inner_evenSub] at h
    exact h
  have h := hfloor _ (y : evenSub N).2 hvf
  rw [show ‖y‖ ^ 2 = ‖(y : evenSub N)‖ ^ 2 from rfl, Cvs.Route.GroundRouteJointGap.norm_sq_evenSub,
    Cvs.Route.GroundRouteJointGap.inner_evenSub, Cvs.Route.GroundRouteJointGap.ofLp_Meven]
  exact h.trans_eq (dotProduct_comm _ _)

/-- **A floor on `vᗮ` above `q` gives the angle bound**: for unit even `v`, `q = v⬝Mv` and an even
floor `μ > q` on `vᗮ`, `SinSqClose` holds at `‖(C − q)⁻¹ r‖²/(1 + ‖(C − q)⁻¹ r‖²)` in `Meven`. -/
theorem sinSqClose_floorPerp {P R N : ℕ} {L μ : ℝ} (hL : 0 < L) {v : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → v ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hqμ : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) < μ) :
    SinSqClose P R L N
      (‖schurVec (Meven P R hL N) (evenVec hve)
          (v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))‖ ^ 2
        / (1 + ‖schurVec (Meven P R hL N) (evenVec hve)
          (v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))‖ ^ 2)) v := by
  obtain ⟨hge, hg1, hmin, -, -⟩ := ground_spec P R hL N
  have hlq : groundLam P R L hL N ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) := by
    have h := hmin v hve
    rwa [hv1, mul_one] at h
  have hq := inner_Meven_evenVec P R hL hve
  have h := one_sub_inner_sq_le_floorPerp (norm_evenVec hve hv1) (norm_evenVec hge hg1)
    (Meven_ground P R hL N) (floor_of_dotProduct hL hve hfloor) (by rwa [hq]) (by rwa [hq])
  rw [hq, inner_evenVec, dotProduct_comm] at h
  exact ⟨hL, h⟩

/-- **A floor on `vᗮ` above `q` gives the angle bound** at `ε`: under the hypotheses of
`sinSqClose_floorPerp`, `‖(C − q)⁻¹ r‖² ≤ ε/(1 − ε)` with `ε < 1` gives `SinSqClose` at `ε`. -/
theorem sinSqClose_of_floorPerp {P R N : ℕ} {L μ ε : ℝ} (hL : 0 < L) {v : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → v ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hqμ : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) < μ) (hε1 : ε < 1)
    (hfp : ‖schurVec (Meven P R hL N) (evenVec hve)
      (v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))‖ ^ 2 ≤ ε / (1 - ε)) :
    SinSqClose P R L N ε v := by
  obtain ⟨hL', h⟩ := sinSqClose_floorPerp hL hve hv1 hfloor hqμ
  refine ⟨hL', h.trans ?_⟩
  set x := ‖schurVec (Meven P R hL N) (evenVec hve)
    (v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))‖ ^ 2
  have hx : 0 ≤ x := sq_nonneg _
  rw [le_div_iff₀ (by linarith)] at hfp
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The angle bound forces a floor**: for unit even `v`, unit even `u ⟂ v` with
`M u = μ u + c v` and `SinSqClose` at `ε`, `(1 − ε)(u⬝Mv)² ≤ ε(μ − λ₁)²`. -/
theorem one_sub_mul_sq_le_of_sinSqClose {P R N : ℕ} {L μ c ε : ℝ} (hL : 0 < L)
    {v u : Idx N → ℝ} (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hue : ∀ i, u (negI N i) = u i) (hu1 : u ⬝ᵥ u = 1) (huv : v ⬝ᵥ u = 0)
    (hu : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u = μ • u + c • v)
    (hS : SinSqClose P R L N ε v) :
    (1 - ε) * (u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v)) ^ 2
      ≤ ε * (μ - groundLam P R L hL N) ^ 2 := by
  obtain ⟨hge, hg1, -, -, -⟩ := ground_spec P R hL N
  obtain ⟨hL', hε⟩ := hS
  have hmem : evenVec hue ∈ perp (evenVec hve) := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_evenVec]
    exact huv
  set u' : perp (evenVec hve) := ⟨evenVec hue, hmem⟩
  have hu' : compr (Meven P R hL N) (evenVec hve) u' = μ • u' := by
    refine compr_eq_smul_of_eq (c := c) (norm_evenVec hve hv1) ?_
    refine Subtype.ext (WithLp.ofLp_injective 2 ?_)
    rw [Cvs.Route.GroundRouteJointGap.ofLp_Meven]
    exact hu
  have hu'1 : ‖u'‖ = 1 := norm_evenVec hue hu1
  have h := one_sub_mul_inner_resid_sq_le (Cvs.Route.GroundRouteJointGap.isSymmetric_Meven P R hL N)
    (norm_evenVec hve hv1) (norm_evenVec hge hg1) (Meven_ground P R hL N) hu'1 hu'
    (ε := ε) (by rw [inner_evenVec, dotProduct_comm]; exact hε)
  have hr : ⟪u', resid (Meven P R hL N) (evenVec hve)⟫_ℝ
      = u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) := by
    rw [real_inner_comm, inner_resid, Cvs.Route.GroundRouteJointGap.inner_evenSub,
      Cvs.Route.GroundRouteJointGap.ofLp_Meven, dotProduct_comm]
    rfl
  rwa [hr] at h

/-- **The angle bound forces Connes' floor**: for unit even `v`, `q = v⬝MXv > 0`, an even floor
`μ > q` on `vᗮ`, unit even `u ⟂ v` with `MX u = μ u + c v`, `0 ≤ λ₁` and `SinSqClose` at `ε > 0`,
`ConnesFloor` holds at `ρ²(1 − ε)/ε`, `ρ² = (u⬝MXv)²/(μ q)`. -/
theorem connesFloor_of_sinSqClose {L μ c ε : ℝ} (hL : 0 < L) {N : ℕ} {v u : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hue : ∀ i, u (negI N i) = u i) (hu1 : u ⬝ᵥ u = 1) (huv : v ⬝ᵥ u = 0)
    (hu : Cvs.Finite.ParitySectorDefect.MX L N *ᵥ u = μ • u + c • v)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → v ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ f))
    (hl0 : 0 ≤ groundLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N)
    (hq : 0 < v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v))
    (hqμ : v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v) < μ) (hε0 : 0 < ε)
    (hS : SinSqClose ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L N ε v) :
    Cvs.Route.AngleBoundFromFloor.ConnesFloor L N
      ((u ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v)) ^ 2
        / (μ * (v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v))) * ((1 - ε) / ε)) v := by
  refine ⟨μ, v, hfloor, ?_, hqμ⟩
  have h := one_sub_mul_sq_le_of_sinSqClose hL hve hv1 hue hu1 huv hu hS
  have hlq : groundLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N
      ≤ v ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ v) := by
    have hm := (ground_spec ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ hL N).2.2.1 v hve
    rwa [hv1, mul_one] at hm
  exact rho_sq_mul_le_of h hl0 (hlq.trans hqμ.le) (hq.trans hqμ) hq hε0

end Window

end Cvs.Route.EigenvectorCoordinateCompression
