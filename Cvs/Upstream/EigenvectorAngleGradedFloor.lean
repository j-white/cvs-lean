import Mathlib
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.WeilForm.CouplingSchurComplement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The angle to an eigenvector through a graded floor on the hyperplane

For unit `v`, `T θ = l θ` and a weight `w` on `vᗮ` with `κ w ≤ ⟪(T − l)·, ·⟫`,
`⟪T v, ·⟫² ≤ R w` and `g‖·‖² ≤ w`: `w((C − l)⁻¹ r) ≤ R/κ²` and `1 − ⟪v, θ⟫² ≤ R/(κ²g + R)`.
For `w = Σᵢ gᵢ‖Pᵢ ·‖²` over an orthogonal family spanning `vᗮ`, `R = Σᵢ ‖Pᵢ(T v)‖²/gᵢ`.
The bound is invariant under `T ↦ T + c`; a Schur coupling of two blocks gives a graded floor.
-/

noncomputable section

open scoped InnerProductSpace

namespace Cvs.Upstream.EigenvectorAngleGradedFloor
open Cvs.ZeroCounting

open Cvs.Route.EigenvectorCoordinateCompression

/-! ### The graded angle bound -/

section Graded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On `vᗮ`, `⟪(C − l) y, y⟫ = ⟪T y − l y, y⟫`. -/
theorem inner_compr_sub_smul (T : E →ₗ[ℝ] E) (v : E) (l : ℝ) (y : perp v) :
    ⟪compr T v y - l • y, y⟫_ℝ = ⟪T y - l • (y : E), y⟫_ℝ := by
  rw [inner_sub_left, inner_sub_left, inner_compr, real_inner_smul_left, real_inner_smul_left]
  rfl

/-- `t ≤ R/a` with `0 ≤ t`, `0 < a`, `0 ≤ R` gives `t/(1 + t) ≤ R/(a + R)`. -/
theorem div_one_add_le_div {t a R : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hR : 0 ≤ R) (h : t ≤ R / a) :
    t / (1 + t) ≤ R / (a + R) := by
  rw [le_div_iff₀ ha] at h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A graded floor `κ w ≤ ⟪T y − l y, y⟫` over `g‖y‖² ≤ w y` is the floor `l + κ g` of `T`
on `vᗮ`. -/
theorem floor_of_graded {T : E →ₗ[ℝ] E} {v : E} {l κ g : ℝ} (w : perp v → ℝ) (hκ : 0 < κ)
    (h1 : ∀ y : perp v, κ * w y ≤ ⟪T y - l • (y : E), y⟫_ℝ)
    (h3 : ∀ y : perp v, g * ‖y‖ ^ 2 ≤ w y) (y : perp v) :
    (l + κ * g) * ‖y‖ ^ 2 ≤ ⟪T y, (y : E)⟫_ℝ := by
  have a := h1 y
  have b := mul_le_mul_of_nonneg_left (h3 y) hκ.le
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at a
  have hn : ‖(y : E)‖ = ‖y‖ := rfl
  rw [hn] at a
  nlinarith

/-- **The graded Schur bound**: in finite dimension, a graded floor `κ w ≤ ⟪T y − l y, y⟫`
on `vᗮ` with `⟪T v, y⟫² ≤ R w y` and `g‖y‖² ≤ w y` puts `l` outside the spectrum of `C` and
gives `w((C − l)⁻¹ r) ≤ R/κ²`. -/
theorem weight_schurVec_le_of_graded [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {v : E}
    {l κ g R : ℝ} (w : perp v → ℝ) (hκ : 0 < κ) (hg : 0 < g) (hR : 0 ≤ R)
    (h1 : ∀ y : perp v, κ * w y ≤ ⟪T y - l • (y : E), y⟫_ℝ)
    (h2 : ∀ y : perp v, ⟪T v, y⟫_ℝ ^ 2 ≤ R * w y)
    (h3 : ∀ y : perp v, g * ‖y‖ ^ 2 ≤ w y) :
    l ∉ spectrum ℝ (compr T v) ∧ w (schurVec T v l) ≤ R / κ ^ 2 := by
  have hl : l ∉ spectrum ℝ (compr T v) :=
    notMem_spectrum_of_floor (floor_of_graded w hκ h1 h3) (by linarith [mul_pos hκ hg])
  refine ⟨hl, ?_⟩
  set z := schurVec T v l
  have he : ⟪T z - l • (z : E), z⟫_ℝ = ⟪T v, (z : E)⟫_ℝ := by
    rw [← inner_compr_sub_smul, compr_sub_smul_schurVec hl, inner_resid]
  have a := h1 z
  rw [he] at a
  have b := h2 z
  have hw0 : 0 ≤ w z := le_trans (by positivity) (h3 z)
  rw [le_div_iff₀ (by positivity)]
  rcases hw0.lt_or_eq with hpos | hzero
  · have hsq : (κ * w z) ^ 2 ≤ R * w z :=
      le_trans (pow_le_pow_left₀ (by positivity) a 2) b
    refine le_of_mul_le_mul_right ?_ hpos
    nlinarith
  · rw [← hzero, zero_mul]
    exact hR

/-- Under the hypotheses of `weight_schurVec_le_of_graded`, `‖(C − l)⁻¹ r‖² ≤ R/(κ²g)`. -/
theorem norm_schurVec_sq_le_of_graded [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {v : E}
    {l κ g R : ℝ} (w : perp v → ℝ) (hκ : 0 < κ) (hg : 0 < g) (hR : 0 ≤ R)
    (h1 : ∀ y : perp v, κ * w y ≤ ⟪T y - l • (y : E), y⟫_ℝ)
    (h2 : ∀ y : perp v, ⟪T v, y⟫_ℝ ^ 2 ≤ R * w y)
    (h3 : ∀ y : perp v, g * ‖y‖ ^ 2 ≤ w y) :
    l ∉ spectrum ℝ (compr T v) ∧ ‖schurVec T v l‖ ^ 2 ≤ R / (κ ^ 2 * g) := by
  obtain ⟨hl, hw⟩ := weight_schurVec_le_of_graded w hκ hg hR h1 h2 h3
  refine ⟨hl, ?_⟩
  have c := h3 (schurVec T v l)
  rw [le_div_iff₀ (by positivity)] at hw ⊢
  nlinarith [mul_le_mul_of_nonneg_left c (sq_nonneg κ)]

/-- **The graded angle bound**: in finite dimension, for unit `v`, a unit eigenvector `θ` at
`l` and a graded floor `κ w ≤ ⟪T y − l y, y⟫` on `vᗮ` with `⟪T v, y⟫² ≤ R w y` and
`g‖y‖² ≤ w y`: `l ∉ σ(C)`, `‖(C − l)⁻¹ r‖² ≤ R/(κ²g)` and `1 − ⟪v, θ⟫² ≤ R/(κ²g + R)`. -/
theorem one_sub_inner_sq_le_of_graded [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} {v θ : E}
    {l κ g R : ℝ} (w : perp v → ℝ) (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ)
    (hκ : 0 < κ) (hg : 0 < g) (hR : 0 ≤ R)
    (h1 : ∀ y : perp v, κ * w y ≤ ⟪T y - l • (y : E), y⟫_ℝ)
    (h2 : ∀ y : perp v, ⟪T v, y⟫_ℝ ^ 2 ≤ R * w y)
    (h3 : ∀ y : perp v, g * ‖y‖ ^ 2 ≤ w y) :
    l ∉ spectrum ℝ (compr T v) ∧ ‖schurVec T v l‖ ^ 2 ≤ R / (κ ^ 2 * g) ∧
      1 - ⟪v, θ⟫_ℝ ^ 2 ≤ R / (κ ^ 2 * g + R) := by
  obtain ⟨hl, hz⟩ := norm_schurVec_sq_le_of_graded w hκ hg hR h1 h2 h3
  refine ⟨hl, hz, ?_⟩
  rw [one_sub_inner_sq_eq_schurVec hv hθ1 hθ hl]
  exact div_one_add_le_div (sq_nonneg _) (by positivity) hR hz

/-- **The graded angle bound at the Rayleigh value**: under the hypotheses of
`one_sub_inner_sq_le_of_graded` with the graded floor taken at `q = ⟪T v, v⟫ ≥ l`,
`‖(C − q)⁻¹ r‖² ≤ R/(κ²g)` and `1 − ⟪v, θ⟫² ≤ R/(κ²g + R)`. -/
theorem one_sub_inner_sq_le_of_graded_rayleigh [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}
    {v θ : E} {l κ g R : ℝ} (w : perp v → ℝ) (hv : ‖v‖ = 1) (hθ1 : ‖θ‖ = 1)
    (hθ : T θ = l • θ) (hκ : 0 < κ) (hg : 0 < g) (hR : 0 ≤ R) (hlq : l ≤ ⟪T v, v⟫_ℝ)
    (h1 : ∀ y : perp v, κ * w y ≤ ⟪T y - ⟪T v, v⟫_ℝ • (y : E), y⟫_ℝ)
    (h2 : ∀ y : perp v, ⟪T v, y⟫_ℝ ^ 2 ≤ R * w y)
    (h3 : ∀ y : perp v, g * ‖y‖ ^ 2 ≤ w y) :
    ‖schurVec T v ⟪T v, v⟫_ℝ‖ ^ 2 ≤ R / (κ ^ 2 * g) ∧
      1 - ⟪v, θ⟫_ℝ ^ 2 ≤ R / (κ ^ 2 * g + R) := by
  refine ⟨(norm_schurVec_sq_le_of_graded w hκ hg hR h1 h2 h3).2, ?_⟩
  have h1' : ∀ y : perp v, κ * w y ≤ ⟪T y - l • (y : E), y⟫_ℝ := by
    intro y
    have a := h1 y
    rw [inner_sub_left, real_inner_smul_left] at a ⊢
    nlinarith [real_inner_self_nonneg (x := (y : E))]
  exact (one_sub_inner_sq_le_of_graded w hv hθ1 hθ hκ hg hR h1' h2 h3).2.2

end Graded

/-! ### Regions: an orthogonal family covering the hyperplane -/

section Regions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

end Regions

/-! ### The two extreme gradings -/

section Extreme

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The joint gap is a lower bound on the eigenvalue**: `1 < K` and `K(q − l) ≤ μ − l` give
`(Kq − μ)/(K − 1) ≤ l`. -/
theorem div_le_of_jointGap {q l μ K : ℝ} (hK : 1 < K) (h : K * (q - l) ≤ μ - l) :
    (K * q - μ) / (K - 1) ≤ l := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **The joint gap with `q ≥ 0` is near-positivity**: `1 < K`, `K(q − l) ≤ μ − l` and `0 ≤ q`
give `−μ/(K − 1) ≤ l`. -/
theorem neg_div_le_of_jointGap {q l μ K : ℝ} (hK : 1 < K) (h : K * (q - l) ≤ μ - l)
    (hq : 0 ≤ q) : -μ / (K - 1) ≤ l := by
  refine le_trans ?_ (div_le_of_jointGap hK h)
  exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)

end Extreme

/-! ### Shift invariance -/

section Shift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Shift

/-! ### A Schur block floor -/

section Schur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The form `(y, w) ↦ ⟪T y − l y, w⟫`. -/
def shiftForm (T : E →ₗ[ℝ] E) (l : ℝ) : LinearMap.BilinForm ℝ E :=
  (innerₗ E).comp (T - l • LinearMap.id)

/-- `shiftForm T l y w = ⟪T y − l y, w⟫`. -/
theorem shiftForm_apply (T : E →ₗ[ℝ] E) (l : ℝ) (y w : E) :
    shiftForm T l y w = ⟪T y - l • y, w⟫_ℝ := by
  simp [shiftForm, inner_sub_left, real_inner_smul_left]

/-- For symmetric `T` the form `⟪T y − l y, w⟫` is symmetric. -/
theorem shiftForm_isSymm {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (l : ℝ) :
    (shiftForm T l).IsSymm := by
  refine ⟨fun y w => ?_⟩
  simp only [shiftForm_apply, inner_sub_left, real_inner_smul_left]
  rw [hT y w, real_inner_comm y w, real_inner_comm (T w) y]

/-- If `0 ≤ η < 1`, `0 ≤ A`, `0 ≤ a` and `b² ≤ (1 − η)Aa`, then
`(η/2)A + (η/4)a ≤ A + 2b + a`. -/
theorem half_add_quarter_le {A a b η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hA : 0 ≤ A)
    (ha : 0 ≤ a) (hb : b ^ 2 ≤ (1 - η) * A * a) :
    η / 2 * A + η / 4 * a ≤ A + 2 * b + a := by
  have hX : 0 ≤ (1 - η / 2) * A := mul_nonneg (by linarith) hA
  have hY : 0 ≤ (1 - η / 4) * a := mul_nonneg (by linarith) ha
  have hXY : (1 - η) * A * a ≤ ((1 - η / 2) * A) * ((1 - η / 4) * a) := by
    have : 0 ≤ (η / 4 + η ^ 2 / 8) * (A * a) := mul_nonneg (by positivity) (mul_nonneg hA ha)
    nlinarith
  have hsq : (2 * b) ^ 2 ≤ ((1 - η / 2) * A + (1 - η / 4) * a) ^ 2 := by
    nlinarith [sq_nonneg ((1 - η / 2) * A - (1 - η / 4) * a)]
  have := (abs_le_of_sq_le_sq' hsq (by linarith)).1
  linarith

/-- **The Schur block floor**, with `A(u) = ⟪T u − l u, u⟫` for symmetric `T`: if
`η A(y) ≤ A(y + w)` for `y ∈ D`, `w ∈ B` with `0 ≤ η < 1`, then
`(η/2)A(y) + (η/4)A(w) ≤ A(y + w)`. -/
theorem half_add_quarter_le_of_coupling {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {l η : ℝ}
    (D B : Submodule ℝ E) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hcoup : ∀ y ∈ D, ∀ w ∈ B, η * ⟪T y - l • y, y⟫_ℝ ≤ ⟪T (y + w) - l • (y + w), y + w⟫_ℝ)
    {y w : E} (hy : y ∈ D) (hw : w ∈ B) :
    η / 2 * ⟪T y - l • y, y⟫_ℝ + η / 4 * ⟪T w - l • w, w⟫_ℝ
      ≤ ⟪T (y + w) - l • (y + w), y + w⟫_ℝ := by
  have hS := shiftForm_isSymm hT l
  have hc : ∀ y ∈ D, ∀ w ∈ B, η * shiftForm T l y y ≤ shiftForm T l (y + w) (y + w) := by
    intro y hy w hw
    simpa only [shiftForm_apply] using hcoup y hy w hw
  have hb := Cvs.WeilForm.CouplingSchurComplement.sq_le_of_margin hS (hc y hy) hw
  have hA : 0 ≤ shiftForm T l y y := by
    have := hc y hy 0 B.zero_mem
    rw [add_zero] at this
    nlinarith
  have ha : 0 ≤ shiftForm T l w w := by
    have := hc 0 D.zero_mem w hw
    simpa only [zero_add, map_zero, LinearMap.zero_apply, mul_zero] using this
  have h := half_add_quarter_le hη0 hη1 hA ha hb
  rw [← Cvs.WeilForm.CouplingSchurComplement.apply_add_self hS] at h
  simpa only [shiftForm_apply] using h

/-- **The Schur block floor, graded**: for symmetric `T` and `A(u) = ⟪T u − l u, u⟫`, the
coupling `η A(y) ≤ A(y + w)` (`y ∈ D`, `w ∈ B`, `0 ≤ η < 1`), `s‖w‖² ≤ A(w)` on `B` and
`W ≤ A` on `D` give `(η/2)(W(y) + (s/2)‖w‖²) ≤ A(y + w)`. -/
theorem schur_graded_floor {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {l η s : ℝ}
    (D B : Submodule ℝ E) (W : E → ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hB : ∀ w ∈ B, s * ‖w‖ ^ 2 ≤ ⟪T w - l • w, w⟫_ℝ)
    (hcoup : ∀ y ∈ D, ∀ w ∈ B, η * ⟪T y - l • y, y⟫_ℝ ≤ ⟪T (y + w) - l • (y + w), y + w⟫_ℝ)
    (hW : ∀ y ∈ D, W y ≤ ⟪T y - l • y, y⟫_ℝ) {y w : E} (hy : y ∈ D) (hw : w ∈ B) :
    η / 2 * (W y + s / 2 * ‖w‖ ^ 2) ≤ ⟪T (y + w) - l • (y + w), y + w⟫_ℝ := by
  have h := half_add_quarter_le_of_coupling hT D B hη0 hη1 hcoup hy hw
  have a := mul_le_mul_of_nonneg_left (hW y hy) (by linarith : (0:ℝ) ≤ η / 2)
  have b := mul_le_mul_of_nonneg_left (hB w hw) (by linarith : (0:ℝ) ≤ η / 4)
  nlinarith

end Schur

end Cvs.Upstream.EigenvectorAngleGradedFloor
