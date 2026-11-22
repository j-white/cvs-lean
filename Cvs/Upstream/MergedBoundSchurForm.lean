import Mathlib
import Cvs.Upstream.MergedLowerBoundPositivity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The merged bound, the pair (bulk floor, form-metric coupling), and the Schur form

For a symmetric bilinear `B` on `E`, subspaces `R` and `H`, and `w ∈ H ∩ Rᗮ`: the merged bound
`B(r+w,r+w) ≥ b‖w‖² + δ·B(r,r)` gives the floor `B(w,w) ≥ b‖w‖²` and the coupling
`B(r,w)² ≤ (1−δ)B(r,r)B(w,w)`; conversely the pair gives the merged bound with `(η/2, ηc_b/2)`.
With `B > 0` on a finite-dimensional `R`, the merged bound is `B(w,w) − (1−δ)⁻¹B(A⁻¹Bw, w) ≥ b‖w‖²`.
-/

noncomputable section

namespace Cvs.Upstream.MergedBoundSchurForm

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The merged lower bound: `b‖w‖² + δ·B(r,r) ≤ B(r+w, r+w)` for `r ∈ R` and `w ∈ H ∩ Rᗮ`. -/
def Merged (B : LinearMap.BilinForm ℝ E) (H R : Submodule ℝ E) (b δ : ℝ) : Prop :=
  ∀ r ∈ R, ∀ w ∈ H, w ∈ Rᗮ → b * ‖w‖ ^ 2 + δ * B r r ≤ B (r + w) (r + w)

/-- The merged bound of a form is `MergedLowerBoundPositivity`'s merged bound of its diagonal `x ↦ B(x,x)`. -/
theorem merged_iff_diag {B : LinearMap.BilinForm ℝ E} {H R : Submodule ℝ E} {b δ : ℝ} :
    Merged B H R b δ ↔ Cvs.Upstream.MergedLowerBoundPositivity.Merged (fun x => B x x) H R b δ :=
  Iff.rfl

/-- The bulk floor: `c_b‖w‖² ≤ B(w,w)` for `w ∈ H ∩ Rᗮ`. -/
def BulkFloor (B : LinearMap.BilinForm ℝ E) (H R : Submodule ℝ E) (cb : ℝ) : Prop :=
  ∀ w ∈ H, w ∈ Rᗮ → cb * ‖w‖ ^ 2 ≤ B w w

/-- The coupling in the form metric: `B(r,w)² ≤ (1−η)B(r,r)B(w,w)` for `r ∈ R`, `w ∈ H ∩ Rᗮ`. -/
def Coupling (B : LinearMap.BilinForm ℝ E) (H R : Submodule ℝ E) (η : ℝ) : Prop :=
  ∀ r ∈ R, ∀ w ∈ H, w ∈ Rᗮ → B r w ^ 2 ≤ (1 - η) * B r r * B w w

/-- `u = A⁻¹Bw`: `u ∈ R` solves the normal equations `B(r,u) = B(r,w)` for every `r ∈ R`. -/
def IsSchurRep (B : LinearMap.BilinForm ℝ E) (R : Submodule ℝ E) (w u : E) : Prop :=
  u ∈ R ∧ ∀ r ∈ R, B r u = B r w

/-- The Schur form `C − (1−δ)⁻¹B*A⁻¹B ≥ b` on `H ∩ Rᗮ`, with `B*A⁻¹B(w) = B(u,w)` for
`u = A⁻¹Bw`. -/
def Schur (B : LinearMap.BilinForm ℝ E) (H R : Submodule ℝ E) (b δ : ℝ) : Prop :=
  ∀ w ∈ H, w ∈ Rᗮ → ∀ u, IsSchurRep B R w u → b * ‖w‖ ^ 2 ≤ B w w - (1 - δ)⁻¹ * B u w

/-- The expansion `B(x+y, x+y) = B(x,x) + 2B(x,y) + B(y,y)` of a symmetric form. -/
theorem apply_add_add {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (x y : E) :
    B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  have h := hB.eq y x
  simp only [map_add, LinearMap.add_apply]
  rw [h]; ring

/-- The expansion along a line: `B(s•x + y, s•x + y) = s²B(x,x) + 2sB(x,y) + B(y,y)`. -/
theorem apply_smul_add {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (s : ℝ) (x y : E) :
    B (s • x + y) (s • x + y) = s ^ 2 * B x x + 2 * s * B x y + B y y := by
  rw [apply_add_add hB]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- `A⁻¹Bw` exists when `R` is finite-dimensional and `B > 0` on `R`. -/
theorem exists_isSchurRep {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {R : Submodule ℝ E}
    [FiniteDimensional ℝ R] (hpos : ∀ r ∈ R, r ≠ 0 → 0 < B r r) (w : E) :
    ∃ u, IsSchurRep B R w u := by
  set B' := B.restrict R with hB'
  have hsep : ∀ x : R, B' x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hx0 : (x : E) ≠ 0 := fun h => hne (Subtype.ext h)
    exact (hpos x x.2 hx0).ne' hx
  have hnd : B'.Nondegenerate :=
    ⟨fun x hx => hsep x (hx x), fun y hy => hsep y (hy y)⟩
  set φ : Module.Dual ℝ R := (B.flip w).comp R.subtype with hφ
  set v := (B'.toDual hnd).symm φ with hv
  refine ⟨v, v.2, fun r hr => ?_⟩
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ ⟨r, hr⟩
  rw [← hv] at h
  simp only [hB', LinearMap.BilinForm.restrict_apply, hφ, LinearMap.coe_comp,
    Function.comp_apply, Submodule.coe_subtype, LinearMap.domRestrict_apply] at h
  rw [hB.eq r v]
  exact h

/-- **Merged ⟹ Schur form**, for `δ < 1`. -/
theorem schur_of_merged {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {H R : Submodule ℝ E}
    {b δ : ℝ} (hm : Merged B H R b δ) (hδ1 : δ < 1) : Schur B H R b δ := by
  intro w hw hwR u hu
  have huu : B u w = B u u := (hu.2 u hu.1).symm
  set s := (1 - δ)⁻¹ with hs
  have hs1 : (1 - δ) * s = 1 := mul_inv_cancel₀ (by linarith)
  have h := hm ((-s) • u) (R.smul_mem _ hu.1) w hw hwR
  rw [apply_smul_add hB] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  rw [huu] at h ⊢
  have e : s * B u u = (1 - δ) * s * (s * B u u) := by rw [hs1, one_mul]
  nlinarith

/-- **Schur form ⟹ merged**, for `δ < 1`, given `B ≥ 0` on `R` and `A⁻¹Bw` for every
`w ∈ H ∩ Rᗮ`. -/
theorem merged_of_schur {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {H R : Submodule ℝ E}
    {b δ : ℝ} (hs : Schur B H R b δ) (hδ1 : δ < 1) (hR : ∀ r ∈ R, 0 ≤ B r r)
    (hex : ∀ w ∈ H, w ∈ Rᗮ → ∃ u, IsSchurRep B R w u) : Merged B H R b δ := by
  intro r hr w hw hwR
  obtain ⟨u, hu⟩ := hex w hw hwR
  have hsw := hs w hw hwR u hu
  have huu : B u w = B u u := (hu.2 u hu.1).symm
  have hru : B r w = B r u := (hu.2 r hr).symm
  set t := 1 - δ with ht
  have ht0 : 0 < t := by linarith
  have hpos := hR (t • r + u) (R.add_mem (R.smul_mem t hr) hu.1)
  rw [apply_smul_add hB] at hpos
  rw [apply_add_add hB, hru]
  rw [huu] at hsw
  have hst : t * (t⁻¹ * B u u) = B u u := by rw [← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
  have hsw' : t * (b * ‖w‖ ^ 2) ≤ t * (B w w - t⁻¹ * B u u) :=
    mul_le_mul_of_nonneg_left hsw ht0.le
  have key : t * (b * ‖w‖ ^ 2 + δ * B r r) ≤ t * (B r r + 2 * B r u + B w w) := by
    nlinarith
  exact le_of_mul_le_mul_left key ht0

/-- **Merged ⟺ Schur form**, for `δ < 1`, when `R` is finite-dimensional and `B > 0` on `R`. -/
theorem merged_iff_schur {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {H R : Submodule ℝ E}
    [FiniteDimensional ℝ R] (hpos : ∀ r ∈ R, r ≠ 0 → 0 < B r r) {b δ : ℝ} (hδ1 : δ < 1) :
    Merged B H R b δ ↔ Schur B H R b δ := by
  refine ⟨fun hm => schur_of_merged hB hm hδ1, fun hs => merged_of_schur hB hs hδ1 ?_ ?_⟩
  · intro r hr
    by_cases h0 : r = 0
    · simp [h0]
    · exact (hpos r hr h0).le
  · exact fun w _ _ => exists_isSchurRep hB hpos w

end Cvs.Upstream.MergedBoundSchurForm
