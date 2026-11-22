import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.InsideFunctionTame
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.ZeroSidePolarized

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The form coupling from the tame coupling, given form-norm density of tame classes

For symmetric `B` with `c‖u‖² ≤ B(u, u)`, finite-dimensional `R ⊆ T`, `T` closed under differences and dense
in `H` for `‖·‖` and `B` jointly, the coupling on `T ∩ Rᗮ` is the coupling on `H`, via `t_n − P_R(t_n − w)`.
At `80 ≤ 2πx`, `T` is the tame classes `w_u`, `R_F ⊆ T` as `spineMap x a = w_{W_a}`, and `TameDense`
gives `FormCoupling x δ ↔ TameCoupling x δ`.
-/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace Cvs.WeilForm.CouplingFromTameDensity
open Cvs.ZeroCounting

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The form `B − c⟪·,·⟫`. -/
def shifted (B : LinearMap.BilinForm ℝ E) (c : ℝ) : LinearMap.BilinForm ℝ E :=
  B - c • innerₗ E

theorem shifted_apply (B : LinearMap.BilinForm ℝ E) (c : ℝ) (u v : E) :
    shifted B c u v = B u v - c * ⟪u, v⟫_ℝ := by
  simp [shifted]

theorem shifted_isSymm {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (c : ℝ) : (shifted B c).IsSymm :=
  ⟨fun u v => by
    simp only [shifted_apply, real_inner_comm u v]
    rw [hB.eq u v]⟩

theorem shifted_nonneg {B : LinearMap.BilinForm ℝ E} {c : ℝ} (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) (u : E) :
    0 ≤ shifted B c u u := by
  rw [shifted_apply, real_inner_self_eq_norm_sq]; linarith [hc u]

theorem shifted_self (B : LinearMap.BilinForm ℝ E) (c : ℝ) (u : E) :
    shifted B c u u = B u u - c * ‖u‖ ^ 2 := by
  rw [shifted_apply, real_inner_self_eq_norm_sq]

/-- **Vanishing norm and form give vanishing pairing**: for symmetric `B` with `c‖u‖² ≤ B(u, u)`,
`‖a_n‖ → 0` and `B(a_n, a_n) → 0` give `B(a_n, b_n) → 0` whenever `‖b_n‖` and `B(b_n, b_n)` converge. -/
theorem tendsto_cross_zero {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {a b : ℕ → E} (ha : Tendsto (fun n => ‖a n‖) atTop (𝓝 0))
    (haB : Tendsto (fun n => B (a n) (a n)) atTop (𝓝 0)) {Nb Qb : ℝ}
    (hb : Tendsto (fun n => ‖b n‖) atTop (𝓝 Nb)) (hbB : Tendsto (fun n => B (b n) (b n)) atTop (𝓝 Qb)) :
    Tendsto (fun n => B (a n) (b n)) atTop (𝓝 0) := by
  have hsa : Tendsto (fun n => shifted B c (a n) (a n)) atTop (𝓝 0) := by
    simp_rw [shifted_self]
    simpa using haB.sub ((ha.pow 2).const_mul c)
  have hsb : Tendsto (fun n => shifted B c (b n) (b n)) atTop (𝓝 (Qb - c * Nb ^ 2)) := by
    simp_rw [shifted_self]
    exact hbB.sub ((hb.pow 2).const_mul c)
  have hsq : Tendsto (fun n => shifted B c (a n) (b n) ^ 2) atTop (𝓝 0) := by
    have hm : Tendsto (fun n => shifted B c (a n) (a n) * shifted B c (b n) (b n)) atTop (𝓝 0) := by
      simpa using hsa.mul hsb
    exact squeeze_zero (fun _ => sq_nonneg _)
      (fun n => (shifted B c).apply_sq_le_of_symm (shifted_nonneg hc)
        (LinearMap.BilinForm.isSymm_iff.1 (shifted_isSymm hB c)) _ _) hm
  have hcr : Tendsto (fun n => shifted B c (a n) (b n)) atTop (𝓝 0) := by
    have h := hsq.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 h
  have hi : Tendsto (fun n => ⟪a n, b n⟫_ℝ) atTop (𝓝 0) := by
    have hm : Tendsto (fun n => ‖a n‖ * ‖b n‖) atTop (𝓝 0) := by simpa using ha.mul hb
    refine (tendsto_zero_iff_abs_tendsto_zero _).2 (squeeze_zero (fun _ => abs_nonneg _)
      (fun n => abs_real_inner_le_norm _ _) hm)
  have := hcr.add (hi.const_mul c)
  simp only [shifted_apply, sub_add_cancel, mul_zero, add_zero] at this
  exact this

/-- A bilinear form is continuous on the diagonal of a finite-dimensional subspace. -/
theorem continuous_apply_self_of_finiteDimensional (B : LinearMap.BilinForm ℝ E) (R : Submodule ℝ E)
    [FiniteDimensional ℝ R] : Continuous fun q : R => B q q := by
  let B' : R →ₗ[ℝ] R →ₗ[ℝ] ℝ := B.compl₁₂ R.subtype R.subtype
  let f : R →L[ℝ] R →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B')
  have h : (fun q : R => B q q) = fun q => f q q := rfl
  rw [h]
  exact f.continuous₂.comp (continuous_id.prodMk continuous_id)

/-- **Approximants inside `Rᗮ`**: for symmetric `B` with `c‖u‖² ≤ B(u, u)`, finite-dimensional `R ⊆ T` and `T`
closed under differences, approximants `t_n ∈ T` of `w ∈ Rᗮ` in norm and form give approximants
`s_n ∈ T ∩ Rᗮ` in norm and form. -/
theorem exists_orthogonal_approx {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {R : Submodule ℝ E} [FiniteDimensional ℝ R]
    [R.HasOrthogonalProjection] {T : Set E} (hT : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ T)
    (hRT : ∀ r ∈ R, r ∈ T) {w : E} (hw : w ∈ Rᗮ) {t : ℕ → E} (htT : ∀ n, t n ∈ T)
    (htn : Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0))
    (htB : Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0)) :
    ∃ s : ℕ → E, (∀ n, s n ∈ T) ∧ (∀ n, s n ∈ Rᗮ) ∧ Tendsto (fun n => ‖s n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (s n - w) (s n - w)) atTop (𝓝 0) := by
  let p : ℕ → E := fun n => R.starProjection (t n - w)
  have hpR : ∀ n, p n ∈ R := fun n => R.starProjection_apply_mem _
  have hp : ∀ n, p n = R.starProjection (t n) := fun n => by
    simp only [p, map_sub, (Submodule.starProjection_apply_eq_zero_iff R).2 hw, sub_zero]
  have hpnorm : Tendsto (fun n => ‖p n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => Submodule.norm_starProjection_apply_le _ _) htn
  let q : ℕ → R := fun n => ⟨p n, hpR n⟩
  have hqn : Tendsto q atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hpnorm
  have hpB : Tendsto (fun n => B (p n) (p n)) atTop (𝓝 0) := by
    have := ((continuous_apply_self_of_finiteDimensional B R).tendsto 0).comp hqn
    simpa [Function.comp_def, q] using this
  have he : ∀ n, (t n - p n) - w = (t n - w) - p n := fun n => by abel
  have hen : Tendsto (fun n => ‖(t n - p n) - w‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (he n).symm ▸ norm_sub_le _ _) ?_
    simpa using htn.add hpnorm
  have hdp : Tendsto (fun n => B (t n - w) (p n)) atTop (𝓝 0) := by
    have h := tendsto_cross_zero hB hc hpnorm hpB htn htB
    exact h.congr fun n => hB.eq _ _
  have heB : Tendsto (fun n => B ((t n - p n) - w) ((t n - p n) - w)) atTop (𝓝 0) := by
    have hexp : ∀ n, B ((t n - p n) - w) ((t n - p n) - w) = B (t n - w) (t n - w) - 2 * B (t n - w) (p n)
        + B (p n) (p n) := fun n => by
      simp only [he n, map_sub, LinearMap.sub_apply]
      rw [hB.eq (p n) (t n), hB.eq (p n) w]
      ring
    simp_rw [hexp]
    simpa using (htB.sub (hdp.const_mul 2)).add hpB
  refine ⟨fun n => t n - p n, fun n => hT _ (htT n) _ (hRT _ (hpR n)), fun n => ?_, hen, heB⟩
  show t n - p n ∈ Rᗮ
  rw [hp]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- **The form converges along approximants**: for symmetric `B` with `c‖u‖² ≤ B(u, u)`, `‖s_n − w‖ → 0` and
`B(s_n − w, s_n − w) → 0` give `B(r, s_n) → B(r, w)` and `B(s_n, s_n) → B(w, w)`. -/
theorem tendsto_apply_of_approx {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {s : ℕ → E} {w : E} (hsn : Tendsto (fun n => ‖s n - w‖) atTop (𝓝 0))
    (hsB : Tendsto (fun n => B (s n - w) (s n - w)) atTop (𝓝 0)) (r : E) :
    Tendsto (fun n => B r (s n)) atTop (𝓝 (B r w)) ∧ Tendsto (fun n => B (s n) (s n)) atTop (𝓝 (B w w)) := by
  have hsw : ∀ n, s n = w + (s n - w) := fun n => by abel
  constructor
  · have h0 := tendsto_cross_zero hB hc hsn hsB (b := fun _ => r) tendsto_const_nhds
      tendsto_const_nhds
    have h1 : ∀ n, B r (s n) = B r w + B (s n - w) r := fun n => by
      conv_lhs => rw [hsw n]
      rw [map_add, hB.eq (s n - w) r]
    simp_rw [h1]
    simpa using h0.const_add (B r w)
  · have h0 := tendsto_cross_zero hB hc hsn hsB (b := fun _ => w) tendsto_const_nhds
      tendsto_const_nhds
    have h1 : ∀ n, B (s n) (s n) = B w w + 2 * B (s n - w) w + B (s n - w) (s n - w) := fun n => by
      conv_lhs => rw [hsw n]
      simp only [map_add, LinearMap.add_apply]
      rw [hB.eq w (s n - w)]
      ring
    simp_rw [h1]
    simpa using ((h0.const_mul 2).const_add (B w w)).add hsB

/-- **The coupling from a dense difference-closed set, relative to `H`**: for symmetric `B` with
`c‖u‖² ≤ B(u, u)`, finite-dimensional `R ⊆ T`, `T` closed under differences and every `w ∈ H` the limit of some
`t_n ∈ T` in norm and form, the coupling on `T ∩ Rᗮ` gives `Coupling B H R δ`. -/
theorem coupling_of_dense {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {H R : Submodule ℝ E} [FiniteDimensional ℝ R]
    [R.HasOrthogonalProjection] {T : Set E} (hT : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ T) (hRT : ∀ r ∈ R, r ∈ T)
    (hD : ∀ w ∈ H, ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0))
    {δ : ℝ} (h : ∀ r ∈ R, ∀ w ∈ T, w ∈ Rᗮ → B r w ^ 2 ≤ (1 - δ) * B r r * B w w) :
    Cvs.Upstream.MergedBoundSchurForm.Coupling B H R δ := by
  intro r hr w hwH hw
  obtain ⟨t, htT, htn, htB⟩ := hD w hwH
  obtain ⟨s, hsT, hsR, hsn, hsB⟩ := exists_orthogonal_approx hB hc hT hRT hw htT htn htB
  obtain ⟨hrs, hss⟩ := tendsto_apply_of_approx hB hc hsn hsB r
  exact le_of_tendsto_of_tendsto' (hrs.pow 2) (hss.const_mul ((1 - δ) * B r r))
    fun n => (h r hr (s n) (hsT n) (hsR n)).trans_eq (by ring)

end Generic

/-! ### At scale `x` -/

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)

/-- The tame classes at `x`: the form-domain classes `w_u` of tests `u` tame on `[1/x, 1]`. -/
def tameSet {x : ℕ} (hx0 : (0 : ℝ) < x) : Set (Dom x) :=
  {w | ∃ (u : ℝ → ℝ) (hu : Tame u (1 / x) 1), Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu = w}

theorem sub_mem_tameSet {x : ℕ} (hx0 : (0 : ℝ) < x) :
    ∀ a ∈ tameSet hx0, ∀ b ∈ tameSet hx0, a - b ∈ tameSet hx0 := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  exact ⟨_, Cvs.WeilForm.InsideFunctionTame.tame_sub hu hv, Cvs.WeilForm.ZeroSidePolarized.wv_sub hx0 hu hv⟩

/-- The window form at `x` is bounded below by `floorConst · ‖·‖²`. -/
theorem floor_Bx (x : ℕ) (u : Dom x) :
    Cvs.WeilForm.WindowFormNormFloor.floorConst (Real.log x) x (Nat.clog 2 x) * ‖u‖ ^ 2 ≤ Bx x u u := by
  rw [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  exact Cvs.WeilForm.FormDomain.weilQW_ge_floor _ _ _ u

end Cvs.WeilForm.CouplingFromTameDensity
