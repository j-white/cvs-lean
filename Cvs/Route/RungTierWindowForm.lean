import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.CourantFischerInterlacing
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung tier of the window form on finite-dimensional test spaces

For orthonormal `v` with `R₁ ≤ F = span v ≤ Ev x` and `T` the operator of `Bx x` in `v`'s coordinates: `λ↑_i(Q|F ∩ Kᗮ)
≤ λ↑_{i+k}(Q|R₁)`; `EvenBulkFloor x b` is the defect bound below `λ↑_t(Q|F ∩ Kᗮ)` up to the surplus above it; the
weighted and plain angle conditions imply it, hold under RH and equal it at `K = R₁`; test spaces with `F ≠ R₁` exist.
-/

noncomputable section

open Module
open scoped RealInnerProductSpace Matrix

namespace Cvs.Route.RungTierWindowForm
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom Bx rung)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Upstream.CourantFischerInterlacing (eigAsc compr isSymmetric_compr inner_compr topSpace botDefect topSurplus)

/-! ### The operator of a bilinear form -/

section FormOp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The operator of a bilinear form on a finite-dimensional space, `⟪T_B u, w⟫ = B u w`. -/
def formOp (B : LinearMap.BilinForm ℝ F) : F →ₗ[ℝ] F :=
  ∑ j, (B.flip (stdOrthonormalBasis ℝ F j)).smulRight (stdOrthonormalBasis ℝ F j)

theorem inner_formOp (B : LinearMap.BilinForm ℝ F) (u w : F) : ⟪formOp B u, w⟫ = B u w := by
  conv_rhs => rw [← (stdOrthonormalBasis ℝ F).sum_repr' w]
  rw [formOp, LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.smulRight_apply, real_inner_smul_left, map_smul, smul_eq_mul]
  rw [mul_comm]
  rfl

theorem isSymmetric_formOp {B : LinearMap.BilinForm ℝ F} (hB : B.IsSymm) : (formOp B).IsSymmetric :=
  fun u w => by rw [inner_formOp, real_inner_comm, inner_formOp, hB.eq]

end FormOp

/-! ### Orthonormal coordinates on a finite-dimensional test space -/

variable {x : ℕ} {d : ℕ}

/-- The coordinate map `a ↦ Σ_i a_i v_i` of a family `v : Fin d → Dom x`. -/
def emb (v : Fin d → Dom x) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] Dom x where
  toFun a := ∑ i, a i • v i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem emb_apply (v : Fin d → Dom x) (a : EuclideanSpace ℝ (Fin d)) : emb v a = ∑ i, a i • v i := rfl

theorem inner_emb {v : Fin d → Dom x} (hv : Orthonormal ℝ v) (a b : EuclideanSpace ℝ (Fin d)) :
    ⟪emb v a, emb v b⟫ = ⟪a, b⟫ := by
  rw [emb_apply, emb_apply, hv.inner_sum, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]

theorem norm_emb {v : Fin d → Dom x} (hv : Orthonormal ℝ v) (a : EuclideanSpace ℝ (Fin d)) :
    ‖emb v a‖ = ‖a‖ := by
  have h := inner_emb hv a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem emb_injective {v : Fin d → Dom x} (hv : Orthonormal ℝ v) : Function.Injective (emb v) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h : ‖a‖ = 0 := by rw [← norm_emb hv, ha]; exact norm_zero
  exact norm_eq_zero.1 h

theorem range_emb (v : Fin d → Dom x) : LinearMap.range (emb v) = Submodule.span ℝ (Set.range v) := by
  ext y
  rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨c, hc⟩ => ⟨WithLp.toLp 2 c, hc⟩⟩

/-- The operator of the window form `Bx x` in the coordinates of `v`: on orthonormal `v` its eigenvalues are the
Ritz values of `Q` on `span v`. -/
def opOn (x : ℕ) (v : Fin d → Dom x) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  formOp ((Bx x).compl₁₂ (emb v) (emb v))

theorem inner_opOn_self (v : Fin d → Dom x) (a : EuclideanSpace ℝ (Fin d)) :
    ⟪opOn x v a, a⟫ = Qx x (emb v a) := by
  rw [opOn, inner_formOp]
  exact Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ _

theorem isSymmetric_opOn (v : Fin d → Dom x) : (opOn x v).IsSymmetric :=
  isSymmetric_formOp ⟨fun a b => (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _).eq (emb v a) (emb v b)⟩

/-- A subspace of `Dom x` read in the coordinates of `v`. -/
abbrev inC (v : Fin d → Dom x) (K : Submodule ℝ (Dom x)) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  K.comap (emb v)

theorem finrank_inC {v : Fin d → Dom x} (hv : Orthonormal ℝ v) {K : Submodule ℝ (Dom x)}
    (hK : K ≤ Submodule.span ℝ (Set.range v)) : finrank ℝ (inC v K) = finrank ℝ K := by
  rw [(Submodule.equivMapOfInjective _ (emb_injective hv) (inC v K)).finrank_eq,
    Submodule.map_comap_eq_of_le (by rwa [range_emb])]

/-- **Orthogonality in coordinates**: for `R ≤ span v`, `emb a ⊥ R` iff `a ⊥ inC v R`. -/
theorem emb_mem_orthogonal_iff {v : Fin d → Dom x} (hv : Orthonormal ℝ v) {R : Submodule ℝ (Dom x)}
    (hR : R ≤ Submodule.span ℝ (Set.range v)) (a : EuclideanSpace ℝ (Fin d)) :
    emb v a ∈ Rᗮ ↔ a ∈ (inC v R)ᗮ := by
  simp only [Submodule.mem_orthogonal]
  constructor
  · intro h c hc
    rw [← inner_emb hv]
    exact h _ hc
  · intro h r hr
    obtain ⟨c, rfl⟩ : r ∈ LinearMap.range (emb v) := by rw [range_emb]; exact hR hr
    rw [inner_emb hv]
    exact h c hr

/-! ### Nothing is lost on orthonormal test spaces -/

/-- Every finite-dimensional subspace of `Dom x` is the span of an orthonormal family. -/
theorem exists_orthonormal_span (F : Submodule ℝ (Dom x)) [FiniteDimensional ℝ F] :
    ∃ (d : ℕ) (v : Fin d → Dom x), Orthonormal ℝ v ∧ Submodule.span ℝ (Set.range v) = F := by
  set b := Module.finBasis ℝ F
  set f : Fin (finrank ℝ F) → Dom x := fun i => (b i : Dom x)
  have hf : LinearIndependent ℝ f := b.linearIndependent.map' F.subtype (Submodule.ker_subtype F)
  refine ⟨_, InnerProductSpace.gramSchmidtNormed ℝ f, InnerProductSpace.gramSchmidtNormed_orthonormal hf, ?_⟩
  rw [InnerProductSpace.span_gramSchmidtNormed_range]
  have : Set.range f = F.subtype '' Set.range b := by
    ext y; simp [f]
  rw [InnerProductSpace.span_gramSchmidt, this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

/-- **`EvenBulkFloor` on orthonormal test spaces**: `EvenBulkFloor x b` holds iff `b‖a‖² ≤ Q(Σ a_i v_i)` whenever
`v` is orthonormal with `R₁ ≤ span v ≤ Ev x` and `Σ a_i v_i ⊥ R₁`. -/
theorem evenBulkFloor_iff_orthonormal (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b ↔ ∀ (d : ℕ) (v : Fin d → Dom x), Orthonormal ℝ v →
      R1 x ≤ Submodule.span ℝ (Set.range v) → Submodule.span ℝ (Set.range v) ≤ Ev x →
      ∀ a : EuclideanSpace ℝ (Fin d), a ∈ (inC v (R1 x))ᗮ → b * ‖a‖ ^ 2 ≤ ⟪opOn x v a, a⟫ := by
  constructor
  · intro h d v hv hR hE a ha
    rw [inner_opOn_self, ← norm_emb hv]
    have hspan : emb v a ∈ Submodule.span ℝ (Set.range v) := by rw [← range_emb]; exact ⟨a, rfl⟩
    exact h _ (hE hspan) ((emb_mem_orthogonal_iff hv hR a).2 ha)
  · intro h w hwE hwR
    obtain ⟨d, v, hv, hspan⟩ := exists_orthonormal_span (R1 x ⊔ ℝ ∙ w)
    have hR : R1 x ≤ Submodule.span ℝ (Set.range v) := hspan ▸ le_sup_left
    have hE : Submodule.span ℝ (Set.range v) ≤ Ev x :=
      hspan ▸ sup_le (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x) ((Submodule.span_singleton_le_iff_mem _ _).2 hwE)
    obtain ⟨a, rfl⟩ : w ∈ LinearMap.range (emb v) := by
      rw [range_emb, hspan]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
    have := h d v hv hR hE a ((emb_mem_orthogonal_iff hv hR a).1 hwR)
    rw [inner_opOn_self, ← norm_emb hv] at this
    exact this

/-! ### The tier -/

section Tier

variable {v : Fin d → Dom x}

/-- **The tier eigenvalues lie below the rung pencil**: for any `K`, with `k = dim(span v ∩ K)` and `i + k < dim R₁`,
`λ↑_i(Q|span v ∩ Kᗮ) ≤ λ↑_{i+k}(Q|R₁)`. -/
theorem eigAsc_tier_le (v : Fin d → Dom x) (K : Submodule ℝ (Dom x)) (i : Fin (finrank ℝ (inC v K)ᗮ))
    (hik : (i : ℕ) + finrank ℝ (inC v K) < finrank ℝ (inC v (R1 x))) :
    eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) i
      ≤ eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))) ⟨i + finrank ℝ (inC v K), hik⟩ :=
  Cvs.Upstream.CourantFischerInterlacing.eigAsc_compr_orthogonal_le (isSymmetric_opOn v) _ _ i hik

end Tier

/-! ### Tier conditions that give the floor -/

/-- **A floor on every tier test space gives `EvenBulkFloor`**: `b‖a‖² ≤ Q(a)` on `span v ∩ Kᗮ ∩ R₁ᗮ` whenever
`R₁ ≤ span v ≤ Ev x` and `dim R₁ − dim K < dim(span v ∩ Kᗮ)`, `K ≤ R₁`, gives `EvenBulkFloor x b`. -/
theorem evenBulkFloor_of_tier {K : Submodule ℝ (Dom x)} (hKR : K ≤ R1 x) {b : ℝ}
    (h : ∀ (d : ℕ) (v : Fin d → Dom x), Orthonormal ℝ v → R1 x ≤ Submodule.span ℝ (Set.range v) →
      Submodule.span ℝ (Set.range v) ≤ Ev x → finrank ℝ (R1 x) - finrank ℝ K < finrank ℝ (inC v K)ᗮ →
      ∀ a : (inC v K)ᗮ, (a : EuclideanSpace ℝ (Fin d)) ∈ (inC v (R1 x))ᗮ →
        b * ‖a‖ ^ 2 ≤ ⟪compr (opOn x v) (inC v K)ᗮ a, a⟫) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b := by
  refine (evenBulkFloor_iff_orthonormal b).2 fun d v hv hRF hFE a ha => ?_
  have hKF : K ≤ Submodule.span ℝ (Set.range v) := hKR.trans hRF
  have haK : a ∈ (inC v K)ᗮ := Submodule.orthogonal_le (Submodule.comap_mono hKR) ha
  by_cases ht : finrank ℝ (R1 x) - finrank ℝ K < finrank ℝ (inC v K)ᗮ
  · have := h d v hv hRF hFE ht ⟨a, haK⟩ ha
    rw [inner_compr] at this
    simpa using this
  · have h1 := Submodule.finrank_add_finrank_orthogonal (inC v K)
    have h2 := Submodule.finrank_add_finrank_orthogonal (inC v (R1 x))
    rw [finrank_inC hv hKF] at h1
    rw [finrank_inC hv hRF] at h2
    have h3 : finrank ℝ K ≤ finrank ℝ (R1 x) := Submodule.finrank_mono hKR
    dsimp only [inC] at h1 h2 ht ⊢
    have hz : finrank ℝ ((R1 x).comap (emb v))ᗮ = 0 := by omega
    have ha0 : a = 0 := by
      rw [Submodule.finrank_eq_zero] at hz
      rw [hz] at ha
      exact (Submodule.mem_bot ℝ).1 ha
    subst ha0
    simp

/-- **The tier angle condition** at `x` against `K ≤ R₁` with margin `b`: for every orthonormal `v` with
`R₁ ≤ span v ≤ Ev x`, with `H = span v ∩ Kᗮ`, `t = dim R₁ − dim K` and `E_t` the bottom `t` eigenvectors of `Q|H`,
every `a ∈ H ∩ R₁ᗮ` has `(λ↑_t − λ↑_0)‖P_{E_t}a‖² ≤ (λ↑_t − b)‖a‖²`. -/
def TierAngle (x : ℕ) (K : Submodule ℝ (Dom x)) (b : ℝ) : Prop :=
  ∀ (d : ℕ) (v : Fin d → Dom x), Orthonormal ℝ v → R1 x ≤ Submodule.span ℝ (Set.range v) →
    Submodule.span ℝ (Set.range v) ≤ Ev x →
    ∀ ht : finrank ℝ (R1 x) - finrank ℝ K < finrank ℝ (inC v K)ᗮ,
    ∀ a : (inC v K)ᗮ, (a : EuclideanSpace ℝ (Fin d)) ∈ (inC v (R1 x))ᗮ →
      (eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩
          - eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨0, Nat.zero_lt_of_lt ht⟩)
        * ‖(topSpace (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩)ᗮ.starProjection a‖ ^ 2
      ≤ (eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩ - b) * ‖a‖ ^ 2

/-- **The weighted tier angle condition**: as `TierAngle`, with the bottom weight charged at each eigenvalue,
`Σ_{j<t}(λ↑_t − λ↑_j)⟪u_j, a⟫² ≤ (λ↑_t − b)‖a‖²`. -/
def TierAngleW (x : ℕ) (K : Submodule ℝ (Dom x)) (b : ℝ) : Prop :=
  ∀ (d : ℕ) (v : Fin d → Dom x), Orthonormal ℝ v → R1 x ≤ Submodule.span ℝ (Set.range v) →
    Submodule.span ℝ (Set.range v) ≤ Ev x →
    ∀ ht : finrank ℝ (R1 x) - finrank ℝ K < finrank ℝ (inC v K)ᗮ,
    ∀ a : (inC v K)ᗮ, (a : EuclideanSpace ℝ (Fin d)) ∈ (inC v (R1 x))ᗮ →
      botDefect (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩ a
        ≤ (eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩ - b) * ‖a‖ ^ 2

/-- **`EvenBulkFloor` is the defect bound up to the surplus**: for `K ≤ R₁`, `EvenBulkFloor x b` iff on every tier
test space `Σ_{j<t}(λ↑_t − λ↑_j)⟪u_j, a⟫² ≤ (λ↑_t − b)‖a‖² + Σ_{j>t}(λ↑_j − λ↑_t)⟪u_j, a⟫²`. -/
theorem evenBulkFloor_iff_defect {K : Submodule ℝ (Dom x)} (hKR : K ≤ R1 x) (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b ↔ ∀ (d : ℕ) (v : Fin d → Dom x), Orthonormal ℝ v →
      R1 x ≤ Submodule.span ℝ (Set.range v) → Submodule.span ℝ (Set.range v) ≤ Ev x →
      ∀ ht : finrank ℝ (R1 x) - finrank ℝ K < finrank ℝ (inC v K)ᗮ,
      ∀ a : (inC v K)ᗮ, (a : EuclideanSpace ℝ (Fin d)) ∈ (inC v (R1 x))ᗮ →
        botDefect (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩ a
          ≤ (eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩ - b) * ‖a‖ ^ 2
            + topSurplus (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) ⟨_, ht⟩ a := by
  constructor
  · intro hb d v hv hRF hFE ht a ha
    refine (Cvs.Upstream.CourantFischerInterlacing.le_inner_iff_botDefect _ _ a b).1 ?_
    rw [inner_compr]
    simpa using (evenBulkFloor_iff_orthonormal b).1 hb d v hv hRF hFE a ha
  · intro h
    exact evenBulkFloor_of_tier hKR fun d v hv hRF hFE ht a ha =>
      (Cvs.Upstream.CourantFischerInterlacing.le_inner_iff_botDefect _ _ a b).2 (h d v hv hRF hFE ht a ha)

/-- **The weighted tier angle condition gives `EvenBulkFloor`**: `TierAngleW x K b` with `K ≤ R₁`. -/
theorem evenBulkFloor_of_tierAngleW {K : Submodule ℝ (Dom x)} (hKR : K ≤ R1 x) {b : ℝ}
    (h : TierAngleW x K b) : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b :=
  (evenBulkFloor_iff_defect hKR b).2 fun d v hv hRF hFE ht a ha =>
    (h d v hv hRF hFE ht a ha).trans (le_add_of_nonneg_right (Cvs.Upstream.CourantFischerInterlacing.topSurplus_nonneg _ _ _))

/-- **At `K = R₁` the weighted angle condition is `EvenBulkFloor`**: `t = 0`, so the defect vanishes. -/
theorem tierAngleW_R1_iff (x : ℕ) (b : ℝ) : TierAngleW x (R1 x) b ↔ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b := by
  refine ⟨evenBulkFloor_of_tierAngleW le_rfl, fun hb => ?_⟩
  intro d v hv hRF hFE ht a ha
  have h := (evenBulkFloor_iff_defect le_rfl b).1 hb d v hv hRF hFE ht a ha
  have hs : ((⟨_, ht⟩ : Fin (finrank ℝ (inC v (R1 x))ᗮ)) : ℕ) = 0 := Nat.sub_self _
  have h0 : botDefect (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))ᗮ) ⟨_, ht⟩ a = 0 :=
    Cvs.Upstream.CourantFischerInterlacing.botDefect_eq_zero _ hs a
  have hfl : b * ‖a‖ ^ 2 ≤ ⟪compr (opOn x v) (inC v (R1 x))ᗮ a, a⟫ := by
    rw [inner_compr]
    simpa using (evenBulkFloor_iff_orthonormal b).1 hb d v hv hRF hFE a a.2
  have hle : b ≤ eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))ᗮ) ⟨_, ht⟩ :=
    Cvs.Upstream.CourantFischerInterlacing.le_eigAsc_of_floor _ (V := ⊤) _ (by simp) fun c _ => by
      rw [inner_compr]
      simpa using (evenBulkFloor_iff_orthonormal b).1 hb d v hv hRF hFE c c.2
  rw [h0]
  exact mul_nonneg (sub_nonneg.2 hle) (sq_nonneg _)

/-! ### Test spaces -/

end Cvs.Route.RungTierWindowForm
