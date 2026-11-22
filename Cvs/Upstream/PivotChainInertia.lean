import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Upstream.BorderedDeterminantPivot
import Cvs.Upstream.ConstrainedFormPivotChain

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inertia count of the pivot chain

A `Q`-orthogonal basis `p_M` of `V` indexed by the active `M` counts the inertia: the negative index of `Q` on `V`
is `#{M : Q(p_M) < 0}` (Sylvester). It exists, unique at each active `M`, when `Q` is nondegenerate on each part of
`V` vanishing from an active `M` on; on the chain of Cvs.Upstream.ConstrainedFormPivotChain, `Q(p_M)` is the Schur pivot of Cvs.Upstream.BorderedDeterminantPivot.
`Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0` holds iff the negative index on `V_N` vanishes for every `N`, iff every intrinsic pivot is `≥ 0`.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.PivotChainInertia
open Cvs.ZeroCounting

section General

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The quadratic form `v ↦ vᵀQv`. -/
def qform (Q : Matrix ι ι ℝ) : QuadraticForm ℝ (ι → ℝ) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' ℝ Q)

theorem qform_apply (Q : Matrix ι ι ℝ) (v : ι → ℝ) : qform Q v = v ⬝ᵥ (Q *ᵥ v) := by
  simp [qform, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

/-- `M` is active in `V`: some `v ∈ V` vanishes above `M` and has `v_M = 1`. -/
def Active (V : Submodule ℝ (ι → ℝ)) (M : ι) : Prop :=
  ∃ v ∈ V, (∀ i, M < i → v i = 0) ∧ v M = 1

/-- A Schur system: for active `M`, `p_M ∈ V` vanishes above `M`, has `p_M(M) = 1`, and is `Q`-orthogonal to every
`u ∈ V` vanishing from `M` on. -/
def SchurSystem (Q : Matrix ι ι ℝ) (V : Submodule ℝ (ι → ℝ)) (p : ι → ι → ℝ) : Prop :=
  ∀ M, Active V M → p M ∈ V ∧ (∀ i, M < i → p M i = 0) ∧ p M M = 1 ∧
    ∀ u ∈ V, (∀ i, M ≤ i → u i = 0) → u ⬝ᵥ (Q *ᵥ p M) = 0

theorem exists_top {v : ι → ℝ} (h0 : v ≠ 0) : ∃ M, (∀ i, M < i → v i = 0) ∧ v M ≠ 0 := by
  classical
  have hS : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hne
    exact h0 (funext fun i => by_contra fun hi => hne ⟨i, by simpa using hi⟩)
  refine ⟨_, fun i hi => ?_, by simpa using Finset.max'_mem _ hS⟩
  by_contra hvi
  exact absurd hi (not_lt.mpr (Finset.le_max' _ i (by simp [hvi])))

omit [Fintype ι] in
theorem active_of {V : Submodule ℝ (ι → ℝ)} {v : ι → ℝ} (hv : v ∈ V) {M : ι} (htop : ∀ i, M < i → v i = 0)
    (hM : v M ≠ 0) : Active V M :=
  ⟨(v M)⁻¹ • v, V.smul_mem _ hv, fun i hi => by simp [htop i hi], by simp [inv_mul_cancel₀ hM]⟩

variable {Q : Matrix ι ι ℝ} {V : Submodule ℝ (ι → ℝ)} {p : ι → ι → ℝ}

/-- The Schur vectors as elements of `V`. -/
def fam (hp : SchurSystem Q V p) : {M // Active V M} → V := fun M => ⟨p M.1, (hp M.1 M.2).1⟩

theorem fam_linearIndependent (hp : SchurSystem Q V p) : LinearIndependent ℝ (fam hp) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  have hS : (Finset.univ.filter fun i => g i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := hne; exact ⟨i, by simp [hi]⟩
  set T := (Finset.univ.filter fun i => g i ≠ 0).max' hS
  have hT : g T ≠ 0 := by simpa using Finset.max'_mem _ hS
  have hcoord := congrArg (fun w : V => (w : ι → ℝ) T.1) hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_zero, Pi.zero_apply, fam] at hcoord
  rw [Finset.sum_eq_single T] at hcoord
  · rw [(hp T.1 T.2).2.2.1, mul_one] at hcoord; exact hT hcoord
  · intro b _ hb
    by_cases hgb : g b = 0
    · simp [hgb]
    · have hle : b ≤ T := Finset.le_max' _ b (by simp [hgb])
      have hlt : b.1 < T.1 := lt_of_le_of_ne hle (fun h => hb (Subtype.ext h))
      rw [(hp b.1 b.2).2.1 T.1 hlt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ T) h

theorem mem_span_of_top (hp : SchurSystem Q V p) :
    ∀ M : ι, ∀ v ∈ V, (∀ i, M < i → v i = 0) →
      v ∈ Submodule.span ℝ (Set.range fun a : {M // Active V M} => p a.1) := by
  intro M
  induction M using WellFoundedLT.induction with
  | _ M ih =>
    intro v hv htop
    set S := Submodule.span ℝ (Set.range fun a : {M // Active V M} => p a.1)
    -- `w = v − v_M p_M` (or `v` when `v_M = 0`) vanishes from `M` on
    have hw : ∃ w ∈ V, (∀ i, M ≤ i → w i = 0) ∧ (w ∈ S → v ∈ S) := by
      by_cases hM : v M = 0
      · refine ⟨v, hv, fun i hi => ?_, id⟩
        rcases hi.lt_or_eq with h | h
        · exact htop i h
        · rw [← h]; exact hM
      · have hA : Active V M := active_of hv htop hM
        obtain ⟨hpV, hptop, hp1, -⟩ := hp M hA
        refine ⟨v - v M • p M, V.sub_mem hv (V.smul_mem _ hpV), fun i hi => ?_, fun hwS => ?_⟩
        · rcases hi.lt_or_eq with h | h
          · simp [htop i h, hptop i h]
          · rw [← h]; simp [hp1]
        · have hpS : p M ∈ S := Submodule.subset_span ⟨⟨M, hA⟩, rfl⟩
          have := S.add_mem hwS (S.smul_mem (v M) hpS)
          simpa using this
    obtain ⟨w, hwV, hwtop, himp⟩ := hw
    refine himp ?_
    by_cases hw0 : w = 0
    · rw [hw0]; exact S.zero_mem
    · obtain ⟨M', hM'top, hM'⟩ := exists_top hw0
      have hlt : M' < M := by
        by_contra hge
        exact hM' (hwtop M' (not_lt.mp hge))
      exact ih M' hlt w hwV hM'top

theorem fam_span (hp : SchurSystem Q V p) : ⊤ ≤ Submodule.span ℝ (Set.range (fam hp)) := by
  rintro ⟨v, hv⟩ -
  have hvS : v ∈ Submodule.span ℝ (Set.range fun a : {M // Active V M} => p a.1) := by
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    · obtain ⟨M, htop, -⟩ := exists_top h0
      exact mem_span_of_top hp M v hv htop
  have himg : (Set.range fun a : {M // Active V M} => p a.1) = V.subtype '' Set.range (fam hp) := by
    rw [← Set.range_comp]; rfl
  rw [himg, Submodule.span_image, Submodule.mem_map] at hvS
  obtain ⟨y, hy, hyv⟩ := hvS
  have : y = ⟨v, hv⟩ := Subtype.ext hyv
  rwa [← this]

/-- The `Q`-orthogonal basis of `V` given by a Schur system. -/
def schurBasis (hp : SchurSystem Q V p) : Module.Basis {M // Active V M} ℝ V :=
  Module.Basis.mk (fam_linearIndependent hp) (fam_span hp)

theorem schurBasis_apply (hp : SchurSystem Q V p) (M : {M // Active V M}) :
    (schurBasis hp M : ι → ℝ) = p M.1 := by
  simp [schurBasis, fam]

theorem dot_eq_zero_of_lt (hp : SchurSystem Q V p) {a b : {M // Active V M}} (hab : a.1 < b.1) :
    p a.1 ⬝ᵥ (Q *ᵥ p b.1) = 0 :=
  (hp b.1 b.2).2.2.2 _ (hp a.1 a.2).1 fun i hi => (hp a.1 a.2).2.1 i (lt_of_lt_of_le hab hi)

omit [LinearOrder ι] in
theorem dot_symm (hQ : Qᵀ = Q) (x y : ι → ℝ) : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]

theorem schurBasis_isOrtho (hQ : Qᵀ = Q) (hp : SchurSystem Q V p) :
    (QuadraticMap.associated (R := ℝ) ((qform Q).restrict V)).IsOrthoᵢ (schurBasis hp) := by
  intro a b hab
  have hdot : p a.1 ⬝ᵥ (Q *ᵥ p b.1) = 0 := by
    rcases lt_or_gt_of_ne (fun h : a.1 = b.1 => hab (Subtype.ext h)) with h | h
    · exact dot_eq_zero_of_lt hp h
    · rw [dot_symm hQ]; exact dot_eq_zero_of_lt hp h
  have hdot' : p b.1 ⬝ᵥ (Q *ᵥ p a.1) = 0 := by rw [dot_symm hQ]; exact hdot
  show QuadraticMap.associated ((qform Q).restrict V) (schurBasis hp a) (schurBasis hp b) = 0
  rw [QuadraticMap.associated_apply]
  simp only [QuadraticMap.restrict_apply, Submodule.coe_add, schurBasis_apply, qform_apply, mulVec_add,
    dotProduct_add, add_dotProduct, hdot, hdot']
  simp

/-- **Sylvester for a Schur system**: the negative index of `Q` on `V` is the number of active `M` with
`Q(p_M) < 0`. -/
theorem sigNeg_eq_ncard (hQ : Qᵀ = Q) (hp : SchurSystem Q V p) :
    sigNeg ((qform Q).restrict V) = {M | Active V M ∧ p M ⬝ᵥ (Q *ᵥ p M) < 0}.ncard := by
  classical
  have e := ((qform Q).restrict V).isometryEquivBasisRepr (schurBasis hp)
  rw [QuadraticMap.basisRepr_eq_of_iIsOrtho _ _ (schurBasis_isOrtho hQ hp)] at e
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨e⟩]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext M
  simp only [Set.mem_image, Set.mem_ofPred_eq, QuadraticMap.restrict_apply, schurBasis_apply, qform_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨hA, h⟩; exact ⟨⟨M, hA⟩, h, rfl⟩

/-- **The positive index** likewise counts the active `M` with `Q(p_M) > 0`. -/
theorem sigPos_eq_ncard (hQ : Qᵀ = Q) (hp : SchurSystem Q V p) :
    sigPos ((qform Q).restrict V) = {M | Active V M ∧ 0 < p M ⬝ᵥ (Q *ᵥ p M)}.ncard := by
  classical
  have e := ((qform Q).restrict V).isometryEquivBasisRepr (schurBasis hp)
  rw [QuadraticMap.basisRepr_eq_of_iIsOrtho _ _ (schurBasis_isOrtho hQ hp)] at e
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares ⟨e⟩]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext M
  simp only [Set.mem_image, Set.mem_ofPred_eq, QuadraticMap.restrict_apply, schurBasis_apply, qform_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨hA, h⟩; exact ⟨⟨M, hA⟩, h, rfl⟩

/-! ### The intrinsic pivot -/

/-- The part of `V` vanishing from `M` on. -/
def lower (V : Submodule ℝ (ι → ℝ)) (M : ι) : Submodule ℝ (ι → ℝ) where
  carrier := {u | u ∈ V ∧ ∀ i, M ≤ i → u i = 0}
  add_mem' := fun ha hb => ⟨V.add_mem ha.1 hb.1, fun i hi => by simp [ha.2 i hi, hb.2 i hi]⟩
  zero_mem' := ⟨V.zero_mem, fun _ _ => rfl⟩
  smul_mem' := fun c u hu => ⟨V.smul_mem c hu.1, fun i hi => by simp [hu.2 i hi]⟩

omit [Fintype ι] in
theorem mem_lower {V : Submodule ℝ (ι → ℝ)} {M : ι} {u : ι → ℝ} :
    u ∈ lower V M ↔ u ∈ V ∧ ∀ i, M ≤ i → u i = 0 := Iff.rfl

/-- `Q` is nondegenerate on `W`: the only `u ∈ W` that is `Q`-orthogonal to all of `W` is `0`. -/
def NondegOn (Q : Matrix ι ι ℝ) (W : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ u ∈ W, (∀ u' ∈ W, u' ⬝ᵥ (Q *ᵥ u) = 0) → u = 0

omit [LinearOrder ι] in
/-- **Riesz on a nondegenerate subspace**: if `Q` is symmetric and nondegenerate on `W`, every functional
`u ↦ uᵀQv` on `W` is `u ↦ uᵀQw` for some `w ∈ W`. -/
theorem exists_orth_repr (hQ : Qᵀ = Q) {W : Submodule ℝ (ι → ℝ)} (hnd : NondegOn Q W)
    (v : ι → ℝ) : ∃ w ∈ W, ∀ u ∈ W, u ⬝ᵥ (Q *ᵥ w) = u ⬝ᵥ (Q *ᵥ v) := by
  classical
  let B : LinearMap.BilinForm ℝ W := (Matrix.toLinearMap₂' ℝ Q).compl₁₂ W.subtype W.subtype
  have hB : ∀ a b : W, B a b = (a : ι → ℝ) ⬝ᵥ (Q *ᵥ (b : ι → ℝ)) := fun a b => by
    simp [B, Matrix.toLinearMap₂'_apply']
  have hsymm : ∀ x y : ι → ℝ, x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  have hnB : B.Nondegenerate := by
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · refine Subtype.ext (hnd m m.2 fun u' hu' => ?_)
      have h := hm ⟨u', hu'⟩
      rw [hB, hsymm] at h
      exact h
    · refine Subtype.ext (hnd m m.2 fun u' hu' => ?_)
      have h := hm ⟨u', hu'⟩
      rwa [hB] at h
  let f : Module.Dual ℝ W := ((Matrix.toLinearMap₂' ℝ Q).flip v).comp W.subtype
  obtain ⟨w, hw⟩ := (B.toDual hnB).surjective f
  refine ⟨w, w.2, fun u hu => ?_⟩
  have := congrArg (fun g : Module.Dual ℝ W => g ⟨u, hu⟩) hw
  simp only [LinearMap.BilinForm.toDual_def, hB, f, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.flip_apply, Matrix.toLinearMap₂'_apply'] at this
  rw [hsymm]; exact this

/-- **A Schur system exists** when `Q` is symmetric and nondegenerate on `lower V M` for every active `M`. -/
theorem exists_schurSystem (hQ : Qᵀ = Q) (hnd : ∀ M, Active V M → NondegOn Q (lower V M)) :
    ∃ p : ι → ι → ℝ, SchurSystem Q V p := by
  classical
  have key : ∀ M, Active V M → ∃ q : ι → ℝ, q ∈ V ∧ (∀ i, M < i → q i = 0) ∧ q M = 1 ∧
      ∀ u ∈ V, (∀ i, M ≤ i → u i = 0) → u ⬝ᵥ (Q *ᵥ q) = 0 := by
    intro M hA
    obtain ⟨v, hv, hvtop, hv1⟩ := hA
    obtain ⟨w, hw, hrep⟩ := exists_orth_repr hQ (hnd M ⟨v, hv, hvtop, hv1⟩) v
    rw [mem_lower] at hw
    refine ⟨v - w, V.sub_mem hv hw.1, fun i hi => by simp [hvtop i hi, hw.2 i hi.le],
      by simp [hv1, hw.2 M le_rfl], fun u hu hutop => ?_⟩
    rw [mulVec_sub, dotProduct_sub, hrep u (mem_lower.mpr ⟨hu, hutop⟩), sub_self]
  refine ⟨fun M => if h : Active V M then Classical.choose (key M h) else 0, fun M hA => ?_⟩
  simp only [dif_pos hA]
  exact Classical.choose_spec (key M hA)

/-- **The Schur vector is unique** at every active `M` where `Q` is nondegenerate on `lower V M`. -/
theorem schurSystem_unique {p' : ι → ι → ℝ} {M : ι} (hA : Active V M) (hnd : NondegOn Q (lower V M))
    (hp : SchurSystem Q V p) (hp' : SchurSystem Q V p') : p M = p' M := by
  obtain ⟨h1, h2, h3, h4⟩ := hp M hA
  obtain ⟨h1', h2', h3', h4'⟩ := hp' M hA
  have hd : p M - p' M ∈ lower V M := mem_lower.mpr ⟨V.sub_mem h1 h1', fun i hi => by
    rcases hi.lt_or_eq with h | h
    · simp [h2 i h, h2' i h]
    · rw [← h]; simp [h3, h3']⟩
  have := hnd _ hd fun u hu => by
    rw [mem_lower] at hu
    rw [mulVec_sub, dotProduct_sub, h4 u hu.1 hu.2, h4' u hu.1 hu.2, sub_self]
  exact sub_eq_zero.mp this

open Classical in
/-- **The intrinsic pivot** `Q(p_M)` of the Schur vector at `M` (`0` when `V` carries no Schur system). -/
def ipiv (Q : Matrix ι ι ℝ) (V : Submodule ℝ (ι → ℝ)) (M : ι) : ℝ :=
  if h : ∃ p, SchurSystem Q V p then Classical.choose h M ⬝ᵥ (Q *ᵥ Classical.choose h M) else 0

/-- The intrinsic pivot is `Q(p_M)` for every Schur system `p`, at every active `M` where `Q` is nondegenerate on
`lower V M`. -/
theorem ipiv_eq {M : ι} (hA : Active V M) (hnd : NondegOn Q (lower V M)) (hp : SchurSystem Q V p) :
    ipiv Q V M = p M ⬝ᵥ (Q *ᵥ p M) := by
  classical
  have h : ∃ p, SchurSystem Q V p := ⟨p, hp⟩
  rw [ipiv, dif_pos h, schurSystem_unique hA hnd (Classical.choose_spec h) hp]

/-- Positive definiteness on `V` makes `Q` nondegenerate on every `lower V M`. -/
theorem nondegOn_lower_of_posDef (hpd : ∀ v ∈ V, v ≠ 0 → 0 < v ⬝ᵥ (Q *ᵥ v)) (M : ι) :
    NondegOn Q (lower V M) := by
  intro u hu horth
  by_contra h0
  have := hpd u (mem_lower.mp hu).1 h0
  rw [horth u hu] at this
  exact lt_irrefl _ this

/-- **The intrinsic inertia count**: for symmetric `Q`, nondegenerate on `lower V M` at every active `M`, the
negative index of `Q` on `V` is the number of active `M` with negative intrinsic pivot. -/
theorem sigNeg_eq_ncard_ipiv (hQ : Qᵀ = Q) (hnd : ∀ M, Active V M → NondegOn Q (lower V M)) :
    sigNeg ((qform Q).restrict V) = {M | Active V M ∧ ipiv Q V M < 0}.ncard := by
  obtain ⟨p, hp⟩ := exists_schurSystem hQ hnd
  rw [sigNeg_eq_ncard hQ hp]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨hA, h⟩ => ⟨hA, (ipiv_eq hA (hnd M hA) hp).symm ▸ h⟩,
    fun ⟨hA, h⟩ => ⟨hA, ipiv_eq hA (hnd M hA) hp ▸ h⟩⟩

/-- The positive index likewise counts the active `M` with positive intrinsic pivot. -/
theorem sigPos_eq_ncard_ipiv (hQ : Qᵀ = Q) (hnd : ∀ M, Active V M → NondegOn Q (lower V M)) :
    sigPos ((qform Q).restrict V) = {M | Active V M ∧ 0 < ipiv Q V M}.ncard := by
  obtain ⟨p, hp⟩ := exists_schurSystem hQ hnd
  rw [sigPos_eq_ncard hQ hp]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨hA, h⟩ => ⟨hA, (ipiv_eq hA (hnd M hA) hp).symm ▸ h⟩,
    fun ⟨hA, h⟩ => ⟨hA, ipiv_eq hA (hnd M hA) hp ▸ h⟩⟩

end General

/-! ### The negative index vanishes exactly on nonnegative forms -/

/-- **`sigNeg q = 0` iff `q ≥ 0`**, for a quadratic form on a finite-dimensional real space. -/
theorem sigNeg_eq_zero_iff {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) : sigNeg q = 0 ↔ ∀ v, 0 ≤ q v := by
  constructor
  · intro h v
    by_contra hv
    push Not at hv
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hneg : ((-q).restrict (ℝ ∙ v)).PosDef := by
      rintro ⟨y, hy⟩ hy0
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have ht : t ≠ 0 := by rintro rfl; exact hy0 (by simp)
      simp only [QuadraticMap.restrict_apply, _root_.neg_apply, QuadraticMap.map_smul, smul_eq_mul]
      nlinarith [mul_self_pos.mpr ht]
    have := le_sigNeg_of_negDef q hneg
    rw [finrank_span_singleton hv0, h] at this
    exact absurd this (by norm_num)
  · intro h
    obtain ⟨W, hW, hpd⟩ := exists_finrank_eq_sigNeg_and_negDef q
    rw [← hW]
    by_contra hne
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hne)
    have h1 := hpd x hx
    have h2 := h x
    simp only [QuadraticMap.restrict_apply, _root_.neg_apply] at h1
    linarith

/-! ### The chain of Cvs.Upstream.ConstrainedFormPivotChain -/

section Chain

open Cvs.Upstream.ConstrainedFormPivotChain (qf rows V mem_V zext restr zext_top zext_apply_lt restr_zext bil_restr qf_restr rows_mulVec_restr)
open Cvs.Upstream.BorderedDeterminantPivot (K blk schur amin amin_mem amin_orth qf_amin blk_transpose)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The chain pivots: `Q₀₀` at `M = 0` and the Schur pivot `κ'_M` of Cvs.Upstream.BorderedDeterminantPivot at `M ≥ 1`. -/
def piv (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) : ℕ → ℝ
  | 0 => Q 0 0
  | m + 1 => schur Q r m

/-- The chain vectors in `Fin (N+1)`: `e₀` at `M = 0` and the zero-extended minimiser `(−w, 1)` at `M ≥ 1`. -/
def chainVec (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (N : ℕ) : ℕ → Fin (N + 1) → ℝ
  | 0 => zext (fun _ : Fin 1 => (1 : ℝ))
  | m + 1 => zext (amin Q r m)

theorem chainVec_system (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) (N : ℕ)
    (hK : ∀ m, ∀ h : m + 1 < N + 1, Active (V r N) ⟨m + 1, h⟩ → IsUnit (K Q r m).det) :
    SchurSystem (blk Q N) (V r N) (fun M => chainVec Q r N M) ∧
      ∀ M : Fin (N + 1), Active (V r N) M →
        chainVec Q r N M ⬝ᵥ (blk Q N *ᵥ chainVec Q r N M) = piv Q r M := by
  have key : ∀ M : Fin (N + 1), Active (V r N) M →
      (chainVec Q r N M ∈ V r N ∧ (∀ i, M < i → chainVec Q r N M i = 0) ∧ chainVec Q r N M M = 1 ∧
        ∀ u ∈ V r N, (∀ i, M ≤ i → u i = 0) → u ⬝ᵥ (blk Q N *ᵥ chainVec Q r N M) = 0) ∧
      chainVec Q r N M ⬝ᵥ (blk Q N *ᵥ chainVec Q r N M) = piv Q r M := by
    rintro ⟨M, hMN⟩ hA
    cases M with
    | zero =>
      obtain ⟨v, hv, hvtop, hv1⟩ := hA
      have hv' : v = chainVec Q r N 0 := by
        funext i
        rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
        · have : i = ⟨0, hMN⟩ := Fin.ext h0
          rw [this, hv1]; simp [chainVec, zext]
        · rw [hvtop i hpos]; simp [chainVec, zext, show ¬ (i : ℕ) < 1 by omega]
      refine ⟨⟨hv' ▸ hv, fun i hi => zext_top (N := N) (fun _ : Fin 1 => (1 : ℝ)) i hi, by simp [chainVec, zext], fun u _ hu => ?_⟩, ?_⟩
      · have : u = 0 := funext fun i => hu i (Fin.zero_le i)
        rw [this, zero_dotProduct]
      · change qf Q N (zext (fun _ : Fin 1 => (1 : ℝ))) = Q 0 0
        rw [← qf_restr Q (by omega : 0 + 1 ≤ N + 1) (zext_top _), restr_zext]
        simp [qf, dotProduct, mulVec]
    | succ m =>
      have hK' := hK m hMN hA
      obtain ⟨hmem, h1⟩ := amin_mem Q r hK'
      have hle : m + 1 + 1 ≤ N + 1 := hMN
      have htop : ∀ i : Fin (N + 1), m + 1 < (i : ℕ) → (zext (amin Q r m) : Fin (N + 1) → ℝ) i = 0 := zext_top _
      refine ⟨⟨?_, fun i hi => zext_top _ i hi, ?_, fun u hu hutop => ?_⟩, ?_⟩
      · rw [mem_V]
        change rows r N *ᵥ zext (amin Q r m) = 0
        rw [← rows_mulVec_restr r hle htop, restr_zext]; exact mem_V.mp hmem
      · change (zext (amin Q r m) : Fin (N + 1) → ℝ) ⟨m + 1, hMN⟩ = 1
        rw [zext_apply_lt (amin Q r m) ⟨m + 1, hMN⟩ (Nat.lt_succ_self (m + 1))]
        exact (congrArg _ (Fin.ext rfl)).trans h1
      · have hutop' : ∀ i : Fin (N + 1), m + 1 < (i : ℕ) → u i = 0 := fun i hi =>
          hutop i (Fin.le_iff_val_le_val.mpr (le_of_lt hi))
        change u ⬝ᵥ (blk Q N *ᵥ zext (amin Q r m)) = 0
        rw [← bil_restr Q hle u hutop' htop, restr_zext]
        have hle' : m + 1 ≤ N + 1 := by omega
        have hutop'' : ∀ i : Fin (N + 1), m < (i : ℕ) → u i = 0 := fun i hi =>
          hutop i (Fin.le_iff_val_le_val.mpr hi)
        have hsnoc : restr hle u = Fin.snoc (restr hle' u) 0 := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · rw [Fin.snoc_last]; exact hutop _ (Fin.le_iff_val_le_val.mpr (le_refl _))
          · rw [Fin.snoc_castSucc]; rfl
        have hu' : restr hle' u ∈ V r m := by
          rw [mem_V, rows_mulVec_restr r hle' hutop'']; exact mem_V.mp hu
        rw [hsnoc]
        exact amin_orth Q r hK' hu'
      · change qf Q N (zext (amin Q r m)) = schur Q r m
        rw [← qf_restr Q hle htop, restr_zext, qf_amin Q hQ r hK']
  exact ⟨fun M hA => (key M hA).1, fun M hA => (key M hA).2⟩

/-- **The inertia count of the chain** (Haynsworth for the bordered chain): if every bordered matrix `K_{M−1}`
in front of an active `M ≥ 1` is invertible, the negative index of `Q_N` on `V_N` is the number of active `M ≤ N`
with negative Schur pivot `piv` (`Q₀₀` at `M = 0`, `det K_M / det K_{M−1}` at `M ≥ 1`), not pivot value `κ_M`. -/
theorem sigNeg_chain (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) (N : ℕ)
    (hK : ∀ m, ∀ h : m + 1 < N + 1, Active (V r N) ⟨m + 1, h⟩ → IsUnit (K Q r m).det) :
    sigNeg ((qform (blk Q N)).restrict (V r N)) = {M : Fin (N + 1) | Active (V r N) M ∧ piv Q r M < 0}.ncard := by
  obtain ⟨hp, hval⟩ := chainVec_system Q hQ r N hK
  rw [sigNeg_eq_ncard (blk_transpose Q hQ N) hp]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨hA, h⟩ => ⟨hA, hval M hA ▸ h⟩, fun ⟨hA, h⟩ => ⟨hA, (hval M hA).symm ▸ h⟩⟩

/-- The positive index of `Q_N` on `V_N` likewise counts the active `M` with positive pivot. -/
theorem sigPos_chain (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) (N : ℕ)
    (hK : ∀ m, ∀ h : m + 1 < N + 1, Active (V r N) ⟨m + 1, h⟩ → IsUnit (K Q r m).det) :
    sigPos ((qform (blk Q N)).restrict (V r N)) = {M : Fin (N + 1) | Active (V r N) M ∧ 0 < piv Q r M}.ncard := by
  obtain ⟨hp, hval⟩ := chainVec_system Q hQ r N hK
  rw [sigPos_eq_ncard (blk_transpose Q hQ N) hp]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun ⟨hA, h⟩ => ⟨hA, hval M hA ▸ h⟩, fun ⟨hA, h⟩ => ⟨hA, (hval M hA).symm ▸ h⟩⟩

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR cosQ_symm) in
/-- **The inertia count of the even bulk form**: at `1 < x`, with the bordered matrices of `cosQ x` against the
`R₁` rows `cosR x` invertible in front of every active `M ≥ 1`, the negative index of the order-`N` cosine-mode
window form on `V_N` is the number of active `M ≤ N` with negative pivot. -/
theorem sigNeg_cosQ {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ)
    (hK : ∀ m, ∀ h : m + 1 < N + 1, Active (V (cosR x) N) ⟨m + 1, h⟩ → IsUnit (K (cosQ x) (cosR x) m).det) :
    sigNeg ((qform (blk (cosQ x) N)).restrict (V (cosR x) N))
      = {M : Fin (N + 1) | Active (V (cosR x) N) M ∧ piv (cosQ x) (cosR x) M < 0}.ncard :=
  sigNeg_chain (cosQ x) (fun i j => cosQ_symm hx1 i j) (cosR x) N hK

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR cosQ_symm) in
/-- The positive index of the order-`N` cosine-mode window form on `V_N` counts the active `M ≤ N` with positive
pivot, with the bordered matrices of `cosQ x` against `cosR x` invertible in front of every active `M ≥ 1`. -/
theorem sigPos_cosQ {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ)
    (hK : ∀ m, ∀ h : m + 1 < N + 1, Active (V (cosR x) N) ⟨m + 1, h⟩ → IsUnit (K (cosQ x) (cosR x) m).det) :
    sigPos ((qform (blk (cosQ x) N)).restrict (V (cosR x) N))
      = {M : Fin (N + 1) | Active (V (cosR x) N) M ∧ 0 < piv (cosQ x) (cosR x) M}.ncard :=
  sigPos_chain (cosQ x) (fun i j => cosQ_symm hx1 i j) (cosR x) N hK

omit [Fintype κ] [DecidableEq κ] in
theorem qform_restrict_apply (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (N : ℕ) (a : V r N) :
    (qform (blk Q N)).restrict (V r N) a = qf Q N a := by
  rw [QuadraticMap.restrict_apply, qform_apply]; rfl

omit [Fintype κ] [DecidableEq κ] in
theorem nonneg_iff_sigNeg (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (N : ℕ) :
    (∀ a ∈ V r N, 0 ≤ qf Q N a) ↔ sigNeg ((qform (blk Q N)).restrict (V r N)) = 0 := by
  rw [sigNeg_eq_zero_iff]
  constructor
  · intro h a
    rw [QuadraticMap.restrict_apply, qform_apply]
    exact h a a.2
  · intro h a ha
    have := h ⟨a, ha⟩
    rwa [QuadraticMap.restrict_apply, qform_apply] at this

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR evenBulkFloor_zero_iff_kappa nonneg_iff_kappa) in
/-- **hF is the vanishing of the negative index**: at `1 < x`, `EvenBulkFloor x 0` holds iff the cosine-mode
window form `cosQ x` has negative index `0` on `V_N` at every truncation `N`. -/
theorem evenBulkFloor_zero_iff_sigNeg {x : ℕ} (hx1 : (1 : ℝ) < x) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 ↔ ∀ N, sigNeg ((qform (blk (cosQ x) N)).restrict (V (cosR x) N)) = 0 := by
  rw [evenBulkFloor_zero_iff_kappa hx1, ← nonneg_iff_kappa]
  exact forall_congr' fun N => nonneg_iff_sigNeg (cosQ x) (cosR x) N

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR) in
/-- **hF is the sign of the Schur pivots**: at `1 < x`, with the bordered matrices of `cosQ x` against `cosR x`
invertible in front of every active index at every truncation, `EvenBulkFloor x 0` holds iff every Schur pivot
at an active index is nonnegative. -/
theorem evenBulkFloor_zero_iff_piv {x : ℕ} (hx1 : (1 : ℝ) < x)
    (hK : ∀ N m, ∀ h : m + 1 < N + 1, Active (V (cosR x) N) ⟨m + 1, h⟩ →
      IsUnit (K (cosQ x) (cosR x) m).det) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 ↔
      ∀ N, ∀ M : Fin (N + 1), Active (V (cosR x) N) M → 0 ≤ piv (cosQ x) (cosR x) M := by
  rw [evenBulkFloor_zero_iff_sigNeg hx1]
  refine forall_congr' fun N => ?_
  rw [sigNeg_cosQ hx1 N (hK N), Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
  simp only [Set.mem_ofPred_eq, not_and, not_lt]

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR cosQ_symm) in
/-- **hF is the sign of the intrinsic pivots**: at `1 < x`, if `cosQ x` is nondegenerate on `lower V_N M` at every
active `M` of every truncation `N`, then `EvenBulkFloor x 0` holds iff every intrinsic pivot at an active index is
nonnegative. -/
theorem evenBulkFloor_zero_iff_ipiv {x : ℕ} (hx1 : (1 : ℝ) < x)
    (hnd : ∀ N, ∀ M : Fin (N + 1), Active (V (cosR x) N) M →
      NondegOn (blk (cosQ x) N) (lower (V (cosR x) N) M)) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 ↔
      ∀ N, ∀ M : Fin (N + 1), Active (V (cosR x) N) M → 0 ≤ ipiv (blk (cosQ x) N) (V (cosR x) N) M := by
  rw [evenBulkFloor_zero_iff_sigNeg hx1]
  refine forall_congr' fun N => ?_
  rw [sigNeg_eq_ncard_ipiv (blk_transpose _ (fun i j => cosQ_symm hx1 i j) N) (hnd N),
    Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
  simp only [Set.mem_ofPred_eq, not_and, not_lt]

end Chain

end Cvs.Upstream.PivotChainInertia
