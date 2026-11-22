import Mathlib
import Cvs.StepA.Edge.CauchyPairingIdentity
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.EdgePencil
import Cvs.StepA.Edge.EdgePencilOperators
import Cvs.StepA.Edge.EdgeSpace
import Cvs.Upstream.RayleighQuotientExtremes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Vertices and their chains

At a vertex (`λ_max = −λ_min = σ > 0`, eigenspaces `E₊`, `E₋`) evaluation at `0` vanishes on exactly
one of `E₊`, `E₋`, and `E₊ ⊕ E₋` is the Krylov chain of a head `H` under `D`, alternating between
them; head and tail in `E₋` make a bottom-start chain `(q, q+1)`, head in `E₊` and tail in `E₋` a
top-start chain `(q, q)`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : EdgeData ι) (z : ι → ℂ)

/-- The top of the pencil, `σ = λ_max A(z)`. -/
def sig : ℝ := lamMax (opA P z)

/-- The top eigenspace `E₊ = ker(A − σ)`. -/
def Eplus : Submodule ℝ (EdgeV P) :=
  Module.End.eigenspace ((opA P z : EdgeV P →L[ℝ] EdgeV P) : Module.End ℝ (EdgeV P)) (sig P z)

/-- The eigenspace `E₋ = ker(A + σ)` at `−σ` (the bottom eigenspace at a vertex). -/
def Eminus : Submodule ℝ (EdgeV P) :=
  Module.End.eigenspace ((opA P z : EdgeV P →L[ℝ] EdgeV P) : Module.End ℝ (EdgeV P)) (-sig P z)

/-- `K₋ = E₋ ∩ ker κ`, the vectors of `E₋` vanishing at `0`. -/
def Kminus : Submodule ℝ (EdgeV P) := Eminus P z ⊓ (ℝ ∙ kap P)ᗮ

/-- A **vertex**: every weight is nonzero and the edge discriminant vanishes. -/
def IsVertex : Prop := (∀ i, z i ≠ 0) ∧ edgeDiscZ P.δ P.g z = 0

/-- The `κ`-order of `x`: the least `j` with `(Dʲx)(0) ≠ 0`. -/
def kOrd (x : EdgeV P) : ℕ := sInf {j : ℕ | ⟪kap P, (opD P ^ j) x⟫ ≠ 0}

/-- A **chain** of length `l` with head `H`: `H` is a nonzero extreme eigenvector,
`(DʲH)(0) = 0` for `j < l − 1`, `(D^{l−1}H)(0) ≠ 0`, and `H, …, D^{l−1}H` span `E₊ ⊔ E₋`. -/
def IsChain (H : EdgeV P) (l : ℕ) : Prop :=
  1 ≤ l ∧ H ≠ 0 ∧ (H ∈ Eplus P z ∨ H ∈ Eminus P z) ∧
    (∀ j, j + 1 < l → ⟪kap P, (opD P ^ j) H⟫ = 0) ∧ ⟪kap P, (opD P ^ (l - 1)) H⟫ ≠ 0 ∧
    Eplus P z ⊔ Eminus P z = Submodule.span ℝ (Set.range fun j : Fin l => (opD P ^ (j : ℕ)) H)

-- merged §0.4
/-- A **bottom-start vertex** of type `(q, q+1)`, `q ≥ 1`: some `H ∈ E₋` has
`(DʲH)(0) = 0` for `j < 2q`, `(D^{2q}H)(0) ≠ 0`, `E₋ = span{D^{2j}H}_{j ≤ q}` and
`E₊ = span{D^{2j+1}H}_{j < q}`. -/
def BottomStart : Prop :=
  IsVertex P z ∧ ∃ q : ℕ, 1 ≤ q ∧ ∃ H ∈ Eminus P z,
    (∀ j < 2 * q, ⟪kap P, (opD P ^ j) H⟫ = 0) ∧ ⟪kap P, (opD P ^ (2 * q)) H⟫ ≠ 0 ∧
    Eminus P z = Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ))) H) ∧
    Eplus P z = Submodule.span ℝ (Set.range fun j : Fin q => (opD P ^ (2 * (j : ℕ) + 1)) H)

-- odd-chains Theorem B
/-- A **top-start vertex** of type `(q, q)`, `q ≥ 1`: some `H ∈ E₊` has
`(DʲH)(0) = 0` for `j < 2q − 1`, `(D^{2q−1}H)(0) ≠ 0`, `E₊ = span{D^{2j}H}_{j < q}` and
`E₋ = span{D^{2j+1}H}_{j < q}`. -/
def TopStart : Prop :=
  IsVertex P z ∧ ∃ q : ℕ, 1 ≤ q ∧ ∃ H ∈ Eplus P z,
    (∀ j < 2 * q - 1, ⟪kap P, (opD P ^ j) H⟫ = 0) ∧ ⟪kap P, (opD P ^ (2 * q - 1)) H⟫ ≠ 0 ∧
    Eplus P z = Submodule.span ℝ (Set.range fun j : Fin q => (opD P ^ (2 * (j : ℕ))) H) ∧
    Eminus P z = Submodule.span ℝ (Set.range fun j : Fin q => (opD P ^ (2 * (j : ℕ) + 1)) H)

/-! ### Spectral data at a vertex -/

variable {P z}

theorem mem_Eplus {x : EdgeV P} : x ∈ Eplus P z ↔ opA P z x = sig P z • x :=
  Module.End.mem_eigenspace_iff

theorem mem_Eminus {x : EdgeV P} : x ∈ Eminus P z ↔ opA P z x = (-sig P z) • x :=
  Module.End.mem_eigenspace_iff

/-! ### Iterated reflection, orders and chains -/

/-- **Iterated reflection**: `Ax = μx` with `(Dʲx)(0) = 0` for `j < p` gives
`A(Dᵖx) = (−1)ᵖ μ Dᵖx`. -/
theorem opA_pow_opD_of_eig {x : EdgeV P} {μ : ℝ} (hx : opA P z x = μ • x) :
    ∀ p : ℕ, (∀ j < p, ⟪kap P, (opD P ^ j) x⟫ = 0) →
      opA P z ((opD P ^ p) x) = ((-1) ^ p * μ) • (opD P ^ p) x
  | 0, _ => by simpa using hx
  | p + 1, h => by
    have ih := opA_pow_opD_of_eig hx p fun j hj => h j (by omega)
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      opA_opD_of_eig P ih (h p (by omega)), pow_succ]
    congr 1
    ring

omit [DecidableEq ι] in
/-- The coefficient vector of a sum is the sum of the coefficient vectors. -/
private lemma vec_add (x y : EdgeV P) : (x + y).vec = x.vec + y.vec := rfl

omit [DecidableEq ι] in
/-- The coefficient vector of a difference is the difference of the coefficient vectors. -/
private lemma vec_sub (x y : EdgeV P) : (x - y).vec = x.vec - y.vec := rfl

omit [DecidableEq ι] in
/-- The coefficient vector of a real multiple is the multiple of the coefficient vector. -/
private lemma vec_smul (c : ℝ) (x : EdgeV P) : (c • x).vec = c • x.vec := rfl

omit [DecidableEq ι] in
/-- The coefficient vector of `0` is `0`. -/
private lemma vec_zero : (0 : EdgeV P).vec = 0 := rfl

omit [DecidableEq ι] in
/-- The coefficient vector of `Dx` is `edgeDer` of the coefficient vector of `x`. -/
private lemma vec_opD (x : EdgeV P) :
    (opD P x).vec = Cvs.StepA.Edge.CauchyPairingIdentity.edgeDer P.δ P.g x.vec := rfl

omit [DecidableEq ι] in
/-- `Dⁱ(Dʲx) = D^{i+j}x`. -/
private lemma opD_pow_apply_pow (i j : ℕ) (x : EdgeV P) :
    (opD P ^ i) ((opD P ^ j) x) = (opD P ^ (i + j)) x := by
  rw [pow_add, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

omit [DecidableEq ι] in
/-- `D` maps the Krylov space `span{Dʲx : j < n}` into `span{Dʲx : j < n + 1}`. -/
private lemma opD_mem_krylov {x y : EdgeV P} {n : ℕ}
    (hy : y ∈ Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio n)) :
    opD P y ∈ Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio (n + 1)) := by
  refine Submodule.span_induction
    (p := fun y _ => opD P y ∈ Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio (n + 1)))
    ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
    (fun c a _ ha => by rw [map_smul]; exact Submodule.smul_mem _ c ha) hy
  rintro _ ⟨j, hj, rfl⟩
  refine Submodule.subset_span ⟨j + 1, ?_, ?_⟩
  · simp only [Set.mem_Iio] at hj ⊢
    omega
  · simp only
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

/-- Multiplying block `i` by `∏_{j ∈ S} (g_j² − g_i²)` stays in the Krylov space
`span{Dʲx : j < 2|S| + 1}`: on block `i`, `(D − δ)² + g_j²` acts as `g_j² − g_i²`. -/
private lemma exists_blockScale_mem (x : EdgeV P) (S : Finset ι) :
    ∃ y ∈ Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio (2 * S.card + 1)),
      ∀ k : Fin 2 × ι, y.vec k = (∏ j ∈ S, (P.g j ^ 2 - P.g k.2 ^ 2)) * x.vec k := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨x, Submodule.subset_span ⟨0, by simp, by simp⟩, fun k => by simp⟩
  | insert a S ha ih =>
    obtain ⟨y, hyK, hy⟩ := ih
    refine ⟨opD P (opD P y) - (2 * P.δ) • opD P y + (P.δ ^ 2 + P.g a ^ 2) • y, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      have h1 := opD_mem_krylov hyK
      have h2 := opD_mem_krylov h1
      have hm : ∀ {n n' : ℕ}, n ≤ n' →
          Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio n)
            ≤ Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio n') := fun h =>
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))
      exact Submodule.add_mem _ (Submodule.sub_mem _ (hm (by omega) h2)
        (Submodule.smul_mem _ _ (hm (by omega) h1))) (Submodule.smul_mem _ _ (hm (by omega) hyK))
    · rintro ⟨e, i⟩
      rw [Finset.prod_insert ha]
      simp only [vec_add, vec_sub, vec_smul, vec_opD]
      fin_cases e <;> simp [Cvs.StepA.Edge.CauchyPairingIdentity.edgeDer, hy] <;> ring

/-- A nonzero `x` has `(Dʲx)(0) ≠ 0` for some `j < 2k`: the Krylov space reaches each block
separately, and on a block the values of `y` and `Dy` at `0` determine `y`. -/
private lemma exists_kap_pow_ne_zero_aux {x : EdgeV P} (hx : x ≠ 0) :
    ∃ j < 2 * Fintype.card ι, ⟪kap P, (opD P ^ j) x⟫ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hK : ∀ y ∈ Submodule.span ℝ ((fun j => (opD P ^ j) x) '' Set.Iio (2 * Fintype.card ι)),
      ⟪kap P, y⟫ = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => ⟪kap P, y⟫ = 0) ?_ (by simp)
      (fun a b _ _ ha hb => by rw [inner_add_right, ha, hb, add_zero])
      (fun c a _ ha => by rw [real_inner_smul_right, ha, mul_zero]) hy
    rintro _ ⟨j, hj, rfl⟩
    exact hcon j hj
  apply hx
  show x.vec = (0 : EdgeV P).vec
  rw [vec_zero]
  funext ⟨e, i⟩
  obtain ⟨y, hyK, hy⟩ := exists_blockScale_mem x (Finset.univ.erase i)
  have hcard : 2 * (Finset.univ.erase i).card + 1 + 1 = 2 * Fintype.card ι := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    have := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  have h1 : ⟪kap P, y⟫ = 0 :=
    hK y (Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega))) hyK)
  have h2 : ⟪kap P, opD P y⟫ = 0 := hK _ (by rw [← hcard]; exact opD_mem_krylov hyK)
  have hc : ∏ j ∈ Finset.univ.erase i, (P.g j ^ 2 - P.g i ^ 2) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj h
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hgj := P.hg0 j
    have hgi := P.hg0 i
    have hm : (P.g j - P.g i) * (P.g j + P.g i) = 0 := by linear_combination h
    have : P.g j = P.g i := by
      rcases mul_eq_zero.mp hm with h' | h'
      · linarith
      · linarith
    exact hji (P.hg this)
  have hz : ∀ i' ≠ i, ∏ j ∈ Finset.univ.erase i, (P.g j ^ 2 - P.g i' ^ 2) = 0 := fun i' hi' =>
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi', Finset.mem_univ _⟩) (sub_self _)
  rw [inner_kap, Cvs.StepA.Edge.CauchyPairingIdentity.edgeVal,
    Finset.sum_eq_single i (fun i' _ hi' => by rw [hy, hz i' hi', zero_mul]) (by simp)] at h1
  rw [inner_kap, vec_opD, Cvs.StepA.Edge.CauchyPairingIdentity.edgeVal,
    Finset.sum_eq_single i (fun i' _ hi' => by
      simp [Cvs.StepA.Edge.CauchyPairingIdentity.edgeDer, hy, hz i' hi']) (by simp)] at h2
  simp only [Cvs.StepA.Edge.CauchyPairingIdentity.edgeDer, hy] at h1 h2
  simp only [Matrix.cons_val_zero] at h2
  have hx0 : x.vec (0, i) = 0 := (mul_eq_zero.mp h1).resolve_left hc
  rw [hx0, mul_zero, mul_zero, zero_sub, neg_eq_zero] at h2
  have hx1 : x.vec (1, i) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (P.hg0 i).ne'
    · exact (mul_eq_zero.mp h).resolve_left hc
  fin_cases e
  · exact hx0
  · exact hx1

-- merged §1 T1, key lemma (R2 l.58, verifier R2 l.723): the frame diagonalises `D` with node
-- eigenvectors of value `1` at `0` (an earlier result node, Cvs.StepA.Edge.CauchyPairingIdentity sum_lift)
/-- **No `D`-invariant subspace vanishes at `0`**: a `D`-invariant `W ≤ ker κ` is `0`. -/
theorem eq_bot_of_invariant_le_ker {W : Submodule ℝ (EdgeV P)}
    (hW : ∀ x ∈ W, opD P x ∈ W) (hk : W ≤ (ℝ ∙ kap P)ᗮ) : W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  obtain ⟨j, -, hj⟩ := exists_kap_pow_ne_zero_aux hx0
  have hmem : ∀ j : ℕ, (opD P ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      exact hW _ ih
  exact hj ((Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hk (hmem j)))

-- merged §1 T1 (R2 l.50: ord ≤ 2k − 1, Cayley–Hamilton on the Krylov space)
/-- **Orders are finite**: a nonzero `x` has `(Dʲx)(0) ≠ 0` for some `j < 2k`. -/
theorem exists_kap_pow_ne_zero {x : EdgeV P} (hx : x ≠ 0) :
    ∃ j < 2 * Fintype.card ι, ⟪kap P, (opD P ^ j) x⟫ ≠ 0 := by
  exact exists_kap_pow_ne_zero_aux hx

/-- The order of a nonzero `x` is attained: `(D^{ord x} x)(0) ≠ 0` and `(Dʲx)(0) = 0` below it. -/
theorem kOrd_spec {x : EdgeV P} (hx : x ≠ 0) :
    ⟪kap P, (opD P ^ kOrd P x) x⟫ ≠ 0 ∧ ∀ j < kOrd P x, ⟪kap P, (opD P ^ j) x⟫ = 0 := by
  obtain ⟨j, -, hj⟩ := exists_kap_pow_ne_zero (P := P) hx
  have hne : {j : ℕ | ⟪kap P, (opD P ^ j) x⟫ ≠ 0}.Nonempty := ⟨j, hj⟩
  refine ⟨Nat.sInf_mem hne, fun i hi => ?_⟩
  by_contra h
  exact absurd (Nat.sInf_le h) (not_le.mpr hi)

-- merged §1 T1 (1b), R2 l.53: `(DF)^{(r)} = −F^{(r+1)}`

omit [DecidableEq ι] in
/-- The order is `p` when `(Dʲx)(0) = 0` for `j < p` and `(Dᵖx)(0) ≠ 0`. -/
private lemma kOrd_eq_of {x : EdgeV P} {p : ℕ} (h0 : ∀ j < p, ⟪kap P, (opD P ^ j) x⟫ = 0)
    (hp : ⟪kap P, (opD P ^ p) x⟫ ≠ 0) : kOrd P x = p := by
  refine le_antisymm (Nat.sInf_le hp) ?_
  by_contra hlt
  push Not at hlt
  exact Nat.sInf_mem (s := {j : ℕ | ⟪kap P, (opD P ^ j) x⟫ ≠ 0}) ⟨p, hp⟩ (h0 _ hlt)

/-- The order of a nonzero vector is below `2k`. -/
private lemma kOrd_lt {x : EdgeV P} (hx : x ≠ 0) : kOrd P x < 2 * Fintype.card ι := by
  obtain ⟨j, hj, hk⟩ := exists_kap_pow_ne_zero (P := P) hx
  exact lt_of_le_of_lt (Nat.sInf_le hk) hj

/-- A subspace containing a vector off the kernel of a functional `ℓ` has dimension one more than
its intersection with `ker ℓ`. -/
private lemma finrank_eq_finrank_inf_ker_add_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {U : Submodule ℝ E} (ℓ : E →ₗ[ℝ] ℝ) {x : E} (hxU : x ∈ U)
    (hx : ℓ x ≠ 0) :
    Module.finrank ℝ U = Module.finrank ℝ (U ⊓ LinearMap.ker ℓ : Submodule ℝ E) + 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hsup : (U ⊓ LinearMap.ker ℓ) ⊔ ℝ ∙ x = U := by
    refine le_antisymm (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hxU))
      fun u hu => ?_
    have e : u = (u - (ℓ u / ℓ x) • x) + (ℓ u / ℓ x) • x := by abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hu
      (Submodule.smul_mem _ _ hxU), ?_⟩)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
  have hinf : (U ⊓ LinearMap.ker ℓ) ⊓ ℝ ∙ x = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hyx⟩ := Submodule.mem_inf.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyx
    have hk := (Submodule.mem_inf.mp hy1).2
    rw [LinearMap.mem_ker, map_smul, smul_eq_mul] at hk
    rw [(mul_eq_zero.mp hk).resolve_right hx, zero_smul]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ LinearMap.ker ℓ) (ℝ ∙ x)
  rw [hsup, hinf, finrank_bot, finrank_span_singleton hx0] at h
  omega

open Classical in
/-- **Dimension by a flag of functionals**: if `ℓ₀, …, ℓ_{N−1}` vanish together only at `0` on
`W`, then `dim W` is the number of `ν < N` with `ℓ_ν ≠ 0` on `W ∩ ker ℓ₀ ∩ … ∩ ker ℓ_{ν−1}`. -/
private lemma finrank_eq_card_flag {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E) (ℓ : ℕ → E →ₗ[ℝ] ℝ) (N : ℕ)
    (hN : ∀ x ∈ W, (∀ j < N, ℓ j x = 0) → x = 0) :
    Module.finrank ℝ W
      = ((Finset.range N).filter fun ν => ∃ x ∈ W, (∀ j < ν, ℓ j x = 0) ∧ ℓ ν x ≠ 0).card := by
  let F : ℕ → Submodule ℝ E := fun ν => W ⊓ ⨅ j, ⨅ (_ : j < ν), LinearMap.ker (ℓ j)
  have hF : ∀ ν x, x ∈ F ν ↔ x ∈ W ∧ ∀ j < ν, ℓ j x = 0 := fun ν x => by
    simp [F, Submodule.mem_iInf]
  have hFs : ∀ ν, F (ν + 1) = F ν ⊓ LinearMap.ker (ℓ ν) := fun ν => by
    ext x
    rw [hF, Submodule.mem_inf, hF, LinearMap.mem_ker]
    constructor
    · rintro ⟨hW, h⟩
      exact ⟨⟨hW, fun j hj => h j (by omega)⟩, h ν (by omega)⟩
    · rintro ⟨⟨hW, h⟩, hν⟩
      refine ⟨hW, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h j hj
      · exact hν
  have hstep : ∀ ν, Module.finrank ℝ (F ν) = Module.finrank ℝ (F (ν + 1))
      + if ∃ x ∈ W, (∀ j < ν, ℓ j x = 0) ∧ ℓ ν x ≠ 0 then 1 else 0 := fun ν => by
    split_ifs with hO
    · obtain ⟨x, hxW, hx0, hxν⟩ := hO
      rw [hFs]
      exact finrank_eq_finrank_inf_ker_add_one (ℓ ν) ((hF ν x).mpr ⟨hxW, hx0⟩) hxν
    · rw [add_zero, hFs, inf_eq_left.mpr]
      intro x hx
      rw [LinearMap.mem_ker]
      by_contra hne
      exact hO ⟨x, ((hF ν x).mp hx).1, ((hF ν x).mp hx).2, hne⟩
  have hind : ∀ ν, Module.finrank ℝ W = Module.finrank ℝ (F ν)
      + ∑ p ∈ Finset.range ν, if ∃ x ∈ W, (∀ j < p, ℓ j x = 0) ∧ ℓ p x ≠ 0 then 1 else 0 := by
    intro ν
    induction ν with
    | zero =>
      have h0 : F 0 = W := by
        ext x
        rw [hF]
        simp
      rw [h0, Finset.range_zero, Finset.sum_empty, add_zero]
    | succ ν ih =>
      rw [ih, hstep ν, Finset.sum_range_succ]
      ring
  have hbot : F N = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hN x ((hF N x).mp hx).1 ((hF N x).mp hx).2
  rw [hind N, hbot, finrank_bot, zero_add, Finset.card_filter]

open Classical in
-- merged §1 T1, R2 l.49: the filtration `W ∩ F_ν` drops by at most one dimension per step
/-- **The orders of a subspace**: the nonzero elements of `W` have exactly `dim W` distinct
orders, all below `2k`. -/
theorem card_kOrd (W : Submodule ℝ (EdgeV P)) :
    ((Finset.range (2 * Fintype.card ι)).filter fun p => ∃ x ∈ W, x ≠ 0 ∧ kOrd P x = p).card
      = Module.finrank ℝ W := by
  let ℓ : ℕ → EdgeV P →ₗ[ℝ] ℝ := fun j =>
    ((innerSL ℝ (kap P)).comp (opD P ^ j) : EdgeV P →L[ℝ] ℝ)
  have hℓ : ∀ j x, ℓ j x = ⟪kap P, (opD P ^ j) x⟫ := fun j x => rfl
  rw [finrank_eq_card_flag W ℓ (2 * Fintype.card ι) (fun x _ h => by
    by_contra hx
    obtain ⟨j, hj, hk⟩ := exists_kap_pow_ne_zero (P := P) hx
    exact hk ((hℓ j x) ▸ h j hj))]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · rintro ⟨x, hxW, hx0, rfl⟩
    obtain ⟨h1, h2⟩ := kOrd_spec (P := P) hx0
    exact ⟨x, hxW, fun j hj => (hℓ j x).trans (h2 j hj), by rw [hℓ]; exact h1⟩
  · rintro ⟨x, hxW, h0, hp⟩
    rw [hℓ] at hp
    simp only [hℓ] at h0
    exact ⟨x, hxW, fun h => hp (by rw [h, map_zero, inner_zero_right]), kOrd_eq_of h0 hp⟩

/-- **Alternation along a chain**: `DʲH` lies in the space of `H` for even `j < l` and in the
other one for odd `j < l`. -/
theorem IsChain.mem {H : EdgeV P} {l : ℕ} (hc : IsChain P z H l) {j : ℕ} (hj : j < l) :
    (H ∈ Eplus P z → (opD P ^ j) H ∈ (if Even j then Eplus P z else Eminus P z)) ∧
    (H ∈ Eminus P z → (opD P ^ j) H ∈ (if Even j then Eminus P z else Eplus P z)) := by
  have hk : ∀ i < j, ⟪kap P, (opD P ^ i) H⟫ = 0 := fun i hi => hc.2.2.2.1 i (by omega)
  constructor
  · intro hH
    have h := opA_pow_opD_of_eig (mem_Eplus.mp hH) j hk
    split_ifs with he
    · rw [mem_Eplus, h, he.neg_one_pow, one_mul]
    · rw [mem_Eminus, h, (Nat.not_even_iff_odd.mp he).neg_one_pow, neg_one_mul]
  · intro hH
    have h := opA_pow_opD_of_eig (mem_Eminus.mp hH) j hk
    split_ifs with he
    · rw [mem_Eminus, h, he.neg_one_pow, one_mul]
    · rw [mem_Eplus, h, (Nat.not_even_iff_odd.mp he).neg_one_pow, neg_one_mul, neg_neg]

/-- At a bottom-start vertex `κ = 0` on `E₊`. -/
theorem BottomStart.kap_Eplus (hb : BottomStart P z) {x : EdgeV P} (hx : x ∈ Eplus P z) :
    ⟪kap P, x⟫ = 0 := by
  obtain ⟨-, q, -, H, -, h0, -, -, hp⟩ := hb
  rw [hp] at hx
  refine Submodule.span_induction (p := fun x _ => ⟪kap P, x⟫ = 0) ?_ (by simp)
    (fun x y _ _ hx hy => by rw [inner_add_right, hx, hy, add_zero])
    (fun a x _ hx => by rw [real_inner_smul_right, hx, mul_zero]) hx
  rintro _ ⟨j, rfl⟩
  exact h0 _ (by omega)

/-! ### Vertices -/

variable [Nonempty ι]

/-- At a vertex `σ > 0`. -/
theorem IsVertex.sig_pos (hv : IsVertex P z) : 0 < sig P z :=
  (lamMin_neg_lamMax_pos P ⟨Classical.arbitrary ι, hv.1 _⟩).2

/-- At a vertex `λ_min = −σ`. -/
theorem IsVertex.lamMin_eq (hv : IsVertex P z) : lamMin (opA P z) = -sig P z := by
  have h := hv.2
  rw [edgeDiscZ_eq] at h
  rw [sig]
  linarith

variable (P z) in
/-- `E₊ ≠ 0`. -/
theorem Eplus_ne_bot : Eplus P z ≠ ⊥ := by
  obtain ⟨x, hx, hAx⟩ := exists_eigen_lamMax (opA_isSelfAdjoint P z)
  exact (Submodule.ne_bot_iff _).mpr ⟨x, mem_Eplus.mpr hAx, hx⟩

/-- At a vertex `E₋ ≠ 0`. -/
theorem IsVertex.Eminus_ne_bot (hv : IsVertex P z) : Eminus P z ≠ ⊥ := by
  obtain ⟨x, hx, hAx⟩ := exists_eigen_lamMin (opA_isSelfAdjoint P z)
  rw [hv.lamMin_eq] at hAx
  exact (Submodule.ne_bot_iff _).mpr ⟨x, mem_Eminus.mpr hAx, hx⟩

/-- At a vertex `E₊ ⊥ E₋`. -/
theorem IsVertex.inner_eq_zero (hv : IsVertex P z) {x y : EdgeV P} (hx : x ∈ Eplus P z)
    (hy : y ∈ Eminus P z) : ⟪x, y⟫ = 0 := by
  have h := inner_opA_comm P z x y
  rw [mem_Eplus.mp hx, mem_Eminus.mp hy, real_inner_smul_left, real_inner_smul_right] at h
  have hs := hv.sig_pos
  nlinarith

/-- **T1(i), one side**: at a vertex `x(0) y(0) = 0` for `x ∈ E₊`, `y ∈ E₋`. -/
theorem IsVertex.kap_mul_eq_zero (hv : IsVertex P z) {x y : EdgeV P} (hx : x ∈ Eplus P z)
    (hy : y ∈ Eminus P z) : ⟪kap P, x⟫ * ⟪kap P, y⟫ = 0 := by
  have h := pairing P (mem_Eplus.mp hx) (mem_Eminus.mp hy)
  rw [add_neg_cancel, zero_mul] at h
  have hs := hv.sig_pos
  have : sig P z * (⟪kap P, x⟫ * ⟪kap P, y⟫) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left hs.ne'

omit [Nonempty ι] in
/-- A symmetric operator with nonnegative quadratic form is bounded below by some `c > 0` on the
orthogonal complement of any subspace containing its kernel. -/
private lemma exists_gap_of_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫)
    (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) {W : Submodule ℝ E} (hker : ∀ v, T v = 0 → v ∈ W) :
    ∃ c > 0, ∀ v ∈ Wᗮ, c * ‖v‖ ^ 2 ≤ ⟪T v, v⟫ := by
  have hzero : ∀ v, ⟪T v, v⟫ = 0 → T v = 0 := by
    intro v hv
    have h := hpos ((⟪T (T v), T v⟫ + 1) • v - ⟪T v, T v⟫ • T v)
    have hs : ⟪T (T v), v⟫ = ⟪T v, T v⟫ := by rw [hT, real_inner_comm]
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hv, hs] at h
    have hb := hpos (T v)
    have ha : ⟪T v, T v⟫ ^ 2 ≤ 0 := by nlinarith
    exact inner_self_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm ha (sq_nonneg _)))
  obtain ⟨c, hc, hle⟩ := exists_pos_le_on_sphere (W := Wᗮ) (f := fun v => ⟪T v, v⟫)
    ((T.continuous.inner continuous_id).continuousOn) (fun w hw hw1 => by
      rcases (hpos w).lt_or_eq with h | h
      · exact h
      · exfalso
        have hw0 : w ∈ W := hker w (hzero w h.symm)
        have : w = 0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hw0 hw)
        rw [this, norm_zero] at hw1
        exact zero_ne_one hw1)
  refine ⟨c, hc, fun v hv => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h1 := hle (‖v‖⁻¹ • v) (Submodule.smul_mem _ _ hv)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
  have e : ‖v‖⁻¹ * (‖v‖⁻¹ * ⟪T v, v⟫) = ⟪T v, v⟫ / ‖v‖ ^ 2 := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)] at h1
  exact h1

-- generic finite spectrum: `A` restricted to the invariant subspace `E₊ᗮ` has top `< σ`
variable (P z) in
/-- **The top gap**: `A ≤ σ − g` on `E₊ᗮ` for some `g > 0`. -/
theorem gap_top :
    ∃ g > 0, ∀ v ∈ (Eplus P z)ᗮ, ⟪opA P z v, v⟫ ≤ (sig P z - g) * ‖v‖ ^ 2 := by
  obtain ⟨c, hc, h⟩ := exists_gap_of_nonneg
    (T := sig P z • ContinuousLinearMap.id ℝ (EdgeV P) - opA P z)
    (fun x y => by
      simp only [sub_apply, smul_apply,
        ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, inner_opA_comm])
    (fun v => by
      have := inner_le_lamMax (opA P z) v
      simp only [sub_apply, smul_apply,
        ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      rw [sig]
      linarith)
    (W := Eplus P z) (fun v hv => by
      rw [mem_Eplus]
      simp only [sub_apply, smul_apply,
        ContinuousLinearMap.id_apply, sub_eq_zero] at hv
      exact hv.symm)
  refine ⟨c, hc, fun v hv => ?_⟩
  have := h v hv
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at this
  linarith

-- generic finite spectrum
/-- **The bottom gap**: at a vertex `A ≥ −σ + g` on `E₋ᗮ` for some `g > 0`. -/
theorem IsVertex.gap_bottom (hv : IsVertex P z) :
    ∃ g > 0, ∀ v ∈ (Eminus P z)ᗮ, (-sig P z + g) * ‖v‖ ^ 2 ≤ ⟪opA P z v, v⟫ := by
  obtain ⟨c, hc, h⟩ := exists_gap_of_nonneg
    (T := opA P z + sig P z • ContinuousLinearMap.id ℝ (EdgeV P))
    (fun x y => by
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, inner_opA_comm])
    (fun v => by
      have := lamMin_le_inner (opA P z) v
      rw [hv.lamMin_eq] at this
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      linarith)
    (W := Eminus P z) (fun v hv => by
      rw [mem_Eminus, neg_smul]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.id_apply] at hv
      exact eq_neg_of_add_eq_zero_left hv)
  refine ⟨c, hc, fun v hv' => ?_⟩
  have := h v hv'
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at this
  linarith

variable (P z) in
/-- **T1(i), the other side**: `κ` does not vanish on both `E₊` and `E₋`. -/
theorem not_kap_zero_both :
    ¬ (Eplus P z ≤ (ℝ ∙ kap P)ᗮ ∧ Eminus P z ≤ (ℝ ∙ kap P)ᗮ) := by
  rintro ⟨hp, hm⟩
  have hk0 : ∀ x ∈ Eplus P z ⊔ Eminus P z, ⟪kap P, x⟫ = 0 := fun x hx => by
    have := (sup_le hp hm) hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
    exact this
  have hinv : ∀ x ∈ Eplus P z ⊔ Eminus P z, opD P x ∈ Eplus P z ⊔ Eminus P z := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have ha0 : ⟪kap P, a⟫ = 0 := hk0 a (Submodule.mem_sup_left ha)
    have hb0 : ⟪kap P, b⟫ = 0 := hk0 b (Submodule.mem_sup_right hb)
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ?_)
    · exact mem_Eminus.mpr (opA_opD_of_eig P (mem_Eplus.mp ha) ha0)
    · rw [mem_Eplus, opA_opD_of_eig P (mem_Eminus.mp hb) hb0, neg_neg]
  have hbot := eq_bot_of_invariant_le_ker hinv (sup_le hp hm)
  exact Eplus_ne_bot P z (eq_bot_iff.mpr (le_sup_left.trans hbot.le))

-- T1 (1c)
/-- **Parity of orders**: at a vertex the orders of nonzero `x ∈ E₊` and `y ∈ E₋` have
odd sum. -/
theorem IsVertex.odd_kOrd_add (hv : IsVertex P z) {x y : EdgeV P} (hx : x ∈ Eplus P z)
    (hx0 : x ≠ 0) (hy : y ∈ Eminus P z) (hy0 : y ≠ 0) : Odd (kOrd P x + kOrd P y) := by
  obtain ⟨hxk, hxlt⟩ := kOrd_spec (P := P) hx0
  obtain ⟨hyk, hylt⟩ := kOrd_spec (P := P) hy0
  set p := kOrd P x
  set p' := kOrd P y
  have hAx := opA_pow_opD_of_eig (mem_Eplus.mp hx) p hxlt
  have hAy := opA_pow_opD_of_eig (mem_Eminus.mp hy) p' hylt
  have hpair := pairing P hAx hAy
  have hσ := hv.sig_pos
  by_contra hodd
  have hev : Even (p + p') := Nat.not_odd_iff_even.mp hodd
  have hsame : ((-1 : ℝ) ^ p) = (-1) ^ p' := by
    rcases Nat.even_add.mp hev with h
    by_cases hp : Even p
    · rw [hp.neg_one_pow, (h.mp hp).neg_one_pow]
    · have hp' : ¬ Even p' := fun h' => hp (h.mpr h')
      rw [(Nat.not_even_iff_odd.mp hp).neg_one_pow, (Nat.not_even_iff_odd.mp hp').neg_one_pow]
  rw [hsame, show (-1 : ℝ) ^ p' * sig P z + (-1) ^ p' * -sig P z = 0 by ring, zero_mul] at hpair
  have hν : (-1 : ℝ) ^ p' * -sig P z ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (neg_ne_zero.mpr hσ.ne')
  have : (-1 : ℝ) ^ p' * -sig P z * (⟪kap P, (opD P ^ p) x⟫ * ⟪kap P, (opD P ^ p') y⟫) = 0 := by
    linear_combination -hpair
  rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hν) with h | h
  · exact hxk h
  · exact hyk h

/-- At a vertex `E₊ ∩ E₋ = 0`. -/
private lemma IsVertex.eq_zero_of_mem (hv : IsVertex P z) {x : EdgeV P} (hp : x ∈ Eplus P z)
    (hm : x ∈ Eminus P z) : x = 0 :=
  inner_self_eq_zero.mp (hv.inner_eq_zero hp hm)

/-- At a vertex, subspaces `S₊ ≤ E₊` and `S₋ ≤ E₋` with `E₊ ⊔ E₋ ≤ S₊ ⊔ S₋` are `E₊` and `E₋`. -/
private lemma IsVertex.eq_of_sup_le (hv : IsVertex P z) {Sp Sm : Submodule ℝ (EdgeV P)}
    (hp : Sp ≤ Eplus P z) (hm : Sm ≤ Eminus P z) (h : Eplus P z ⊔ Eminus P z ≤ Sp ⊔ Sm) :
    Eplus P z = Sp ∧ Eminus P z = Sm := by
  constructor
  · refine le_antisymm (fun x hx => ?_) hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h (Submodule.mem_sup_left hx))
    have hb' : b = x - a := eq_sub_of_add_eq' hab
    have hb0 : b = 0 :=
      hv.eq_zero_of_mem (hb' ▸ Submodule.sub_mem _ hx (hp ha)) (hm hb)
    rw [hb0, add_zero] at hab
    exact hab ▸ ha
  · refine le_antisymm (fun x hx => ?_) hm
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h (Submodule.mem_sup_right hx))
    have ha' : a = x - b := eq_sub_of_add_eq hab
    have ha0 : a = 0 :=
      hv.eq_zero_of_mem (hp ha) (ha' ▸ Submodule.sub_mem _ hx (hm hb))
    rw [ha0, zero_add] at hab
    exact hab ▸ hb

-- merged §1 T1 (1d): orders are closed downward (`kOrd_opD`), single-parity (`odd_kOrd_add`) and
-- `dim E₊ + dim E₋` in number (`card_kOrd`), so they are `{0, …, l−1}`; the head of order `l − 1`
-- has a Krylov chain of distinct orders spanning `E₊ ⊕ E₋` (R2 l.53-68, verifier R2 l.723)
/-- **T1, the chain theorem**: at a vertex there is a chain. -/
theorem IsVertex.exists_chain (hv : IsVertex P z) : ∃ H l, IsChain P z H l := by
  classical
  let Op := (Finset.range (2 * Fintype.card ι)).filter
    fun p => ∃ x ∈ Eplus P z, x ≠ 0 ∧ kOrd P x = p
  let Om := (Finset.range (2 * Fintype.card ι)).filter
    fun p => ∃ x ∈ Eminus P z, x ≠ 0 ∧ kOrd P x = p
  have hne : (Op ∪ Om).Nonempty := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (Eplus_ne_bot P z)
    exact ⟨kOrd P x, Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (kOrd_lt hx0), x, hx, hx0, rfl⟩)⟩
  obtain ⟨H, hHpm, hH0, hHm⟩ : ∃ H, (H ∈ Eplus P z ∨ H ∈ Eminus P z) ∧ H ≠ 0 ∧
      kOrd P H = (Op ∪ Om).max' hne := by
    rcases Finset.mem_union.mp ((Op ∪ Om).max'_mem hne) with h | h
    · obtain ⟨-, x, hx, hx0, hxk⟩ := Finset.mem_filter.mp h
      exact ⟨x, Or.inl hx, hx0, hxk⟩
    · obtain ⟨-, x, hx, hx0, hxk⟩ := Finset.mem_filter.mp h
      exact ⟨x, Or.inr hx, hx0, hxk⟩
  set m := (Op ∪ Om).max' hne with hm_def
  obtain ⟨hk1, hk2⟩ := kOrd_spec (P := P) hH0
  rw [hHm] at hk1 hk2
  have hmn : m < 2 * Fintype.card ι := hHm ▸ kOrd_lt hH0
  refine ⟨H, m + 1, by omega, hH0, hHpm, fun j hj => hk2 j (by omega),
    by simpa using hk1, ?_⟩
  have hSle : Submodule.span ℝ (Set.range fun j : Fin (m + 1) => (opD P ^ (j : ℕ)) H)
      ≤ Eplus P z ⊔ Eminus P z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    have hz : ∀ i < (j : ℕ), ⟪kap P, (opD P ^ i) H⟫ = 0 := fun i hi => hk2 i (by omega)
    rcases hHpm with hH | hH
    · have h := opA_pow_opD_of_eig (mem_Eplus.mp hH) j hz
      rcases neg_one_pow_eq_or ℝ (j : ℕ) with h1 | h1
      · rw [h1, one_mul] at h
        exact Submodule.mem_sup_left (mem_Eplus.mpr h)
      · rw [h1, neg_one_mul] at h
        exact Submodule.mem_sup_right (mem_Eminus.mpr h)
    · have h := opA_pow_opD_of_eig (mem_Eminus.mp hH) j hz
      rcases neg_one_pow_eq_or ℝ (j : ℕ) with h1 | h1
      · rw [h1, one_mul] at h
        exact Submodule.mem_sup_right (mem_Eminus.mpr h)
      · rw [h1, neg_one_mul, neg_neg] at h
        exact Submodule.mem_sup_left (mem_Eplus.mpr h)
  refine (Submodule.eq_of_le_of_finrank_le hSle ?_).symm
  have hinf : Eplus P z ⊓ Eminus P z = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hv.eq_zero_of_mem (Submodule.mem_inf.mp hx).1 (Submodule.mem_inf.mp hx).2
  have hsum : Module.finrank ℝ ↥(Eplus P z ⊔ Eminus P z) = Op.card + Om.card := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Eplus P z) (Eminus P z)
    rw [hinf, finrank_bot, add_zero, ← card_kOrd (Eplus P z), ← card_kOrd (Eminus P z)] at h
    exact h
  have hdisj : Disjoint Op Om := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨-, x, hx, hx0, hxk⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, y, hy, hy0, hyk⟩ := Finset.mem_filter.mp hp'
    have hodd := hv.odd_kOrd_add hx hx0 hy hy0
    rw [hxk, hyk, ← two_mul] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (even_two_mul p)
  have hsub : Op ∪ Om ⊆ Finset.range (m + 1) := fun p hp =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((Op ∪ Om).le_max' p hp))
  have hsub' : Finset.range (m + 1) ⊆ (Finset.range (2 * Fintype.card ι)).filter fun p =>
      ∃ x ∈ Submodule.span ℝ (Set.range fun j : Fin (m + 1) => (opD P ^ (j : ℕ)) H),
        x ≠ 0 ∧ kOrd P x = p := by
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have hz : ∀ i < p, ⟪kap P, (opD P ^ i) ((opD P ^ (m - p)) H)⟫ = 0 := fun i hi => by
      rw [opD_pow_apply_pow]
      exact hk2 _ (by omega)
    have hnz : ⟪kap P, (opD P ^ p) ((opD P ^ (m - p)) H)⟫ ≠ 0 := by
      rw [opD_pow_apply_pow, show p + (m - p) = m by omega]
      exact hk1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (opD P ^ (m - p)) H,
      Submodule.subset_span ⟨⟨m - p, by omega⟩, rfl⟩, ?_, kOrd_eq_of hz hnz⟩
    rintro h
    rw [h, map_zero, inner_zero_right] at hnz
    exact hnz rfl
  rw [hsum, ← Finset.card_union_of_disjoint hdisj, ← card_kOrd]
  exact (Finset.card_le_card hsub).trans (Finset.card_le_card hsub')

-- merged §1 T1'
/-- **T1'**: a chain with head and tail in `E₋` makes a bottom-start vertex. -/
theorem IsChain.bottomStart (hv : IsVertex P z) {H : EdgeV P} {l : ℕ} (hc : IsChain P z H l)
    (hH : H ∈ Eminus P z) (ht : (opD P ^ (l - 1)) H ∈ Eminus P z) : BottomStart P z := by
  obtain ⟨hl, -, -, hk0, hkt, hspan⟩ := id hc
  have ht0 : (opD P ^ (l - 1)) H ≠ 0 := fun h => hkt (by rw [h, inner_zero_right])
  have hev : Even (l - 1) := by
    by_contra hodd
    have h := (hc.mem (j := l - 1) (by omega)).2 hH
    rw [if_neg hodd] at h
    exact ht0 (hv.eq_zero_of_mem h ht)
  obtain ⟨q, hq⟩ := hev
  have hSm : Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ))) H)
      ≤ Eminus P z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    have h := (hc.mem (j := 2 * (j : ℕ)) (by omega)).2 hH
    rwa [if_pos (even_two_mul _)] at h
  have hSp : Submodule.span ℝ (Set.range fun j : Fin q => (opD P ^ (2 * (j : ℕ) + 1)) H)
      ≤ Eplus P z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    have h := (hc.mem (j := 2 * (j : ℕ) + 1) (by omega)).2 hH
    rwa [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one _))] at h
  have hsup : Eplus P z ⊔ Eminus P z ≤
      Submodule.span ℝ (Set.range fun j : Fin q => (opD P ^ (2 * (j : ℕ) + 1)) H) ⊔
        Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ))) H) := by
    rw [hspan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    rcases Nat.even_or_odd (j : ℕ) with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩)
      simp only
      rw [hi, two_mul]
    · refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩)
      simp only
      rw [hi]
  obtain ⟨hEp, hEm⟩ := hv.eq_of_sup_le hSp hSm hsup
  obtain rfl | hq1 := Nat.eq_zero_or_pos q
  · exfalso
    apply Eplus_ne_bot P z
    rw [hEp]
    simp
  refine ⟨hv, q, hq1, H, hH, fun j hj => hk0 j (by omega), ?_, hEm, hEp⟩
  rw [show 2 * q = l - 1 by omega]
  exact hkt

-- odd-chains Theorem B setting (R2 l.225): even length `l = 2q`, head in `E₊`
/-- A chain with head in `E₊` and tail in `E₋` makes a top-start vertex. -/
theorem IsChain.topStart (hv : IsVertex P z) {H : EdgeV P} {l : ℕ} (hc : IsChain P z H l)
    (hH : H ∈ Eplus P z) (ht : (opD P ^ (l - 1)) H ∈ Eminus P z) : TopStart P z := by
  obtain ⟨hl, -, -, hk0, hkt, hspan⟩ := id hc
  have ht0 : (opD P ^ (l - 1)) H ≠ 0 := fun h => hkt (by rw [h, inner_zero_right])
  have hodd : ¬ Even (l - 1) := by
    intro hev
    have h := (hc.mem (j := l - 1) (by omega)).1 hH
    rw [if_pos hev] at h
    exact ht0 (hv.eq_zero_of_mem h ht)
  obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hodd
  have hSp : Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ))) H)
      ≤ Eplus P z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    have h := (hc.mem (j := 2 * (j : ℕ)) (by omega)).1 hH
    rwa [if_pos (even_two_mul _)] at h
  have hSm : Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ) + 1)) H)
      ≤ Eminus P z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    have h := (hc.mem (j := 2 * (j : ℕ) + 1) (by omega)).1 hH
    rwa [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one _))] at h
  have hsup : Eplus P z ⊔ Eminus P z ≤
      Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ))) H) ⊔
        Submodule.span ℝ (Set.range fun j : Fin (q + 1) => (opD P ^ (2 * (j : ℕ) + 1)) H) := by
    rw [hspan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj := j.isLt
    rcases Nat.even_or_odd (j : ℕ) with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩)
      simp only
      rw [hi, two_mul]
    · refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩)
      simp only
      rw [hi]
  obtain ⟨hEp, hEm⟩ := hv.eq_of_sup_le hSp hSm hsup
  refine ⟨hv, q + 1, by omega, H, hH, fun j hj => hk0 j (by omega), ?_, hEp, hEm⟩
  rw [show 2 * (q + 1) - 1 = l - 1 by omega]
  exact hkt

/-! ### Consequences of bottom start -/

-- odd-chains Theorem A Step 3 (R2 l.251-252, even-index `K₋`, verifier R2 l.701)
/-- **The Hardy membership**: at a bottom-start vertex `D⁻¹E₊ ⊆ K₋`. -/
theorem BottomStart.opDinv_mem_Kminus (hb : BottomStart P z) {w : EdgeV P}
    (hw : w ∈ Eplus P z) : opDinv P w ∈ Kminus P z := by
  obtain ⟨-, q, -, H, -, h0, -, hm, hp⟩ := hb
  rw [hp] at hw
  refine Submodule.span_induction (p := fun w _ => opDinv P w ∈ Kminus P z) ?_
    (by simp) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun a x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ a hx) hw
  rintro _ ⟨j, rfl⟩
  have hj := j.isLt
  have e : opDinv P ((opD P ^ (2 * (j : ℕ) + 1)) H) = (opD P ^ (2 * (j : ℕ))) H := by
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, opDinv_opD]
  simp only
  rw [e, Kminus, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [hm]
    exact Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h0 _ (by omega)

-- merged §2 hypothesis `dim E₋ ≥ 2` (`H, D²H` independent)
/-- At a bottom-start vertex `dim E₋ ≥ 2`. -/
theorem BottomStart.two_le_finrank (hb : BottomStart P z) :
    2 ≤ Module.finrank ℝ (Eminus P z) := by
  classical
  obtain ⟨-, q, hq, H, hH, h0, hne, hm, -⟩ := hb
  have hH0 : H ≠ 0 := fun h => hne (by rw [h, map_zero, inner_zero_right])
  have hD2 : (opD P ^ 2) H ∈ Eminus P z := by
    rw [hm]
    exact Submodule.subset_span ⟨⟨1, by omega⟩, by simp⟩
  have hk1 : kOrd P H = 2 * q := kOrd_eq_of h0 hne
  have hnz : ⟪kap P, (opD P ^ (2 * q - 2)) ((opD P ^ 2) H)⟫ ≠ 0 := by
    rw [opD_pow_apply_pow, show 2 * q - 2 + 2 = 2 * q by omega]
    exact hne
  have hk2 : kOrd P ((opD P ^ 2) H) = 2 * q - 2 :=
    kOrd_eq_of (fun j hj => by rw [opD_pow_apply_pow]; exact h0 _ (by omega)) hnz
  have hD20 : (opD P ^ 2) H ≠ 0 := fun h => hnz (by rw [h, map_zero, inner_zero_right])
  have hlt := kOrd_lt hH0
  rw [hk1] at hlt
  rw [← card_kOrd]
  calc 2 = ({2 * q - 2, 2 * q} : Finset ℕ).card := (Finset.card_pair (by omega)).symm
    _ ≤ _ := Finset.card_le_card fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      rcases hp with rfl | rfl
      · exact ⟨by omega, _, hD2, hD20, hk2⟩
      · exact ⟨hlt, H, hH, hH0, hk1⟩

-- odd-chains Theorem B, mirror of Step 3 (R2 l.287)
/-- **The Hardy membership, top start**: at a top-start vertex `D⁻¹E₋ ⊆ E₊ ∩ ker κ`. -/
theorem TopStart.opDinv_mem (ht : TopStart P z) {v : EdgeV P} (hv : v ∈ Eminus P z) :
    opDinv P v ∈ Eplus P z ∧ ⟪kap P, opDinv P v⟫ = 0 := by
  obtain ⟨-, q, -, H, -, h0, -, hp, hm⟩ := ht
  rw [hm] at hv
  refine Submodule.span_induction
    (p := fun v _ => opDinv P v ∈ Eplus P z ∧ ⟪kap P, opDinv P v⟫ = 0) ?_ ⟨by simp, by simp⟩
    (fun x y _ _ hx hy => ⟨by rw [map_add]; exact Submodule.add_mem _ hx.1 hy.1,
      by rw [map_add, inner_add_right, hx.2, hy.2, add_zero]⟩)
    (fun a x _ hx => ⟨by rw [map_smul]; exact Submodule.smul_mem _ a hx.1,
      by rw [map_smul, real_inner_smul_right, hx.2, mul_zero]⟩) hv
  rintro _ ⟨j, rfl⟩
  have hj := j.isLt
  have e : opDinv P ((opD P ^ (2 * (j : ℕ) + 1)) H) = (opD P ^ (2 * (j : ℕ))) H := by
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, opDinv_opD]
  simp only
  rw [e]
  refine ⟨?_, h0 _ (by omega)⟩
  rw [hp]
  exact Submodule.subset_span ⟨j, rfl⟩

end Cvs.StepA.Edge.PlanarBoxLemma
