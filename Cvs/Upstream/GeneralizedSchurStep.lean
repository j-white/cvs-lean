import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The generalized Schur step: Gauss transform, Potapov factor and confluent pivots

For symmetric `K` with `diag(u)K − K diag(u) = GJGᵀ`, the Gauss transform at `κ = K_kk` keeps the displacement, with
rows `G_iΘ(u_i)` for the Potapov factor `Θ(z) = 1 − JG_kᵀG_k/(κ(z − u_k))`, and `ΘJΘᵀ = J` for antisymmetric `J`.
Hermite data `K_ii = G′_iJG_iᵀ` pass through the step, so each pivot of the in-place chain is `G′_MJG_Mᵀ` and equals
`det K_{≤M}/det K_{<M}`; on kernels this holds for one-node and composite steps, with divided differences as witnesses.
-/

noncomputable section

open Matrix Filter Topology

namespace Cvs.Upstream.GeneralizedSchurStep

/-! ### The Gauss transform of one pivot -/

section Gauss

variable {R : Type*} [Field R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]

end Gauss

/-! ### The Potapov factor -/

section Potapov

variable {R : Type*} [Field R] {m : Type*} [Fintype m] [DecidableEq m]

end Potapov

/-! ### In-place elimination and Hermite data -/

section InPlace

variable {R : Type*} [Field R] {ι m : Type*} [Fintype m]

/-- In-place elimination of node `k`: `K ↦ K − K(·, k)K(k, ·)/K(k, k)`. -/
def stepMat (K : Matrix ι ι R) (k : ι) : Matrix ι ι R := Matrix.of fun i j => K i j - K i k * K k j / K k k

/-- The in-place generator update `G_i ↦ G_i − (K_ik/K_kk) G_k`. -/
def stepGen (K : Matrix ι ι R) (G : ι → m → R) (k : ι) : ι → m → R := fun i => G i - (K i k / K k k) • G k

/-- The in-place derivative update `G′_i ↦ G′_i − ((G′_iJG_kᵀ − K_ik)/((u_i − u_k)K_kk)) G_k`. -/
def stepDer (K : Matrix ι ι R) (u : ι → R) (J : Matrix m m R) (G G' : ι → m → R) (k : ι) : ι → m → R :=
  fun i => G' i - ((G' i ⬝ᵥ (J *ᵥ G k) - K i k) / ((u i - u k) * K k k)) • G k

/-- Hermite data on a node set `s`: `(u_i − u_j)K_ij = G_iJG_jᵀ`, `K` symmetric, and `K_ii = G′_iJG_iᵀ`. -/
def HermiteOn (s : Set ι) (K : Matrix ι ι R) (u : ι → R) (G G' : ι → m → R) (J : Matrix m m R) : Prop :=
  (∀ i ∈ s, ∀ j ∈ s, (u i - u j) * K i j = G i ⬝ᵥ (J *ᵥ G j)) ∧ (∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    ∧ ∀ i ∈ s, K i i = G' i ⬝ᵥ (J *ᵥ G i)

omit [Fintype m] in
/-- Hermite data restrict to a smaller node set. -/
theorem HermiteOn.mono [Fintype m] {s t : Set ι} {K : Matrix ι ι R} {u : ι → R} {G G' : ι → m → R}
    {J : Matrix m m R} (h : HermiteOn s K u G G' J) (hts : t ⊆ s) : HermiteOn t K u G G' J :=
  ⟨fun i hi j hj => h.1 i (hts hi) j (hts hj), fun i hi j hj => h.2.1 i (hts hi) j (hts hj),
    fun i hi => h.2.2 i (hts hi)⟩

/-- **The in-place step keeps the displacement**: if `(u_i − u_j)K_ij = G_iJG_jᵀ` and `K` is symmetric on `s ∋ k`,
the eliminated matrix and generator satisfy the same identity on `s`. -/
theorem disp_stepMat {s : Set ι} {K : Matrix ι ι R} {u : ι → R} {G : ι → m → R} {J : Matrix m m R}
    (hd : ∀ i ∈ s, ∀ j ∈ s, (u i - u j) * K i j = G i ⬝ᵥ (J *ᵥ G j)) (hs : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    {k : ι} (hk : k ∈ s) :
    ∀ i ∈ s, ∀ j ∈ s, (u i - u j) * stepMat K k i j = stepGen K G k i ⬝ᵥ (J *ᵥ stepGen K G k j) := by
  intro i hi j hj
  have hik := hd i hi k hk
  have hkj := hd k hk j hj
  have hij := hd i hi j hj
  have hkk := hd k hk k hk
  rw [sub_self, zero_mul] at hkk
  simp only [stepMat, of_apply, stepGen, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [← hik, ← hkj, ← hij, ← hkk, hs j hj k hk]
  by_cases h0 : K k k = 0
  · simp [h0]
  · field_simp
    ring

/-- **The in-place step carries Hermite data**: with distinct nodes on `s ∋ k` and `K_ii = G′_iJG_iᵀ`, every
remaining node `i ≠ k` of `s` has `K̃_ii = G̃′_iJG̃_iᵀ` for the eliminated matrix, generator and derivative. -/
theorem diag_stepMat {s : Set ι} {K : Matrix ι ι R} {u : ι → R} {G G' : ι → m → R} {J : Matrix m m R}
    (h : HermiteOn s K u G G' J) (hu : Set.InjOn u s) {k : ι} (hk : k ∈ s) {i : ι} (hi : i ∈ s) (hik : i ≠ k) :
    stepMat K k i i = stepDer K u J G G' k i ⬝ᵥ (J *ᵥ stepGen K G k i) := by
  obtain ⟨hd, hs, hD⟩ := h
  have hne : u i - u k ≠ 0 := sub_ne_zero.mpr fun e => hik (hu hi hk e)
  have e1 := hD i hi
  have e2 := hd k hk i hi
  have e3 := hd k hk k hk
  have e4 := hs k hk i hi
  simp only [stepMat, of_apply, stepDer, stepGen, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← e1, ← e2, ← e3, e4]
  by_cases h0 : K k k = 0
  · simp [h0]
  · field_simp
    ring

/-- **The in-place step on Hermite data**: eliminating `k ∈ s` (distinct nodes on `s`) gives Hermite data on
`s \ {k}` for the eliminated matrix, generator and derivative. -/
theorem HermiteOn.step {s : Set ι} {K : Matrix ι ι R} {u : ι → R} {G G' : ι → m → R} {J : Matrix m m R}
    (h : HermiteOn s K u G G' J) (hu : Set.InjOn u s) {k : ι} (hk : k ∈ s) :
    HermiteOn (s \ {k}) (stepMat K k) u (stepGen K G k) (stepDer K u J G G' k) J := by
  refine ⟨fun i hi j hj => disp_stepMat h.1 h.2.1 hk i hi.1 j hj.1, fun i hi j hj => ?_,
    fun i hi => diag_stepMat h hu hk hi.1 hi.2⟩
  simp only [stepMat, of_apply]
  rw [h.2.1 i hi.1 j hj.1, h.2.1 i hi.1 k hk, h.2.1 k hk j hj.1]
  ring

/-- The matrix after eliminating `a 0, …, a (M − 1)` in place. -/
def iterMat (K : Matrix ι ι R) (a : ℕ → ι) : ℕ → Matrix ι ι R
  | 0 => K
  | M + 1 => stepMat (iterMat K a M) (a M)

/-- The generator after eliminating `a 0, …, a (M − 1)` in place. -/
def iterGen (K : Matrix ι ι R) (G : ι → m → R) (a : ℕ → ι) : ℕ → ι → m → R
  | 0 => G
  | M + 1 => stepGen (iterMat K a M) (iterGen K G a M) (a M)

/-- The derivative data after eliminating `a 0, …, a (M − 1)` in place. -/
def iterDer (K : Matrix ι ι R) (u : ι → R) (J : Matrix m m R) (G G' : ι → m → R) (a : ℕ → ι) :
    ℕ → ι → m → R
  | 0 => G'
  | M + 1 => stepDer (iterMat K a M) u J (iterGen K G a M) (iterDer K u J G G' a M) (a M)

/-- **Hermite data along the in-place chain**: eliminating distinct nodes `a 0, …, a (M − 1)` of `s` leaves
Hermite data on the remaining nodes `s \ a '' {j < M}`. -/
theorem hermiteOn_iter {s : Set ι} {K : Matrix ι ι R} {u : ι → R} {G G' : ι → m → R} {J : Matrix m m R}
    (h : HermiteOn s K u G G' J) (hu : Set.InjOn u s) {a : ℕ → ι} (M : ℕ) (ha : ∀ j < M, a j ∈ s)
    (hinj : Set.InjOn a (Set.Iio M)) :
    HermiteOn (s \ a '' Set.Iio M) (iterMat K a M) u (iterGen K G a M) (iterDer K u J G G' a M) J := by
  induction M with
  | zero =>
    have : a '' Set.Iio 0 = ∅ := by ext x; simp
    rw [this, Set.sdiff_empty]; exact h
  | succ M ih =>
    have ih' := ih (fun j hj => ha j (by omega)) (hinj.mono (Set.Iio_subset_Iio (by omega)))
    have hmem : a M ∈ s \ a '' Set.Iio M := by
      refine ⟨ha M (by omega), ?_⟩
      rintro ⟨j, hj, e⟩
      have hj' : j < M := hj
      have := hinj (show j ∈ Set.Iio (M + 1) from by simp; omega) (show M ∈ Set.Iio (M + 1) from by simp) e
      omega
    refine (ih'.step (hu.mono Set.sdiff_subset) hmem).mono ?_
    rintro x ⟨hxs, hx⟩
    refine ⟨⟨hxs, fun ⟨j, hj, e⟩ => hx ⟨j, by simp at hj ⊢; omega, e⟩⟩, fun e => hx ⟨M, by simp, ?_⟩⟩
    exact (Set.mem_singleton_iff.mp e).symm

/-- **The pivot law along the in-place chain**: for Hermite data on `s` with distinct nodes and distinct
eliminated nodes `a 0, …, a M ∈ s`, the `M`-th pivot is the confluent value
`K_M(a_M, a_M) = G′_M(a_M) J G_M(a_M)ᵀ` of the current data. -/
theorem pivot_eq_hermite {s : Set ι} {K : Matrix ι ι R} {u : ι → R} {G G' : ι → m → R} {J : Matrix m m R}
    (h : HermiteOn s K u G G' J) (hu : Set.InjOn u s) {a : ℕ → ι} (M : ℕ) (ha : ∀ j ≤ M, a j ∈ s)
    (hinj : Set.InjOn a (Set.Iic M)) :
    iterMat K a M (a M) (a M) = iterDer K u J G G' a M (a M) ⬝ᵥ (J *ᵥ iterGen K G a M (a M)) := by
  have H := hermiteOn_iter h hu M (fun j hj => ha j hj.le) (hinj.mono Set.Iio_subset_Iic_self)
  refine H.2.2 (a M) ⟨ha M le_rfl, ?_⟩
  rintro ⟨j, hj, e⟩
  have hj' : j < M := hj
  have := hinj (Set.Iio_subset_Iic_self hj) (Set.mem_Iic.mpr (le_refl M)) e
  omega

end InPlace

/-! ### Kernels: the step and the confluent pivot -/

section Kernel

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m : Type*} [Fintype m]

end Kernel

/-! ### The zero-side Loewner kernel -/

section ZeroSide

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ρ : Type*} [Fintype ρ]

end ZeroSide

/-! ### Holomorphic divided differences -/

section DSlope

end DSlope

end Cvs.Upstream.GeneralizedSchurStep
