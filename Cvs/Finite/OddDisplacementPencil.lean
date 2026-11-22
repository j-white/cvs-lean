import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenBottomRealRoots
import Cvs.Upstream.SymmetricMatrixBottom

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The odd displacement and the symmetric pencil on `H_W`

On odd vectors `ω_i²(Mv)_i − (M(ω²v))_i = b_i (ω·v) − ω_i (b·v)`, so `(W²u)ᵀMv = uᵀM(W²v)` on `ω^⊥`.
For symmetric involution-invariant `A ≥ 0` on odd vectors: the radical on `y^⊥` is the odd kernel,
and an odd `y` orthogonal to the odd kernel is in the odd range.
-/

noncomputable section

open Matrix

namespace Cvs.Finite.OddDisplacementPencil
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The odd displacement -/

-- H_fix Step 1.1 (Cvs.Finite.DisplacementIdentity.displacement applied twice, as Cvs.Finite.EvenBottomRealRoots.qdisplacement)
/-- **The displacement identity in `ω²`, on odd vectors**:
`ω_i²(Mv)_i − (M(ω²v))_i = b_i (ω·v) − ω_i (b·v)`. -/
theorem odd_displacement {a b ω : ι → ℝ} (hωinj : Function.Injective ω) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hω : ∀ i, ω (neg i) = -ω i) (hb : ∀ i, b (neg i) = -b i)
    {v : ι → ℝ} (hv : ∀ i, v (neg i) = -v i) (i : ι) :
    ω i ^ 2 * (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ v) i
      - (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ (fun j => ω j ^ 2 * v j)) i
      = b i * (ω ⬝ᵥ v) - ω i * (b ⬝ᵥ v) := by
  have h1 := Cvs.Finite.DisplacementIdentity.displacement (a := a) (b := b) hωinj v i
  have h2 := Cvs.Finite.DisplacementIdentity.displacement (a := a) (b := b) hωinj (fun j => ω j * v j) i
  have hs1 : ∑ j, v j = 0 := Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd hinv hv
  have hs2 : ∑ j, b j * (ω j * v j) = 0 :=
    Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd hinv (fun j => by rw [hb, hω, hv]; ring)
  have e : (fun j => ω j * (fun j => ω j * v j) j) = (fun j => ω j ^ 2 * v j) :=
    funext fun j => by ring
  rw [e] at h2
  beta_reduce at h1 h2
  rw [hs2] at h2
  rw [hs1] at h1
  simp only [dotProduct]
  linear_combination ω i * h1 + h2

/-- **The `W²`-pencil is symmetric on `ω^⊥`**: for odd `u, v` with `ω·u = ω·v = 0`,
`(W²u)ᵀMv = uᵀM(W²v)`. -/
theorem W2_dotProduct_mulVec_comm {a b ω : ι → ℝ} (hωinj : Function.Injective ω) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hω : ∀ i, ω (neg i) = -ω i) (hb : ∀ i, b (neg i) = -b i)
    {u v : ι → ℝ} (hv : ∀ i, v (neg i) = -v i) (hu0 : ω ⬝ᵥ u = 0) (hv0 : ω ⬝ᵥ v = 0) :
    (fun i => ω i ^ 2 * u i) ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ v)
      = u ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ (fun j => ω j ^ 2 * v j)) := by
  have hd := fun i => odd_displacement (a := a) hωinj hinv hω hb hv i
  have hu0' : ∑ i, u i * ω i = 0 := by
    rw [← hu0]; simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring
  simp only [dotProduct] at hv0 ⊢
  have key : ∀ i, u i * (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ (fun j => ω j ^ 2 * v j)) i
      = ω i ^ 2 * u i * (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ v) i
        + u i * ω i * (∑ j, b j * v j) := by
    intro i
    have h := hd i
    simp only [dotProduct, hv0, mul_zero, zero_sub] at h
    linear_combination (-u i) * h
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, ← Finset.sum_mul, hu0',
    zero_mul, add_zero]

/-! ### Odd vectors under a symmetric involution-invariant matrix -/

omit [DecidableEq ι] in
/-- A matrix commuting with the involution sends odd vectors to odd vectors. -/
theorem mulVec_odd {A : Matrix ι ι ℝ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) {v : ι → ℝ} (hv : ∀ i, v (neg i) = -v i) (i : ι) :
    (A *ᵥ v) (neg i) = -(A *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  rw [← Cvs.Finite.EvenBottomRealRoots.sum_neg_even hinv (fun j => A (neg i) j * v j), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [hA, hv]; ring

omit [DecidableEq ι] in
/-- **Nonnegative on odd vectors and zero at an odd vector forces the image to vanish.** -/
theorem mulVec_eq_zero_of_odd_psd {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j)
    (hpsd : ∀ v : ι → ℝ, (∀ i, v (neg i) = -v i) → 0 ≤ v ⬝ᵥ (A *ᵥ v))
    {v : ι → ℝ} (hv : ∀ i, v (neg i) = -v i) (h0 : v ⬝ᵥ (A *ᵥ v) = 0) : A *ᵥ v = 0 := by
  set w := A *ᵥ v with hwdef
  have hw : ∀ i, w (neg i) = -w i := mulVec_odd hinv hA hv
  have hwAv : w ⬝ᵥ (A *ᵥ v) = w ⬝ᵥ w := rfl
  have hvAw : v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ w := by
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm hsymm]
  have hexp : ∀ t : ℝ, (v + t • w) ⬝ᵥ (A *ᵥ (v + t • w))
      = v ⬝ᵥ (A *ᵥ v) + 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (A *ᵥ w)) := by
    intro t
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, hvAw, hwAv]
    simp only [smul_eq_mul]; ring
  by_contra hne
  have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' w)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  have hC := hpsd w hw
  set C := w ⬝ᵥ (A *ᵥ w)
  set s : ℝ := (w ⬝ᵥ w) / (C + 1) with hs
  have hC1 : 0 < C + 1 := by linarith
  have hs0 : 0 < s := div_pos hpos hC1
  have hsC : s * C ≤ w ⬝ᵥ w := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ hC1]; nlinarith
  have hev : ∀ i, (v + (-s) • w) (neg i) = -(v + (-s) • w) i := by
    intro i; simp [hv i, hw i]; ring
  have h := hpsd _ hev
  rw [hexp, h0] at h
  nlinarith

-- H_fix Step 1.2 (radical of `G` on `H_W` is `E ∩ H_W`)
/-- **The radical on `y^⊥`**: for symmetric, involution-invariant `A ≥ 0` on odd vectors, an odd
`v ⊥ y` with `uᵀAv = 0` for every odd `u ⊥ y` has `Av = 0`. -/
theorem mulVec_eq_zero_of_perp {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j)
    (hpsd : ∀ v : ι → ℝ, (∀ i, v (neg i) = -v i) → 0 ≤ v ⬝ᵥ (A *ᵥ v)) {y v : ι → ℝ}
    (hv : ∀ i, v (neg i) = -v i) (hyv : y ⬝ᵥ v = 0)
    (horth : ∀ u : ι → ℝ, (∀ i, u (neg i) = -u i) → y ⬝ᵥ u = 0 → u ⬝ᵥ (A *ᵥ v) = 0) :
    A *ᵥ v = 0 :=
  mulVec_eq_zero_of_odd_psd hsymm hinv hA hpsd hv (horth v hv hyv)

omit [DecidableEq ι] in
/-- A matrix commuting with the involution commutes with precomposition by it:
`(A (v ∘ neg))_i = (Av)_{neg i}`. -/
private theorem mulVec_comp_neg {A : Matrix ι ι ℝ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) (v : ι → ℝ) (i : ι) :
    (A *ᵥ (fun j => v (neg j))) i = (A *ᵥ v) (neg i) := by
  simp only [mulVec, dotProduct]
  rw [← Cvs.Finite.EvenBottomRealRoots.sum_neg_even hinv (fun j => A i j * v (neg j))]
  exact Finset.sum_congr rfl fun j _ => by rw [hinv j, ← hA (neg i) j, hinv i]

omit [DecidableEq ι] in
/-- The odd part `(v − v ∘ neg)/2` of a vector, under a matrix commuting with the involution:
`(A v_odd)_i = ((Av)_i − (Av)_{neg i})/2`. -/
private theorem mulVec_oddPart {A : Matrix ι ι ℝ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) (v : ι → ℝ) (i : ι) :
    (A *ᵥ (fun j => (v j - v (neg j)) / 2)) i = ((A *ᵥ v) i - (A *ᵥ v) (neg i)) / 2 := by
  have e : (fun j => (v j - v (neg j)) / 2) = (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • fun j => v (neg j) :=
    funext fun j => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, mulVec_sub, mulVec_smul, mulVec_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
    mulVec_comp_neg hinv hA, smul_eq_mul, smul_eq_mul]
  ring

-- H_fix Step 1.3 (pivot `w` with `(M − μ)w = η` when `E ⊆ H_W`)
/-- **The odd Fredholm alternative**: for symmetric involution-invariant `A`, an odd `y` orthogonal to
every odd vector of the kernel is `Aw` for an odd `w`. -/
theorem exists_odd_mulVec_eq {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j) {y : ι → ℝ}
    (hy : ∀ i, y (neg i) = -y i)
    (hker : ∀ v : ι → ℝ, (∀ i, v (neg i) = -v i) → A *ᵥ v = 0 → y ⬝ᵥ v = 0) :
    ∃ w : ι → ℝ, (∀ i, w (neg i) = -w i) ∧ A *ᵥ w = y := by
  -- `y` is orthogonal to the whole kernel: the odd part of a kernel vector is in the kernel
  have hperp : ∀ k : ι → ℝ, A *ᵥ k = 0 → y ⬝ᵥ k = 0 := by
    intro k hk
    have hko : ∀ i,
        (fun j => (k j - k (neg j)) / 2) (neg i) = -(fun j => (k j - k (neg j)) / 2) i :=
      fun i => by simp only [hinv i]; ring
    have hAko : A *ᵥ (fun j => (k j - k (neg j)) / 2) = 0 := by
      funext i; rw [mulVec_oddPart hinv hA, hk]; simp
    have h1 := hker _ hko hAko
    have h2 : y ⬝ᵥ k - y ⬝ᵥ (fun j => (k j - k (neg j)) / 2) = 0 := by
      rw [← dotProduct_sub]
      simp only [dotProduct]
      exact Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd hinv
        (fun i => by simp only [Pi.sub_apply, hy i, hinv i]; ring)
    linarith
  -- on `EuclideanSpace`, `A` is self-adjoint and its range is the orthogonal of its kernel
  have hadj : (Matrix.toEuclideanLin A).adjoint = Matrix.toEuclideanLin A := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hsymm j i]
  have hy' : (WithLp.toLp 2 y : EuclideanSpace ℝ ι) ∈ (Matrix.toEuclideanLin A).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have hk' : A *ᵥ WithLp.ofLp k = 0 := by
      have := congrArg WithLp.ofLp hk
      simpa [Matrix.ofLp_toLpLin] using this
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa using hperp _ hk'
  rw [LinearMap.orthogonal_ker, hadj] at hy'
  obtain ⟨w', hw'⟩ := hy'
  have hw : A *ᵥ WithLp.ofLp w' = y := by
    have := congrArg WithLp.ofLp hw'
    simpa [Matrix.ofLp_toLpLin] using this
  -- the odd part of a preimage is an odd preimage
  refine ⟨fun j => (WithLp.ofLp w' j - WithLp.ofLp w' (neg j)) / 2,
    fun i => by simp only [hinv i]; ring, ?_⟩
  funext i
  rw [mulVec_oddPart hinv hA, hw, hy i]
  ring

end Cvs.Finite.OddDisplacementPencil
