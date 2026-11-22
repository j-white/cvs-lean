import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The divided-difference matrix and its commutator

    q i j = (b i − b j)/(pos i − pos j)  off the diagonal,  q i i = a i
    D·Q − Q·D = |β⟩⟨η| − |η⟩⟨β|,   β = b,  η = 1

with `D` the diagonal of `pos`.  RH.md §3.23 carries what this is for.
-/

noncomputable section

open Matrix

namespace Cvs.Finite.DividedDifferenceCommutator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-! ### The symmetry `γ`, and odd-against-even -/

omit [DecidableEq ι] in
/-- **An odd vector is orthogonal to an even one** — the two `γ`-eigenspaces are
orthogonal, which is what makes `⟨β, ξ⟩ = 0`. -/
theorem sum_odd_even {neg : ι → ι} (hinv : Function.Involutive neg)
    {u v : ι → ℝ} (hu : ∀ i, u (neg i) = -u i) (hv : ∀ i, v (neg i) = v i) :
    ∑ i, u i * v i = 0 := by
  have hre : ∑ i, u (neg i) * v (neg i) = ∑ i, u i * v i :=
    Equiv.sum_comp (hinv.toPerm) (fun x => u x * v x)
  have hneg : ∑ i, u (neg i) * v (neg i) = -∑ i, u i * v i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hu i, hv i]; ring
  linarith [hre, hneg]

/-! ### Lemma `key` -/

omit [DecidableEq ι] in
/-- Multiplying a rank one on the left. -/
theorem mul_vecMulVec (M : Matrix ι ι ℝ) (u v : ι → ℝ) :
    M * Matrix.vecMulVec u v = Matrix.vecMulVec (M.mulVec u) v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq ι] in
/-- Multiplying a rank one on the right, against a symmetric matrix. -/
theorem vecMulVec_mul_of_isSymm {M : Matrix ι ι ℝ} (hM : M.IsSymm) (u v : ι → ℝ) :
    Matrix.vecMulVec u v * M = Matrix.vecMulVec u (M.mulVec v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : M k j = M j k := by rw [← Matrix.IsSymm.apply hM]
  rw [this]; ring

variable {a b pos : ι → ℝ}

/-- The all-ones vector `η`. -/
def ones (ι : Type*) : ι → ℝ := fun _ => 1

/-- **The divided-difference matrix** — CvS `\eqref{form}`. -/
def ddMatrix (a b pos : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then a i else (b i - b j) / (pos i - pos j)

omit [Fintype ι] in
@[simp] theorem ddMatrix_diag (i : ι) : ddMatrix a b pos i i = a i := by
  simp [ddMatrix]

omit [Fintype ι] in
theorem ddMatrix_off {i j : ι} (h : i ≠ j) :
    ddMatrix a b pos i j = (b i - b j) / (pos i - pos j) := by
  simp [ddMatrix, h]

omit [Fintype ι] in
/-- **It is symmetric.** -/
theorem ddMatrix_isSymm : (ddMatrix a b pos).IsSymm := by
  ext i j
  by_cases h : i = j
  · subst h; rfl
  · rw [Matrix.transpose_apply, ddMatrix_off h, ddMatrix_off (Ne.symm h),
      ← neg_sub (b i) (b j), ← neg_sub (pos i) (pos j), neg_div_neg_eq]

/-- **Lemma `basics`(ii): the commutator is the rank-two `|β⟩⟨η| − |η⟩⟨β|`.**  The one
identity the whole finite-dimensional argument turns on. -/
theorem comm_eq (hpos : Function.Injective pos) (a b : ι → ℝ) :
    Matrix.diagonal pos * ddMatrix a b pos - ddMatrix a b pos * Matrix.diagonal pos
      = Matrix.vecMulVec b (ones ι) - Matrix.vecMulVec (ones ι) b := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.vecMulVec_apply, ones]
  by_cases h : i = j
  · subst h; simp; ring
  · rw [ddMatrix_off h]
    have hne : pos i - pos j ≠ 0 := sub_ne_zero.mpr (fun hc => h (hpos hc))
    field_simp

variable {neg : ι → ι} {xi : ι → ℝ}

omit [DecidableEq ι] in
/-- **`|u⟩⟨η|` acts as `u` on a normalised vector.** -/
theorem vecMulVec_ones_mulVec (u : ι → ℝ) (hnorm : ∑ i, xi i = 1) :
    Matrix.vecMulVec u (ones ι) *ᵥ xi = u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, ones]
  have hstep : ∑ k, u i * 1 * xi k = u i * ∑ k, xi k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hstep, hnorm, mul_one]

omit [Fintype ι] in
/-- **Lemma `basics`(i): `Q` commutes with the reflection `γ`.** -/
theorem comm_gamma (hneg : Function.Involutive neg)
    (ha : ∀ i, a (neg i) = a i) (hb : ∀ i, b (neg i) = -b i)
    (hp : ∀ i, pos (neg i) = -pos i) (i j : ι) :
    ddMatrix a b pos (neg i) (neg j) = ddMatrix a b pos i j := by
  by_cases h : i = j
  · subst h; simp [ddMatrix, ha]
  · have hn : neg i ≠ neg j := fun hc => h (hneg.injective hc)
    rw [ddMatrix_off hn, ddMatrix_off h, hb, hb, hp, hp]
    rw [show -b i - -b j = -(b i - b j) by ring, show -pos i - -pos j = -(pos i - pos j) by ring,
      neg_div_neg_eq]

/-- **Lemma `key`(i).**  `Q D ξ = −β`, from the commutator identity, `Qξ = 0`,
`⟨η,ξ⟩ = 1` and `⟨β,ξ⟩ = 0`. -/
theorem Q_mulVec_D_xi (hpos : Function.Injective pos) (hinv : Function.Involutive neg)
    (hb : ∀ i, b (neg i) = -b i) (hxi : ∀ i, xi (neg i) = xi i)
    (hQxi : (ddMatrix a b pos).mulVec xi = 0)
    (hnorm : ∑ i, xi i = 1) :
    (ddMatrix a b pos).mulVec ((Matrix.diagonal pos).mulVec xi) = -b := by
  have hcomm := congrArg (fun M => M.mulVec xi) (comm_eq hpos a b)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] at hcomm
  have h1 : Matrix.vecMulVec b (ones ι) *ᵥ xi = b := vecMulVec_ones_mulVec b hnorm
  have h2 : Matrix.vecMulVec (ones ι) b *ᵥ xi = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, ones]
    have hstep : ∑ k, 1 * b k * xi k = ∑ k, b k * xi k :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hstep]
    exact sum_odd_even hinv hb hxi
  rw [hQxi, Matrix.mulVec_zero, h1, h2, zero_sub, sub_zero] at hcomm
  exact neg_eq_iff_eq_neg.mp hcomm

/-- The perturbed operator `D' := D − |Dξ⟩⟨η|` of Lemma `key`. -/
def Dprime (pos xi : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal pos - Matrix.vecMulVec ((Matrix.diagonal pos).mulVec xi) (ones ι)

/-- **Lemma `key`(ii), in matrix form.**  `Q·D' = Dᵀ'·Q`, which is exactly selfadjointness
of `D'` for the inner product `⟨Qf, g⟩`. -/
theorem Q_mul_Dprime (hpos : Function.Injective pos) (hinv : Function.Involutive neg)
    (hb : ∀ i, b (neg i) = -b i) (hxi : ∀ i, xi (neg i) = xi i)
    (hQxi : (ddMatrix a b pos).mulVec xi = 0)
    (hnorm : ∑ i, xi i = 1) :
    ddMatrix a b pos * Dprime pos xi
      = (Dprime pos xi)ᵀ * ddMatrix a b pos := by
  have hQD := Q_mulVec_D_xi hpos hinv hb hxi hQxi hnorm
  have hsymm := ddMatrix_isSymm (a := a) (b := b) (pos := pos)
  have hcomm := comm_eq hpos a b
  -- left side
  have hL : ddMatrix a b pos * Dprime pos xi
      = ddMatrix a b pos * Matrix.diagonal pos + Matrix.vecMulVec b (ones ι) := by
    rw [Dprime, Matrix.mul_sub, mul_vecMulVec, hQD]
    ext i j
    simp [Matrix.vecMulVec_apply]
  -- right side
  have hR : (Dprime pos xi)ᵀ * ddMatrix a b pos
      = ddMatrix a b pos * Matrix.diagonal pos + Matrix.vecMulVec b (ones ι) := by
    rw [Dprime, Matrix.transpose_sub, Matrix.transpose_vecMulVec, Matrix.diagonal_transpose,
      Matrix.sub_mul, vecMulVec_mul_of_isSymm hsymm, hQD]
    have hDQ : Matrix.diagonal pos * ddMatrix a b pos
        = ddMatrix a b pos * Matrix.diagonal pos
          + (Matrix.vecMulVec b (ones ι) - Matrix.vecMulVec (ones ι) b) := by
      rw [← hcomm]; abel
    rw [hDQ]
    ext i j
    simp [Matrix.vecMulVec_apply, ones]
    ring
  rw [hL, hR]

/-- **`D' ξ = 0`** — the perturbation is built to kill `ξ`. -/
theorem Dprime_mulVec_xi (hnorm : ∑ i, xi i = 1) :
    Dprime pos xi *ᵥ xi = 0 := by
  rw [Dprime, Matrix.sub_mulVec, vecMulVec_ones_mulVec _ hnorm, sub_self]

end Cvs.Finite.DividedDifferenceCommutator
