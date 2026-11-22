import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ShiftedDiagonalSimplicity
import Cvs.Finite.TruncationQuadraticForm

/-!
# The discrete bottom of a symmetric matrix, without the spectral theorem

The form attains its minimum on the sphere; the shifted matrix is nonnegative; a nonnegative
symmetric form vanishing at `xi` annihilates `xi` (the first-order condition). With the involution
symmetry, an odd gap forces every bottom eigenvector to be even.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.SymmetricMatrixBottom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The sphere of coefficient vectors -/

/-- The unit sphere of coefficient vectors. -/
def sphere (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {v | v ⬝ᵥ v = 1}

omit [DecidableEq ι] in
theorem dotProduct_self_nonneg' (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq ι] in
theorem isClosed_sphere : IsClosed (sphere ι) :=
  isClosed_eq (by fun_prop) continuous_const

omit [DecidableEq ι] in
theorem isBounded_sphere : Bornology.IsBounded (sphere ι) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun v hv => ?_⟩
  have hv' : v ⬝ᵥ v = 1 := hv
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
  have : v i * v i ≤ v ⬝ᵥ v :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  rwa [hv'] at this

omit [DecidableEq ι] in
theorem isCompact_sphere : IsCompact (sphere ι) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_sphere isBounded_sphere

theorem sphere_nonempty [Nonempty ι] : (sphere ι).Nonempty :=
  ⟨Pi.single (Classical.arbitrary ι) 1, by
    show Pi.single (Classical.arbitrary ι) (1:ℝ) ⬝ᵥ Pi.single (Classical.arbitrary ι) 1 = 1
    simp⟩

/-- **The quadratic form attains its minimum on the sphere.** -/
theorem exists_min [Nonempty ι] (A : Matrix ι ι ℝ) :
    ∃ xi ∈ sphere ι, ∀ v ∈ sphere ι, xi ⬝ᵥ (A *ᵥ xi) ≤ v ⬝ᵥ (A *ᵥ v) := by
  obtain ⟨xi, hxi, hmin⟩ := isCompact_sphere.exists_isMinOn sphere_nonempty
    (f := fun v => v ⬝ᵥ (A *ᵥ v)) (by fun_prop : Continuous fun v : ι → ℝ => v ⬝ᵥ (A *ᵥ v)).continuousOn
  exact ⟨xi, hxi, fun v hv => hmin hv⟩

omit [DecidableEq ι] in
/-- **A lower bound on the sphere is a lower bound everywhere**, by scaling. -/
theorem quad_ge {A : Matrix ι ι ℝ} {lam : ℝ} (hmin : ∀ v ∈ sphere ι, lam ≤ v ⬝ᵥ (A *ᵥ v))
    (v : ι → ℝ) : lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  by_cases hv : v = 0
  · subst hv; simp
  · have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonneg' v)
      (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
    set c : ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ with hc
    have hcc : c * c = (v ⬝ᵥ v)⁻¹ := by rw [hc, ← mul_inv, Real.mul_self_sqrt hpos.le]
    have hmem : c • v ∈ sphere ι := by
      show (c • v) ⬝ᵥ (c • v) = 1
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc,
        inv_mul_cancel₀ hpos.ne']
    have h := hmin _ hmem
    rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      hcc] at h
    calc lam * (v ⬝ᵥ v) ≤ (v ⬝ᵥ v)⁻¹ * (v ⬝ᵥ (A *ᵥ v)) * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = v ⬝ᵥ (A *ᵥ v) := by field_simp

/-! ### The first-order condition -/

omit [DecidableEq ι] in
/-- A symmetric matrix's form is symmetric. -/
theorem dotProduct_mulVec_comm {N : Matrix ι ι ℝ} (hsymm : ∀ i j, N i j = N j i) (v w : ι → ℝ) :
    v ⬝ᵥ (N *ᵥ w) = w ⬝ᵥ (N *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have : Nᵀ = N := by ext i j; exact hsymm j i
  rw [this, dotProduct_comm]

/-- **A nonnegative symmetric form vanishing at `xi` annihilates `xi`.** -/
theorem mulVec_eq_zero_of_min {N : Matrix ι ι ℝ} (hsymm : ∀ i j, N i j = N j i)
    (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (N *ᵥ v)) {xi : ι → ℝ} (hxi : xi ⬝ᵥ (N *ᵥ xi) = 0) :
    N *ᵥ xi = 0 := by
  have hc : ∀ w : ι → ℝ, w ⬝ᵥ (N *ᵥ xi) = 0 := by
    intro w
    set c := w ⬝ᵥ (N *ᵥ xi) with hcdef
    set d := w ⬝ᵥ (N *ᵥ w) with hddef
    have hd : 0 ≤ d := hpsd w
    have key : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * d := by
      intro t
      have h := hpsd (xi + t • w)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
        dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct, hxi,
        dotProduct_mulVec_comm hsymm xi w] at h
      simp only [smul_eq_mul] at h
      rw [← hcdef, ← hddef] at h
      nlinarith [h]
    by_contra hne
    have hc2 : 0 < c ^ 2 := sq_pos_iff.mpr hne
    have hd1 : 0 < d + 1 := by linarith
    have h1 := key (-c / (d + 1))
    have h2 : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d
        = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
      field_simp; ring
    rw [h2] at h1
    have h3 : -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 < 0 := by
      apply div_neg_of_neg_of_pos
      · nlinarith
      · positivity
    linarith
  funext i
  have := hc (Pi.single i 1)
  rwa [single_dotProduct, one_mul] at this

/-! ### The discrete bottom -/

/-- **The bottom of a symmetric matrix**: a unit vector `xi` and a value `lam` with
`lam ≤` the form everywhere and `A xi = lam xi`. -/
theorem exists_bottom [Nonempty ι] {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) :
    ∃ (lam : ℝ) (xi : ι → ℝ), xi ⬝ᵥ xi = 1 ∧ (∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
      ∧ A *ᵥ xi = lam • xi := by
  obtain ⟨xi, hxi, hmin⟩ := exists_min A
  have hxi' : xi ⬝ᵥ xi = 1 := hxi
  set lam := xi ⬝ᵥ (A *ᵥ xi) with hlam
  have hge : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := quad_ge hmin
  refine ⟨lam, xi, hxi', hge, ?_⟩
  set N : Matrix ι ι ℝ := A - lam • (1 : Matrix ι ι ℝ) with hN
  have hNsymm : ∀ i j, N i j = N j i := by
    intro i j; simp only [hN, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hsymm i j,
      smul_eq_mul]
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hNform : ∀ v, v ⬝ᵥ (N *ᵥ v) = v ⬝ᵥ (A *ᵥ v) - lam * (v ⬝ᵥ v) := by
    intro v
    simp only [hN, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hNpsd : ∀ v, 0 ≤ v ⬝ᵥ (N *ᵥ v) := fun v => by rw [hNform]; linarith [hge v]
  have hNxi : xi ⬝ᵥ (N *ᵥ xi) = 0 := by rw [hNform, hxi', mul_one, hlam, sub_self]
  have h := mulVec_eq_zero_of_min hNsymm hNpsd hNxi
  rw [hN, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h

/-! ### The odd gap makes the bottom even -/

/-- **Under an odd gap, every `lam`-eigenvector is even.** -/
theorem oddPart_eq_zero_of_gap {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i)
    {neg : ι → ι} (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j)
    {lam : ℝ} (hge : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hgap : ∀ o : ι → ℝ, (∀ i, o (neg i) = -o i) → o ≠ 0 → lam * (o ⬝ᵥ o) < o ⬝ᵥ (A *ᵥ o))
    {v : ι → ℝ} (hv : A *ᵥ v = lam • v) :
    Cvs.Finite.TruncationQuadraticForm.oddPart neg v = 0 := by
  set N : Matrix ι ι ℝ := A - lam • (1 : Matrix ι ι ℝ) with hN
  have hNsymm : ∀ i j, N i j = N j i := by
    intro i j; simp only [hN, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hsymm i j,
      smul_eq_mul]
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hNneg : ∀ i j, N (neg i) (neg j) = N i j := by
    intro i j; simp only [hN, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hA,
      hinv.injective.eq_iff]
  have hNform : ∀ w, w ⬝ᵥ (N *ᵥ w) = w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w) := by
    intro w
    simp only [hN, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hNpsd : ∀ w, 0 ≤ w ⬝ᵥ (N *ᵥ w) := fun w => by rw [hNform]; linarith [hge w]
  have hNv : v ⬝ᵥ (N *ᵥ v) = 0 := by
    rw [hN, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, sub_self, dotProduct_zero]
  have hsplit := Cvs.Finite.TruncationQuadraticForm.dotProduct_mulVec_split hNsymm hinv hNneg v
  have he := hNpsd (Cvs.Finite.TruncationQuadraticForm.evenPart neg v)
  have ho := hNpsd (Cvs.Finite.TruncationQuadraticForm.oddPart neg v)
  have hoz : Cvs.Finite.TruncationQuadraticForm.oddPart neg v ⬝ᵥ (N *ᵥ Cvs.Finite.TruncationQuadraticForm.oddPart neg v) = 0 := by
    linarith
  by_contra hne
  have h1 := hgap _ (Cvs.Finite.TruncationQuadraticForm.oddPart_odd hinv v) hne
  rw [hNform] at hoz
  linarith

/-- **The kernel line, reduced to even vectors.** -/
theorem kerline_of_even {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i)
    {neg : ι → ι} (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j)
    {lam : ℝ} (hge : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hgap : ∀ o : ι → ℝ, (∀ i, o (neg i) = -o i) → o ≠ 0 → lam * (o ⬝ᵥ o) < o ⬝ᵥ (A *ᵥ o))
    {xi : ι → ℝ}
    (heven : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → A *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi) :
    ∀ v : ι → ℝ, A *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi := by
  intro v hv
  have ho := oddPart_eq_zero_of_gap hsymm hinv hA hge hgap hv
  have hveven : ∀ i, v (neg i) = v i := by
    intro i
    have := congrFun ho i
    simp only [Cvs.Finite.TruncationQuadraticForm.oddPart, Pi.zero_apply] at this
    linarith
  exact heven v hveven hv

/-- **Eigenvectors of `A` at `lam` are the kernel of the shifted matrix**, in `Cvs.Finite.TruncationZeroFreeOffAxes`'s form. -/
theorem shiftDiag_mulVec_eq_zero_iff (a b pos : ι → ℝ) (lam : ℝ) (v : ι → ℝ) :
    Cvs.Finite.DividedDifferenceCommutator.ddMatrix (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag a lam) b pos *ᵥ v = 0
      ↔ Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ v = lam • v := by
  rw [← Cvs.Finite.ShiftedDiagonalSimplicity.ddMatrix_sub_smul, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero]

/-- **The shifted form is the form less `lam` times the norm.** -/
theorem dotProduct_shiftDiag (a b pos : ι → ℝ) (lam : ℝ) (v : ι → ℝ) :
    v ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag a lam) b pos *ᵥ v)
      = v ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ v) - lam * (v ⬝ᵥ v) := by
  rw [← Cvs.Finite.ShiftedDiagonalSimplicity.ddMatrix_sub_smul, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

end Cvs.Upstream.SymmetricMatrixBottom
