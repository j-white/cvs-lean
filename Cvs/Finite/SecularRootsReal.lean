import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EigenvectorFormRealSpectrum

/-!
# The secular roots are real

Eigenvectors of `D'` are the explicit `rootVec`, whose entries are `ξ_j/(pos_j − s)`; feeding
a complex root through the real/imaginary split of `finmain`(i) forces its imaginary part to
vanish.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix Cvs.Finite.DividedDifferenceCommutator Cvs.Finite.SelfAdjointRealSpectrum Cvs.Finite.EigenvectorFormRealSpectrum

namespace Cvs.Finite.SecularRootsReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The construction over an arbitrary field -/

section Gen

variable {K : Type*} [Field K]

/-- `D' = D − |Dξ⟩⟨η|` over an arbitrary field. -/
def DprimeGen (pos xi : ι → K) : Matrix ι ι K :=
  Matrix.diagonal pos - Matrix.vecMulVec (fun i => pos i * xi i) (fun _ => 1)

/-- **`D'` acts componentwise up to the mean.** -/
theorem DprimeGen_mulVec_apply (pos xi u : ι → K) (i : ι) :
    (DprimeGen pos xi *ᵥ u) i = pos i * u i - pos i * xi i * ∑ k, u k := by
  have hrank : (Matrix.vecMulVec (fun i => pos i * xi i) (fun _ => (1 : K)) *ᵥ u) i
      = pos i * xi i * ∑ k, u k := by
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum]
  simp [DprimeGen, Matrix.sub_mulVec, Matrix.mulVec_diagonal, hrank]

/-- **The eigenvector attached to a root**, `v = w + ξ/s` with `w_j = ξ_j/(pos_j − s)`. -/
def rootVec (pos xi : ι → K) (s : K) : ι → K :=
  fun j => xi j / (pos j - s) + (1 / s) * xi j

omit [Fintype ι] [DecidableEq ι] in
/-- **A component of `v` is `ξ_j·pos_j` over `s·(pos_j − s)`.** -/
theorem rootVec_apply (pos xi : ι → K) {s : K} (hs : s ≠ 0) {j : ι} (hj : pos j - s ≠ 0) :
    rootVec pos xi s j = xi j * pos j / (s * (pos j - s)) := by
  simp only [rootVec]; field_simp; ring

omit [DecidableEq ι] in
/-- **`Σ_j v_j = 1/s`**, since `w` sums to zero and `ξ` sums to one. -/
theorem sum_rootVec (pos xi : ι → K) (s : K)
    (hsum : ∑ j, xi j / (pos j - s) = 0) (hnorm : ∑ i, xi i = 1) :
    ∑ j, rootVec pos xi s j = 1 / s := by
  simp only [rootVec]
  rw [Finset.sum_add_distrib, hsum, ← Finset.mul_sum, hnorm, zero_add, mul_one]

/-- **Every root of `P` is an eigenvalue of `D'`.**  `hsum` is `P(s) = 0` divided by
`∏_j (pos_j − s)`. -/
theorem DprimeGen_mulVec_rootVec (pos xi : ι → K) {s : K}
    (hs : s ≠ 0) (hps : ∀ j, pos j - s ≠ 0)
    (hsum : ∑ j, xi j / (pos j - s) = 0) (hnorm : ∑ i, xi i = 1) :
    DprimeGen pos xi *ᵥ rootVec pos xi s = s • rootVec pos xi s := by
  funext i
  have hpi := hps i
  rw [DprimeGen_mulVec_apply, sum_rootVec pos xi s hsum hnorm, Pi.smul_apply, smul_eq_mul]
  simp only [rootVec]
  field_simp
  ring

end Gen

/-! ### Over `ℝ`, against `Dprime` -/

variable {pos xi : ι → ℝ}

/-- **`DprimeGen` is `Dprime`.** -/
theorem DprimeGen_eq_Dprime (pos xi : ι → ℝ) : DprimeGen pos xi = Dprime pos xi := by
  ext i j
  simp [DprimeGen, Dprime, ones, Matrix.vecMulVec_apply, Matrix.mulVec_diagonal]

/-! ### Step 2: when the eigenvector degenerates -/

section Vanish

variable {K : Type*} [Field K]

omit [Fintype ι] [DecidableEq ι] in
/-- **`v` vanishes exactly on the locus `ξ_j·pos_j = 0`.** -/
theorem rootVec_eq_zero_iff (pos xi : ι → K) {s : K} (hs : s ≠ 0) (hps : ∀ j, pos j - s ≠ 0) :
    rootVec pos xi s = 0 ↔ ∀ j, xi j * pos j = 0 := by
  constructor
  · intro h j
    have hj := congrFun h j
    rw [rootVec_apply pos xi hs (hps j)] at hj
    exact (div_eq_zero_iff.mp hj).resolve_right (mul_ne_zero hs (hps j))
  · intro h
    funext j
    rw [rootVec_apply pos xi hs (hps j), h j, zero_div]
    rfl

end Vanish

/-! ### Step 3: over `ℂ`, a root off the real axis is impossible -/

/-- Real and imaginary parts of a complex eigenvector of `D'` form the real pair that
`eq_zero_of_complex_eigenpair` consumes. -/
theorem Dprime_mulVec_re_im (pos xi : ι → ℝ) (v : ι → ℂ) (s : ℂ)
    (h : DprimeGen (fun i => (pos i : ℂ)) (fun i => (xi i : ℂ)) *ᵥ v = s • v) :
    Dprime pos xi *ᵥ (fun j => (v j).re)
        = s.re • (fun j => (v j).re) - s.im • (fun j => (v j).im) ∧
      Dprime pos xi *ᵥ (fun j => (v j).im)
        = s.im • (fun j => (v j).re) + s.re • (fun j => (v j).im) := by
  have hc : ∀ i, ((pos i : ℝ) : ℂ) * v i - ((pos i * xi i : ℝ) : ℂ) * ∑ k, v k = s * v i := by
    intro i
    have h2 := congrFun h i
    rw [DprimeGen_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h2
    push_cast
    linear_combination h2
  have hre : ∀ i, (Dprime pos xi *ᵥ (fun j => (v j).re)) i
      = pos i * (v i).re - pos i * xi i * ∑ k, (v k).re := by
    intro i
    rw [← DprimeGen_eq_Dprime, DprimeGen_mulVec_apply]
  have him : ∀ i, (Dprime pos xi *ᵥ (fun j => (v j).im)) i
      = pos i * (v i).im - pos i * xi i * ∑ k, (v k).im := by
    intro i
    rw [← DprimeGen_eq_Dprime, DprimeGen_mulVec_apply]
  constructor
  · funext i
    have := congrArg Complex.re (hc i)
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_sum, Complex.im_sum] at this
    rw [hre i]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [this]
  · funext i
    have := congrArg Complex.im (hc i)
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_sum, Complex.im_sum] at this
    rw [him i]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [this]

variable {a b : ι → ℝ} {neg : ι → ι}

-- `hsum` is `P(s) = 0` divided by `∏_j (pos_j − s)`; the matrix is positive semidefinite,
-- of divided-difference form, with kernel the line through the even normalised `ξ`.
/-- **Theorem `finmain`(i), in polynomial form.**  Every root of
`P(s) = Σ_k ξ_k ∏_{j ≠ k} (pos_j − s)` is real, provided `ξ_j·pos_j ≠ 0` for some `j`. -/
theorem root_im_eq_zero
    (hposinj : Function.Injective pos) (hinv : Function.Involutive neg)
    (hb : ∀ i, b (neg i) = -b i) (hxieven : ∀ i, xi (neg i) = xi i)
    (hQpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (ddMatrix a b pos *ᵥ v))
    (hQxi : ddMatrix a b pos *ᵥ xi = 0)
    (hnorm : ∑ i, xi i = 1)
    (hkerline : ∀ v : ι → ℝ, ddMatrix a b pos *ᵥ v = 0 → ∃ c : ℝ, v = c • xi)
    (hne : ∃ j, xi j * pos j ≠ 0)
    {s : ℂ} (hsum : ∑ j, (xi j : ℂ) / ((pos j : ℂ) - s) = 0) :
    s.im = 0 := by
  by_contra hbe
  have hs : s ≠ 0 := fun h => hbe (by rw [h]; exact Complex.zero_im)
  have hps : ∀ j, ((pos j : ℝ) : ℂ) - s ≠ 0 := by
    intro j hc
    have h3 : ((pos j : ℝ) : ℂ) = s := by linear_combination hc
    exact hbe (by rw [← h3]; exact Complex.ofReal_im (pos j))
  have hnormC : ∑ i, ((xi i : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hnorm, Complex.ofReal_one]
  have heig := DprimeGen_mulVec_rootVec (fun i => ((pos i : ℝ) : ℂ))
    (fun i => ((xi i : ℝ) : ℂ)) hs hps hsum hnormC
  obtain ⟨h1, h2⟩ := Dprime_mulVec_re_im pos xi _ s heig
  obtain ⟨hx, hy⟩ :=
    Dprime_real_spectrum hposinj hinv hb hxieven hQpsd hQxi hnorm hkerline hbe h1 h2
  have hv0 : rootVec (fun i => ((pos i : ℝ) : ℂ)) (fun i => ((xi i : ℝ) : ℂ)) s = 0 := by
    funext j
    refine Complex.ext ?_ ?_
    · simpa using congrFun hx j
    · simpa using congrFun hy j
  obtain ⟨j, hj⟩ := hne
  have := (rootVec_eq_zero_iff (fun i => ((pos i : ℝ) : ℂ))
    (fun i => ((xi i : ℝ) : ℂ)) hs hps).mp hv0 j
  rw [← Complex.ofReal_mul, Complex.ofReal_eq_zero] at this
  exact hj this

end Cvs.Finite.SecularRootsReal
