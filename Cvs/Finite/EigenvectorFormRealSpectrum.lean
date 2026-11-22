import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.SelfAdjointRealSpectrum

/-!
# `finmain`(i), in eigenvector form

For the CvS matrix — positive semidefinite, of divided-difference form, kernel exactly the
line through `ξ` — the perturbed `D' = D − |Dξ⟩⟨η|` has no eigenvalue off the real axis.
This is the eigenvalue statement the theorem's polynomial encodes; the determinant identity
is the bridge between the two.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix Cvs.Finite.DividedDifferenceCommutator Cvs.Finite.SelfAdjointRealSpectrum

namespace Cvs.Finite.EigenvectorFormRealSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a b pos : ι → ℝ} {neg : ι → ι} {xi : ι → ℝ}

/-- **`ker Q ⊆ ker D'`**, from `ker Q = ℝ·ξ` and `D' ξ = 0`. -/
theorem Dprime_ker (hnorm : ∑ i, xi i = 1)
    (hkerline : ∀ v : ι → ℝ, ddMatrix a b pos *ᵥ v = 0 → ∃ c : ℝ, v = c • xi)
    (v : ι → ℝ) (hv : ddMatrix a b pos *ᵥ v = 0) : Dprime pos xi *ᵥ v = 0 := by
  obtain ⟨c, hc⟩ := hkerline v hv
  rw [hc, Matrix.mulVec_smul, Dprime_mulVec_xi hnorm, smul_zero]

-- The hypotheses are CvS's: `Q` of the divided-difference form, positive semidefinite, with
-- one-dimensional kernel spanned by an even `ξ` normalised by `⟨η, ξ⟩ = 1`.
/-- **Theorem `finmain`(i).**  `D'` admits no eigenvalue with nonzero imaginary part: any
real pair `(x, y)` realising `α + iβ` with `β ≠ 0` is zero. -/
theorem Dprime_real_spectrum
    (hposinj : Function.Injective pos) (hinv : Function.Involutive neg)
    (hb : ∀ i, b (neg i) = -b i) (hxieven : ∀ i, xi (neg i) = xi i)
    (hQpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (ddMatrix a b pos *ᵥ v))
    (hQxi : ddMatrix a b pos *ᵥ xi = 0)
    (hnorm : ∑ i, xi i = 1)
    (hkerline : ∀ v : ι → ℝ, ddMatrix a b pos *ᵥ v = 0 → ∃ c : ℝ, v = c • xi)
    {al be : ℝ} (hbe : be ≠ 0) {x y : ι → ℝ}
    (hx : Dprime pos xi *ᵥ x = al • x - be • y)
    (hy : Dprime pos xi *ᵥ y = be • x + al • y) :
    x = 0 ∧ y = 0 :=
  eq_zero_of_complex_eigenpair ddMatrix_isSymm hQpsd
    (Q_mul_Dprime hposinj hinv hb hxieven hQxi hnorm)
    (Dprime_ker hnorm hkerline) hbe hx hy

end Cvs.Finite.EigenvectorFormRealSpectrum
