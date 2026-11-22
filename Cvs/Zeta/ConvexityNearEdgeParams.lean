import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ConvexityZetaEdges

/-!
# The parameters, and the near edge
-/

open Complex

namespace Cvs.ArchScore

/-- A point on a vertical edge, in the form the edge bounds are stated in. -/
theorem edge_param {α : ℝ} {z : ℂ} (h : z.re = α) : z = (α : ℂ) + (z.im : ℂ) * I := by
  apply Complex.ext <;> simp [← h]

/-! ### The parameters for `ζ`

`α = -1/2`, `β = 3/2`, and edge exponents `a = 1`, `b = 0` determine
`b' = (b-a)/(β-α) = -1/2` and `a' = a - b'α = 3/4`.  These four facts are the whole
instantiation. -/

/-- **The near edge for the entire part.**  `ζ₀` is bounded on `Re s = 3/2`, so its exponent
there is `0`. -/
theorem zeta₀_edge_three_halves {t : ℝ} (ht : 1 ≤ |t|) {C₀ : ℝ}
    (hC₀ : ‖riemannZeta ((3 : ℂ) / 2 + (t : ℂ) * I)‖ ≤ C₀) :
    ‖riemannZeta₀ ((3 : ℂ) / 2 + (t : ℂ) * I)‖ ≤ C₀ + 1 := by
  refine Cvs.ArchScore.norm_zeta₀_le ?_ hC₀
  have him : ((3 : ℂ) / 2 + (t : ℂ) * I).im = t := by simp
  rw [him]; exact ht

end Cvs.ArchScore
