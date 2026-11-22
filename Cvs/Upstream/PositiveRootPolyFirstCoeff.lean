import Mathlib

/-!
# A polynomial with positive real roots, normalised at `0`, is controlled by its first coefficient
`eval_div_eval_zero`: if every root of `p : ℂ[X]` is real and positive and `p(0) ≠ 0`, then
`p(w)/p(0) = ∑_j (−1)^j e_j(1/r) w^j` (`ecoeff`), and `norm_ecoeff_le` bounds the `j`-th coefficient by
`e_1^j / j!` with `e_1 = ∑ 1/r = −ecoeff 1` — the input `an earlier result` needs.
-/

noncomputable section

open Polynomial Finset Filter Topology

namespace Cvs.Upstream.PositiveRootPolyFirstCoeff

theorem eval_eq_eval_zero_mul_prod {p : ℂ[X]} (hroots : ∀ r ∈ p.roots, r ≠ 0) (w : ℂ) :
    p.eval w = p.eval 0 * (p.roots.map fun r => 1 - r⁻¹ * w).prod := by
  have hs := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots, hs.eval_eq_prod_roots, mul_assoc]
  congr 1
  rw [← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun r hr => ?_)
  have := hroots r hr
  field_simp
  ring

end Cvs.Upstream.PositiveRootPolyFirstCoeff
