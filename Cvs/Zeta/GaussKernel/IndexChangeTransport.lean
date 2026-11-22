import Mathlib
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ZeroSetsAgree

/-!
# The index change, and the passage reduces to multiplicity alone
-/

namespace Cvs.Criterion

open scoped Real
open Cvs.Zeta.GaussKernel.AdmissibleKernel

/-- Every `ξ`-zero lies in the criterion's index set. -/
theorem mem_of_riemannXi_eq_zero {ρ : ℂ} (h : Cvs.Zeta.riemannXi ρ = 0) :
    ρ ∈ nonTrivialZeroSet :=
  (Cvs.Zeta.ZeroIndex.riemannXi_eq_zero_iff_mem_nonTrivialZeroSet ρ).mp h

open Classical in
/-- **The finite sum transports.**  A `Finset` of `ξ`-zeros becomes a `Finset` of the
criterion's index type with the same sum. -/
theorem sum_transport {S : Finset ℂ} (hS : ∀ ρ ∈ S, Cvs.Zeta.riemannXi ρ = 0)
    (f : ℂ → ℝ) :
    ∑ ρ ∈ S.subtype (· ∈ nonTrivialZeroSet), f (ρ : ℂ) = ∑ ρ ∈ S, f ρ :=
  Finset.sum_subtype_of_mem f (fun ρ hρ => mem_of_riemannXi_eq_zero (hS ρ hρ))

open Classical in
/-- **And the covering condition transports.**  If `S` holds every `ξ`-zero below height
`T'`, the transported window holds every index below `T'`. -/
theorem absorbing_transport {S : Finset ℂ} {T' : ℝ}
    (hcov : ∀ u : ℂ, Cvs.Zeta.riemannXi u = 0 → |u.im| < T' → u ∈ S)
    (ρ : nonTrivialZeroSet) (hρ : |((ρ : ℂ)).im| < T') :
    ρ ∈ S.subtype (· ∈ nonTrivialZeroSet) := by
  refine Finset.mem_subtype.mpr ?_
  exact hcov (ρ : ℂ) (Cvs.Zeta.ZeroIndex.riemannXi_apply_eq_zero ρ) hρ

/-- The height function the diagonal uses, on the criterion's index type. -/
noncomputable def height (ρ : nonTrivialZeroSet) : ℝ := |((ρ : ℂ)).im|

end Cvs.Criterion
