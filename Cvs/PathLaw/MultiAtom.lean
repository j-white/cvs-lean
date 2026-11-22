/-
The multi-atom capacity budget.

The Single-Atom Path Law gives each arithmetic block its exact norm; the
triangle inequality then caps the whole prime block by the sum of the
Path Law budgets:

  ‖∑_q ΔO_q‖ ≤ ∑_q pathLawNorm(q, c) = ∑_q 2cos(π/(m_q+1)) Λ(q)/√q.

This is only an upper bound. The joint norm of several atoms is in general
strictly smaller; for two atoms in a short window see `Cvs.PathLaw.TwoAtom`.
-/
import Cvs.PathLaw.Model
import Cvs.PathLaw.RealAtom

namespace Cvs.PathLaw

/-- **The multi-atom capacity budget** (hypothesis-style). Any finite
family of operators whose matrices are the Loewner atoms has its sum
capped in norm by the sum of the Path Law budgets. -/
theorem multi_atom_budget (c : ℕ) (s : Finset ℕ)
    (T : ℕ → AtomSpaceC →L[ℂ] AtomSpaceC)
    (hq : ∀ q ∈ s, 2 ≤ q) (hc : ∀ q ∈ s, q < c)
    (hT : ∀ q ∈ s, ∀ k l : ℤ,
      inner ℂ (lp.single 2 l (1 : ℂ)) (T q (lp.single 2 k (1 : ℂ)))
        = ((atomEntry q c l k : ℝ) : ℂ)) :
    ‖∑ q ∈ s, T q‖ ≤ ∑ q ∈ s, pathLawNorm q c :=
  calc ‖∑ q ∈ s, T q‖ ≤ ∑ q ∈ s, ‖T q‖ := norm_sum_le _ _
    _ = ∑ q ∈ s, pathLawNorm q c := Finset.sum_congr rfl fun q hq' =>
        single_atom_path_lawC q c (hq q hq') (hc q hq') (T q) (hT q hq')

/-- The capacity budget for the canonical complex atoms. -/
theorem multi_atom_budget_atomCLMC (c : ℕ) (s : Finset ℕ)
    (hq : ∀ q ∈ s, 2 ≤ q) (hc : ∀ q ∈ s, q < c) :
    ‖∑ q ∈ s, atomCLMC q c‖ ≤ ∑ q ∈ s, pathLawNorm q c :=
  multi_atom_budget c s _ hq hc fun q hq' =>
    inner_atomCLMC q c (hq q hq') (hc q hq')

/-! ### The prime block -/

/-- The prime-power index set of the window: prime powers `q < c`. -/
def primePowers (c : ℕ) : Finset ℕ :=
  (Finset.range c).filter IsPrimePow

/-- **The arithmetic prime block**: the sum of the canonical real atoms
over all prime powers in the window, `W_p = ∑_{q = p^k < c} ΔO_q`. -/
noncomputable def primeBlock (c : ℕ) : AtomSpace →L[ℝ] AtomSpace :=
  ∑ q ∈ primePowers c, atomCLMR q c

/-- The prime block obeys the capacity budget: its norm is capped by the
sum of the exact Path Law norms of its atoms. -/
theorem norm_primeBlock_le (c : ℕ) :
    ‖primeBlock c‖ ≤ ∑ q ∈ primePowers c, pathLawNorm q c := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun q hq => ?_
  have hmem := Finset.mem_filter.mp hq
  exact le_of_eq (opNorm_atomCLMR q c hmem.2.two_le
    (Finset.mem_range.mp hmem.1))

end Cvs.PathLaw
