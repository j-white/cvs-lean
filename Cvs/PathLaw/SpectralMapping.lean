/-
Polynomial spectral mapping, annihilation form.

Two generic reductions used by the exact spectral-set theorem:

* `eval_eq_zero_of_mem_spectrum_of_aeval_eq_zero`: if a polynomial `q`
  annihilates an algebra element `a`, then every spectral value of `a` is a
  root of `q`. (Consequently an annihilating product of linear factors traps
  the spectrum in a finite set — no direct-integral theory needed.)
* `mem_spectrum_of_eigenvector`: an eigenvalue of a continuous linear
  endomorphism lies in its spectrum.
-/
import Cvs.PathLaw.OpNorm
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

open Polynomial

namespace Cvs.PathLaw

section Algebraic

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- If `q` annihilates `a`, every spectral value of `a` is a root of `q`:
by `spectrum.subset_polynomial_aeval`, `q.eval μ` lies in the spectrum of
`aeval a q = 0`, which is `{0}`. -/
theorem eval_eq_zero_of_mem_spectrum_of_aeval_eq_zero
    {a : A} {q : 𝕜[X]} (hq : aeval a q = 0) {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 a) :
    q.eval μ = 0 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact absurd hμ (by simp)
  · have h := spectrum.subset_polynomial_aeval a q ⟨μ, hμ, rfl⟩
    rw [hq, spectrum.zero_eq] at h
    exact h

/-- Annihilation traps the spectrum in the root set. -/
theorem spectrum_subset_roots_of_aeval_eq_zero
    {a : A} {q : 𝕜[X]} (hq : aeval a q = 0) :
    spectrum 𝕜 a ⊆ {μ : 𝕜 | q.eval μ = 0} := fun _ hμ =>
  eval_eq_zero_of_mem_spectrum_of_aeval_eq_zero hq hμ

end Algebraic

section Eigen

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- An eigenvalue of a continuous linear endomorphism lies in its spectrum:
a unit annihilating a nonzero vector is absurd. -/
theorem mem_spectrum_of_eigenvector {T : E →L[𝕜] E} {μ : 𝕜} {x : E}
    (hx : x ≠ 0) (hTx : T x = μ • x) : μ ∈ spectrum 𝕜 T := by
  rw [spectrum.mem_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hker : (algebraMap 𝕜 (E →L[𝕜] E) μ - T) x = 0 := by
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, hTx, sub_self]
  apply hx
  calc x = ((↑u⁻¹ * ↑u : E →L[𝕜] E)) x := by rw [Units.inv_mul]; rfl
    _ = (↑u⁻¹ : E →L[𝕜] E) ((↑u : E →L[𝕜] E) x) := by
        rw [mul_apply_eq_comp]
    _ = (↑u⁻¹ : E →L[𝕜] E) 0 := by rw [hu, hker]
    _ = 0 := map_zero _

end Eigen

end Cvs.PathLaw
