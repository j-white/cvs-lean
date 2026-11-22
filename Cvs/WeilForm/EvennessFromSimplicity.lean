import Mathlib

/-!
# Connes–van Suijlekom's evenness hypothesis is not independent

    reflect_eq_or_neg : R involutive, commuting with T, lam simple → R η = ±η
    even_of_cone      : and η in a sign cone → R η = η

RH.md §3.23 carries the construction and what is measured about it.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.WeilForm.EvennessFromSimplicity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Simplicity of an eigenvalue, as the statement that its eigenspace is spanned by `eta`. -/
def IsSimpleAt (T : E →L[ℝ] E) (lam : ℝ) (eta : E) : Prop :=
  T eta = lam • eta ∧ eta ≠ 0 ∧ ∀ v : E, T v = lam • v → ∃ c : ℝ, v = c • eta

/-- **A reflection-invariant operator has eigenvectors that are even or odd.**  If `R` is an
involution commuting with `T` and `lam` is simple, its eigenvector satisfies `R eta = ± eta`. -/
theorem reflect_eq_or_neg {T R : E →L[ℝ] E} {lam : ℝ} {eta : E}
    (hinv : ∀ v : E, R (R v) = v) (hcomm : ∀ v : E, T (R v) = R (T v))
    (hsimple : IsSimpleAt T lam eta) :
    R eta = eta ∨ R eta = -eta := by
  obtain ⟨heig, hne, huniq⟩ := hsimple
  have hR : T (R eta) = lam • R eta := by
    rw [hcomm, heig, map_smul]
  obtain ⟨c, hc⟩ := huniq (R eta) hR
  have hcc : (c * c) • eta = eta := by
    have h1 : R (R eta) = eta := hinv eta
    rw [hc] at h1
    rw [map_smul] at h1
    rw [hc] at h1
    rw [smul_smul] at h1
    exact h1
  have hc2 : c * c = 1 := by
    by_contra hne1
    have : (c * c - 1) • eta = 0 := by
      rw [sub_smul, hcc, one_smul, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact hne1 (by linarith [sub_eq_zero.mp h])
    · exact hne h
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · left; rw [hc, h, one_smul]
  · right; rw [hc, h, neg_one_smul]

/-- **Evenness is free, given a constant sign.**  If in addition the eigenvector lies in a
cone `P` that `R` preserves and that meets its own negative only at `0`, the odd case is
impossible and `eta` is even. -/
theorem even_of_cone {T R : E →L[ℝ] E} {lam : ℝ} {eta : E} (P : Set E)
    (hinv : ∀ v : E, R (R v) = v) (hcomm : ∀ v : E, T (R v) = R (T v))
    (hsimple : IsSimpleAt T lam eta)
    (hPR : ∀ v ∈ P, R v ∈ P) (hcone : ∀ v ∈ P, -v ∈ P → v = 0)
    (hmem : eta ∈ P) :
    R eta = eta := by
  rcases reflect_eq_or_neg hinv hcomm hsimple with h | h
  · exact h
  · exfalso
    have h1 : R eta ∈ P := hPR eta hmem
    rw [h] at h1
    have := hcone eta hmem h1
    exact hsimple.2.1 this

end Cvs.WeilForm.EvennessFromSimplicity
