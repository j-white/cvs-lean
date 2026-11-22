import Mathlib
import Cvs.Finite.EvenBottomRealRoots
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Upstream.SymmetricMatrixBottom

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The odd-sector bottom of the window matrix

A symmetric matrix attains its least Rayleigh quotient on every nonzero invariant subspace, at an
eigenvector. The odd vectors of an involution the matrix commutes with form such a subspace, so the
CvS matrix has an odd bottom eigenpair at every scale with at least one mode pair.
-/

noncomputable section

open Matrix Real Cvs.Finite.SymmetricModeSet

namespace Cvs.StepA.OddSectorBottom

/-! ### Minimisers on an invariant subspace -/

section General

variable {ι : Type*} [Fintype ι]

/-- **A minimiser of the form on an invariant subspace is an eigenvector.** -/
theorem eigen_of_submodule_min {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i)
    {S : Submodule ℝ (ι → ℝ)} (hS : ∀ v ∈ S, A *ᵥ v ∈ S) {lam : ℝ} {xi : ι → ℝ} (hxi : xi ∈ S)
    (hmin : ∀ v ∈ S, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hlev : xi ⬝ᵥ (A *ᵥ xi) = lam * (xi ⬝ᵥ xi)) : A *ᵥ xi = lam • xi := by
  set r : ι → ℝ := A *ᵥ xi - lam • xi with hr
  have hrS : r ∈ S := S.sub_mem (hS xi hxi) (S.smul_mem lam hxi)
  have hcomm := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm hsymm
  have hexp : ∀ t : ℝ, (xi - t • r) ⬝ᵥ (A *ᵥ (xi - t • r)) - lam * ((xi - t • r) ⬝ᵥ (xi - t • r))
      = (xi ⬝ᵥ (A *ᵥ xi) - lam * (xi ⬝ᵥ xi)) - 2 * t * (r ⬝ᵥ r)
        + t ^ 2 * (r ⬝ᵥ (A *ᵥ r) - lam * (r ⬝ᵥ r)) := by
    intro t
    have h1 : xi ⬝ᵥ (A *ᵥ r) = r ⬝ᵥ (A *ᵥ xi) := hcomm xi r
    have h2 : r ⬝ᵥ r = r ⬝ᵥ (A *ᵥ xi) - lam * (r ⬝ᵥ xi) := by
      rw [hr]; simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have h3 : xi ⬝ᵥ r = r ⬝ᵥ xi := dotProduct_comm _ _
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [h1, h3]
    linear_combination (2 * t) * h2
  have hrr : 0 ≤ r ⬝ᵥ r := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' r
  have hC : 0 ≤ r ⬝ᵥ (A *ᵥ r) - lam * (r ⬝ᵥ r) := by linarith [hmin r hrS]
  by_contra hne
  have hr0 : r ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hpos : 0 < r ⬝ᵥ r := lt_of_le_of_ne hrr (fun h => hr0 (dotProduct_self_eq_zero.mp h.symm))
  set C := r ⬝ᵥ (A *ᵥ r) - lam * (r ⬝ᵥ r) with hCdef
  set s : ℝ := (r ⬝ᵥ r) / (C + 1) with hs
  have hC1 : 0 < C + 1 := by linarith
  have hs0 : 0 < s := div_pos hpos hC1
  have hsC : s * C ≤ r ⬝ᵥ r := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ hC1]; nlinarith
  have hmem : xi - s • r ∈ S := S.sub_mem hxi (S.smul_mem s hrS)
  have h := hmin _ hmem
  have he := hexp s
  rw [hlev, sub_self, zero_sub] at he
  nlinarith

/-- A lower bound on the unit vectors of a subspace bounds the form on the whole subspace. -/
theorem submodule_quad_ge {A : Matrix ι ι ℝ} {S : Submodule ℝ (ι → ℝ)} {lam : ℝ}
    (hmin : ∀ v ∈ S, v ⬝ᵥ v = 1 → lam ≤ v ⬝ᵥ (A *ᵥ v)) (v : ι → ℝ) (hv : v ∈ S) :
    lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  by_cases hv0 : v = 0
  · subst hv0; simp
  · have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v)
      (fun h => hv0 (dotProduct_self_eq_zero.mp h.symm))
    set c : ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ with hc
    have hcc : c * c = (v ⬝ᵥ v)⁻¹ := by rw [hc, ← mul_inv, Real.mul_self_sqrt hpos.le]
    have h1 : (c • v) ⬝ᵥ (c • v) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc,
        inv_mul_cancel₀ hpos.ne']
    have h : lam ≤ (c • v) ⬝ᵥ (A *ᵥ (c • v)) := hmin _ (S.smul_mem c hv) h1
    rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      hcc] at h
    calc lam * (v ⬝ᵥ v) ≤ (v ⬝ᵥ v)⁻¹ * (v ⬝ᵥ (A *ᵥ v)) * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = v ⬝ᵥ (A *ᵥ v) := by field_simp

/-- **A symmetric matrix has a bottom eigenpair on every nonzero invariant subspace.** -/
theorem exists_submodule_min {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i)
    {S : Submodule ℝ (ι → ℝ)} (hS : ∀ v ∈ S, A *ᵥ v ∈ S) {v0 : ι → ℝ} (hv0 : v0 ∈ S)
    (hv0ne : v0 ≠ 0) :
    ∃ (lam : ℝ) (xi : ι → ℝ), xi ∈ S ∧ xi ⬝ᵥ xi = 1
      ∧ (∀ v ∈ S, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) ∧ A *ᵥ xi = lam • xi := by
  have hK : IsCompact (Cvs.Upstream.SymmetricMatrixBottom.sphere ι ∩ (S : Set (ι → ℝ))) :=
    Cvs.Upstream.SymmetricMatrixBottom.isCompact_sphere.inter_right (Submodule.closed_of_finiteDimensional S)
  have hpos : 0 < v0 ⬝ᵥ v0 := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v0)
    (fun h => hv0ne (dotProduct_self_eq_zero.mp h.symm))
  set c : ℝ := (Real.sqrt (v0 ⬝ᵥ v0))⁻¹ with hc
  have hcc : c * c = (v0 ⬝ᵥ v0)⁻¹ := by rw [hc, ← mul_inv, Real.mul_self_sqrt hpos.le]
  have hne : (Cvs.Upstream.SymmetricMatrixBottom.sphere ι ∩ (S : Set (ι → ℝ))).Nonempty := by
    refine ⟨c • v0, ?_, S.smul_mem c hv0⟩
    show (c • v0) ⬝ᵥ (c • v0) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc,
      inv_mul_cancel₀ hpos.ne']
  obtain ⟨xi, ⟨hxis, hxiS⟩, hmin⟩ := hK.exists_isMinOn hne
    (by fun_prop : Continuous fun v : ι → ℝ => v ⬝ᵥ (A *ᵥ v)).continuousOn
  have hxi1 : xi ⬝ᵥ xi = 1 := hxis
  have hge := submodule_quad_ge (A := A) (S := S) (lam := xi ⬝ᵥ (A *ᵥ xi))
    (fun v hv hv1 => hmin (show v ∈ Cvs.Upstream.SymmetricMatrixBottom.sphere ι ∩ (S : Set (ι → ℝ)) from
      ⟨hv1, hv⟩))
  exact ⟨_, xi, hxiS, hxi1, hge, eigen_of_submodule_min hsymm hS hxiS hge (by rw [hxi1, mul_one])⟩

/-! ### The odd subspace of an involution -/

/-- The odd vectors under an involution. -/
def oddSub (neg : ι → ι) : Submodule ℝ (ι → ℝ) where
  carrier := {v | ∀ i, v (neg i) = -v i}
  add_mem' := by
    intro a b ha hb i
    have ha' : ∀ i, a (neg i) = -a i := ha
    have hb' : ∀ i, b (neg i) = -b i := hb
    simp only [Pi.add_apply, ha' i, hb' i]; ring
  zero_mem' := by intro i; simp
  smul_mem' := by
    intro c v hv i
    have hv' : ∀ i, v (neg i) = -v i := hv
    simp only [Pi.smul_apply, smul_eq_mul, hv' i]; ring

omit [Fintype ι] in
theorem mem_oddSub {neg : ι → ι} {v : ι → ℝ} : v ∈ oddSub neg ↔ ∀ i, v (neg i) = -v i := Iff.rfl

/-- A matrix commuting with the involution sends odd vectors to odd vectors. -/
theorem mulVec_odd {A : Matrix ι ι ℝ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) {v : ι → ℝ} (hv : ∀ i, v (neg i) = -v i) (i : ι) :
    (A *ᵥ v) (neg i) = -(A *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  rw [← Cvs.Finite.EvenBottomRealRoots.sum_neg_even hinv (fun j => A (neg i) j * v j), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [hA, hv]; ring

/-- **An odd bottom eigenpair exists** for a symmetric matrix commuting with an involution that
moves some index. -/
theorem exists_odd_bottom_of {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j) {a : ι}
    (ha : neg a ≠ a) :
    ∃ (lam : ℝ) (xi : ι → ℝ), (∀ i, xi (neg i) = -xi i) ∧ xi ⬝ᵥ xi = 1
      ∧ (∀ v : ι → ℝ, (∀ i, v (neg i) = -v i) → lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
      ∧ A *ᵥ xi = lam • xi := by
  classical
  set o : ι → ℝ := fun i => (if i = a then 1 else 0) - (if i = neg a then 1 else 0) with ho
  have hodd : o ∈ oddSub neg := by
    intro i
    have e1 : (neg i = a) ↔ (i = neg a) := ⟨fun h => by rw [← h, hinv i], fun h => by rw [h, hinv a]⟩
    have e2 : (neg i = neg a) ↔ (i = a) := hinv.injective.eq_iff
    simp only [ho, e1, e2]
    ring
  have hne : o ≠ 0 := by
    intro h
    have := congrFun h a
    simp [ho, ha.symm] at this
  obtain ⟨lam, xi, hxiS, hxi1, hmin, heig⟩ := exists_submodule_min (S := oddSub neg) hsymm
    (fun v hv i => mulVec_odd hinv hA hv i) hodd hne
  exact ⟨lam, xi, hxiS, hxi1, fun v hv => hmin v hv, heig⟩

end General

/-! ### The window matrix -/

/-- **An odd-sector bottom of the CvS matrix exists** at every scale with at least one mode pair. -/
theorem exists_odd_bottom {L : ℝ} (hL : 0 < L) (P R N : ℕ) (hN : 0 < N) :
    ∃ (lam : ℝ) (xi : Idx N → ℝ), (∀ i, xi (negI N i) = -xi i) ∧ xi ⬝ᵥ xi = 1
      ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) →
          lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = lam • xi :=
  exists_odd_bottom_of (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (mode_injective N)) (negI_involutive N)
    (Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R (mode_injective N) (mode_negI N))
    (a := some (⟨0, hN⟩, true)) (by simp [negI])

end Cvs.StepA.OddSectorBottom
