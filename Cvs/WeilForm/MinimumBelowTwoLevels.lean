import Mathlib
import Cvs.Upstream.TightCoordinateConvergence

/-!
# The minimum sits below any two diagonal levels

    λ_min ≤ max (D m₀) (D m₁)   for any two distinct modes

The rank one is blind to one direction in every plane of modes: a two-dimensional space
carries a vector orthogonal to `v`, and there the perturbed form is the diagonal one.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence

namespace Cvs.WeilForm.MinimumBelowTwoLevels

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- The vector in the plane of two modes that the rank one cannot see. -/
def pairVec (v : ι → ℝ) (m₀ m₁ : ι) (n : ι) : ℝ :=
  if n = m₀ then v m₁ / Real.sqrt ((v m₀) ^ 2 + (v m₁) ^ 2)
  else if n = m₁ then -(v m₀) / Real.sqrt ((v m₀) ^ 2 + (v m₁) ^ 2) else 0

section
variable {v : ι → ℝ} {m₀ m₁ : ι}

omit [Countable ι] [Nonempty ι] in
theorem pairVec_fst : pairVec v m₀ m₁ m₀ = v m₁ / Real.sqrt ((v m₀) ^ 2 + (v m₁) ^ 2) := by
  simp [pairVec]

omit [Countable ι] [Nonempty ι] in
theorem pairVec_snd (hne : m₀ ≠ m₁) :
    pairVec v m₀ m₁ m₁ = -(v m₀) / Real.sqrt ((v m₀) ^ 2 + (v m₁) ^ 2) := by
  simp [pairVec, hne.symm]

omit [Countable ι] [Nonempty ι] in
theorem pairVec_apply_notMem {n : ι} (h0 : n ≠ m₀) (h1 : n ≠ m₁) :
    pairVec v m₀ m₁ n = 0 := by simp [pairVec, h0, h1]

/-- **It is a unit vector**, when `v` does not vanish at both modes. -/
theorem tsum_sq_pairVec (hne : m₀ ≠ m₁) (hv : (v m₀) ^ 2 + (v m₁) ^ 2 ≠ 0) :
    ∑' n : ι, (pairVec v m₀ m₁ n) ^ 2 = 1 := by
  classical
  have hpos : 0 < (v m₀) ^ 2 + (v m₁) ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hv)
  rw [tsum_eq_sum (s := ({m₀, m₁} : Finset ι)) (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [pairVec_apply_notMem hn.1 hn.2])]
  rw [Finset.sum_pair hne, pairVec_fst, pairVec_snd hne, div_pow, div_pow,
    Real.sq_sqrt hpos.le]
  field_simp
  ring

/-- **The rank one does not see it.** -/
theorem tsum_mul_pairVec (hne : m₀ ≠ m₁) :
    ∑' n : ι, v n * pairVec v m₀ m₁ n = 0 := by
  classical
  rw [tsum_eq_sum (s := ({m₀, m₁} : Finset ι)) (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [pairVec_apply_notMem hn.1 hn.2])]
  rw [Finset.sum_pair hne, pairVec_fst, pairVec_snd hne]
  field_simp
  ring

/-- The pair vector lies in the form's domain. -/
theorem pairVec_mem (σ : ι → ℝ) (hne : m₀ ≠ m₁) (hv : (v m₀) ^ 2 + (v m₁) ^ 2 ≠ 0) :
    pairVec v m₀ m₁ ∈ sphereDom σ := by
  classical
  refine ⟨?_, tsum_sq_pairVec hne hv, ?_⟩
  · exact summable_of_ne_finset_zero (s := ({m₀, m₁} : Finset ι)) fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [pairVec_apply_notMem hn.1 hn.2]
  · exact summable_of_ne_finset_zero (s := ({m₀, m₁} : Finset ι)) fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [pairVec_apply_notMem hn.1 hn.2]

end

end Cvs.WeilForm.MinimumBelowTwoLevels
