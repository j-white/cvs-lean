import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Upstream.SymmetricMatrixBottom

/-!
# The antiderivative of an odd eigenvector is the resolvent of the constant mode
For an odd eigenvector `o` of the CvS matrix with eigenvalue `μ`, the division vector `x_i = o_i/ω_i` (`i ≠ 0`),
`x₀ = −∑ o_i/ω_i` — the coefficients of the antiderivative of `o`'s sine polynomial — satisfies `ωx = o`,
`∑ x = 0` and `bᵀx = 0`, so the displacement identity gives `(M − μ)x = r·e₀` (`mulVec_div_off`) and
`xᵀ(M − μ)x = x₀·r` (`quad_div`). Hence `x₀·r < 0` puts the discrete bottom strictly below `μ`
(`lamD_lt_of_div`): the ordering half of step (a), at any mode count, is the sign of one number.
-/

noncomputable section

open Real Matrix

namespace Cvs.Finite.OddEigenvectorResolvent

open Cvs.Finite.SymmetricModeSet

/-- The frequencies of `Idx N` at scale `L`. -/
abbrev om (L : ℝ) (N : ℕ) : Idx N → ℝ := Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N)

/-- The division vector of `o`. -/
def xdiv (L : ℝ) (N : ℕ) (o : Idx N → ℝ) : Idx N → ℝ
  | none => -∑ j : Fin N × Bool, o (some j) / om L N (some j)
  | some j => o (some j) / om L N (some j)

theorem om_none (L : ℝ) (N : ℕ) : om L N none = 0 := by
  simp [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega, mode]

theorem om_some_ne {L : ℝ} (hL : 0 < L) (N : ℕ) (j : Fin N × Bool) : om L N (some j) ≠ 0 := by
  have h0 := om_none L N
  intro h
  have hinj := Cvs.Finite.DisplacementIdentity.omega_injective hL (mode_injective N)
  exact Option.some_ne_none j (hinj (h.trans h0.symm))

theorem sum_xdiv (L : ℝ) (N : ℕ) (o : Idx N → ℝ) : ∑ i, xdiv L N o i = 0 := by
  rw [Fintype.sum_option]; simp [xdiv]

theorem om_mul_xdiv {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i)
    (i : Idx N) : om L N i * xdiv L N o i = o i := by
  rcases i with _ | j
  · have h := hodd none
    simp only [negI] at h
    rw [om_none, zero_mul]; linarith
  · simp only [xdiv]; field_simp [om_some_ne hL N j]

theorem xdiv_even {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (i : Idx N) :
    xdiv L N o (negI N i) = xdiv L N o i := by
  rcases i with _ | ⟨k, bb⟩
  · rfl
  · have ho := hodd (some (k, bb))
    have hw := Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg (L := L) (mode_negI N) (some (k, bb))
    have hne := om_some_ne hL N (k, bb)
    simp only [xdiv, negI, om] at ho hw hne ⊢
    rw [ho, hw]
    field_simp

theorem bval_dot_xdiv {L : ℝ} (hL : 0 < L) (P R N : ℕ) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) :
    ∑ j, Cvs.Finite.PairFormDividedDifference.bval P R L (mode N j) * xdiv L N o j = 0 := by
  refine Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd (negI_involutive N) (fun i => ?_)
  rw [xdiv_even hL N hodd, mode_negI, Cvs.Finite.PairFormDividedDifference.bval_neg, neg_mul]

/-- **Away from the constant mode, `x` is an eigenvector**: `(Mx)_i = μ x_i` for `i ≠ 0`. -/
theorem mulVec_div_off {L : ℝ} (hL : 0 < L) (P R N : ℕ) {o : Idx N → ℝ} {μ : ℝ}
    (hodd : ∀ i, o (negI N i) = -o i)
    (hMo : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o = μ • o) (j : Fin N × Bool) :
    (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) (some j) = μ * xdiv L N o (some j) := by
  have hinj := Cvs.Finite.DisplacementIdentity.omega_injective hL (mode_injective N)
  have hd := Cvs.Finite.DisplacementIdentity.displacement (a := fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N k))
    (b := fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k)) hinj (xdiv L N o) (some j)
  have hωx : (fun k => Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) k * xdiv L N o k) = o :=
    funext fun k => om_mul_xdiv hL N hodd k
  change om L N (some j) * (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) (some j)
    - (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ (fun k => om L N k * xdiv L N o k)) (some j)
    = _ at hd
  rw [hωx, hMo, sum_xdiv, mul_zero, bval_dot_xdiv hL P R N hodd, sub_zero, Pi.smul_apply, smul_eq_mul,
    ← om_mul_xdiv hL N hodd (some j)] at hd
  have hne := om_some_ne hL N j
  have : om L N (some j) * ((Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) (some j)
      - μ * xdiv L N o (some j)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · linarith

/-- **The excess of the division vector is `x₀ · r`.** -/
theorem quad_div {L : ℝ} (hL : 0 < L) (P R N : ℕ) {o : Idx N → ℝ} {μ : ℝ}
    (hodd : ∀ i, o (negI N i) = -o i)
    (hMo : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o = μ • o) :
    xdiv L N o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) - μ * (xdiv L N o ⬝ᵥ xdiv L N o)
      = xdiv L N o none * ((Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) none - μ * xdiv L N o none) := by
  have hz : ∀ j : Fin N × Bool, xdiv L N o (some j) * (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) (some j)
      = μ * (xdiv L N o (some j) * xdiv L N o (some j)) := by
    intro j; rw [mulVec_div_off hL P R N hodd hMo j]; ring
  have hsum : ∑ j : Fin N × Bool, xdiv L N o (some j) * (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) (some j)
      = μ * ∑ j : Fin N × Bool, xdiv L N o (some j) * xdiv L N o (some j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => hz j
  simp only [dotProduct, Fintype.sum_option]
  rw [hsum]
  ring

/-- **The ordering half of step (a) from one sign**: if `x₀ · r < 0` for an odd eigenvector at `μ`, the
discrete bottom lies strictly below `μ`. -/
theorem lamD_lt_of_div {L : ℝ} (hL : 0 < L) (P R N : ℕ) {o : Idx N → ℝ} {μ : ℝ}
    (hodd : ∀ i, o (negI N i) = -o i)
    (hMo : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o = μ • o)
    (hsign : xdiv L N o none * ((Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xdiv L N o) none
      - μ * xdiv L N o none) < 0) :
    lamD P R L hL N < μ := by
  obtain ⟨-, hge, -⟩ := xiD_spec P R L hL N
  have hq := quad_div hL P R N hodd hMo
  rw [← hq] at hsign
  have hpos : 0 < xdiv L N o ⬝ᵥ xdiv L N o := by
    rcases lt_or_eq_of_le (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' (xdiv L N o)) with h | h
    · exact h
    · have h0 : xdiv L N o = 0 := dotProduct_self_eq_zero.mp h.symm
      rw [h0] at hsign; simp at hsign
  have h1 := hge (xdiv L N o)
  nlinarith

end Cvs.Finite.OddEigenvectorResolvent
