import Mathlib
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-!
# Vanishing moments damp the universal amplitude by `u^{-2J}`, exactly
The moments `μ_j = ∑_k xi_k (2πk)^{2j}` are the coefficients of the universal rational factor at
infinity, `R(u) = −∑_j μ_j u^{−2j−2}`. If the first `J` vanish then, as a finite identity,
`R_xi(u) = u^{−2J}·R_{xi·(2πk)^{2J}}(u)`, so `F_xi(u) = u^{−4J}·F_{shift}(u)` and the CvS form is
`L·∑_ρ m_ρ Re[(Lz_ρ)^{−4J} F_{shift}(Lz_ρ)]`: endpoint flatness of the window function is the same
as a scale-explicit damping of every zero's contribution by `(L·z_ρ)^{−4J}`.
-/

noncomputable section

open Real Filter Topology Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.VanishingMomentsDamping
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- The squared frequency `(2πk)²` as a complex number. -/
def q (mode : ι → ℤ) (k : ι) : ℂ := ((2 * π * mode k : ℝ) : ℂ) ^ 2

/-- The `j`-th moment `∑_k xi_k (2πk)^{2j}`. -/
def moment (mode : ι → ℤ) (xi : ι → ℝ) (j : ℕ) : ℂ := ∑ k, (xi k : ℂ) * q mode k ^ j

/-- The moment-shifted coefficients `xi_k (2πk)^{2J}`. -/
def shift (mode : ι → ℤ) (xi : ι → ℝ) (J : ℕ) : ι → ℝ :=
  fun k => xi k * ((2 * π * mode k) ^ 2) ^ J

omit [Fintype ι] in
theorem shift_cast (mode : ι → ℤ) (xi : ι → ℝ) (J : ℕ) (k : ι) :
    ((shift mode xi J k : ℝ) : ℂ) = (xi k : ℂ) * q mode k ^ J := by
  unfold shift q; push_cast; ring

/-- **The finite moment identity**: with the first `J` moments zero,
`R_xi(u) = u^{−2J}·R_{shift J}(u)`. -/
theorem R_eq_of_moments (mode : ι → ℤ) (xi : ι → ℝ) {J : ℕ}
    (hJ : ∀ j < J, moment mode xi j = 0) {u : ℂ} (hu : u ≠ 0)
    (hq : ∀ k, q mode k - u ^ 2 ≠ 0) :
    Cvs.Finite.UniversalFunctionPairing.R mode xi u
      = (u ^ (2 * J))⁻¹ * Cvs.Finite.UniversalFunctionPairing.R mode (shift mode xi J) u := by
  have hupow : u ^ (2 * J) ≠ 0 := pow_ne_zero _ hu
  have key : ∀ k, (xi k : ℂ) / (q mode k - u ^ 2)
      - (u ^ (2 * J))⁻¹ * (((shift mode xi J k : ℝ) : ℂ) / (q mode k - u ^ 2))
      = -(u ^ (2 * J))⁻¹ * ∑ i ∈ Finset.range J,
          (xi k : ℂ) * ((u ^ 2) ^ i * q mode k ^ (J - 1 - i)) := by
    intro k
    have hd := hq k
    have hg := geom_sum₂_mul (u ^ 2) (q mode k) J
    rw [shift_cast]
    have h2J : u ^ (2 * J) = (u ^ 2) ^ J := by rw [pow_mul]
    rw [← Finset.mul_sum, h2J]
    have hpow : (u ^ 2) ^ J ≠ 0 := by rw [← h2J]; exact hupow
    rw [eq_comm, ← sub_eq_zero]
    have hg' : (u ^ 2) ^ J - q mode k ^ J
        = (∑ i ∈ Finset.range J, (u ^ 2) ^ i * q mode k ^ (J - 1 - i)) * (u ^ 2 - q mode k) := hg.symm
    field_simp
    rw [show u ^ 2 - q mode k = -(q mode k - u ^ 2) by ring] at hg'
    linear_combination (-(xi k : ℂ)) * hg'
  -- sum the pointwise identity and use the vanishing moments
  unfold Cvs.Finite.UniversalFunctionPairing.R
  rw [Finset.mul_sum]
  have hsum : ∑ k, ((xi k : ℂ) / (q mode k - u ^ 2)
      - (u ^ (2 * J))⁻¹ * (((shift mode xi J k : ℝ) : ℂ) / (q mode k - u ^ 2))) = 0 := by
    simp_rw [key]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∑ i ∈ Finset.range J, ∑ k : ι, (xi k : ℂ) * ((u ^ 2) ^ i * q mode k ^ (J - 1 - i)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hm := hJ (J - 1 - i) (by have := Finset.mem_range.mp hi; omega)
      unfold moment at hm
      rw [show ∑ k : ι, (xi k : ℂ) * ((u ^ 2) ^ i * q mode k ^ (J - 1 - i))
          = (u ^ 2) ^ i * ∑ k : ι, (xi k : ℂ) * q mode k ^ (J - 1 - i) by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring]
      rw [hm, mul_zero]
    rw [this, mul_zero]
  rw [Finset.sum_sub_distrib] at hsum
  unfold q at hsum
  linear_combination hsum

/-- The universal function vanishes at the origin. -/
theorem F_zero (mode : ι → ℤ) (xi : ι → ℝ) : Cvs.Finite.UniversalFunctionPairing.F mode xi 0 = 0 := by
  unfold Cvs.Finite.UniversalFunctionPairing.F; simp

/-- **The universal function of a vector with `J` vanishing moments is `u^{−4J}` times that of
the shifted vector.** -/
theorem F_eq_of_moments (mode : ι → ℤ) (xi : ι → ℝ) {J : ℕ}
    (hJ : ∀ j < J, moment mode xi j = 0) {u : ℂ}
    (hq : ∀ k, q mode k - u ^ 2 ≠ 0) :
    Cvs.Finite.UniversalFunctionPairing.F mode xi u
      = (u ^ (4 * J))⁻¹ * Cvs.Finite.UniversalFunctionPairing.F mode (shift mode xi J) u := by
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [F_zero, F_zero, mul_zero]
  unfold Cvs.Finite.UniversalFunctionPairing.F
  rw [R_eq_of_moments mode xi hJ hu hq]
  have : (u ^ (4 * J))⁻¹ = ((u ^ (2 * J))⁻¹) ^ 2 := by
    rw [show 4 * J = 2 * J * 2 by ring, pow_mul, inv_pow]
  rw [this]; ring

omit [Fintype ι] in
/-- The genericity hypothesis in the dilated variable. -/
theorem q_sub_ne {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) {z : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - z ^ 2 ≠ 0) (k : ι) :
    q mode k - ((L : ℂ) * z) ^ 2 ≠ 0 := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  intro h
  apply hgen k
  have : ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - z ^ 2
      = (q mode k - ((L : ℂ) * z) ^ 2) / (L : ℂ) ^ 2 := by
    unfold q; push_cast; field_simp
  rw [this, h, zero_div]

/-- **The CvS form of a vector with `J` vanishing moments**: every zero's contribution is damped
by `(L·z_ρ)^{−4J}`, with the shifted vector's universal function in place of the original. -/
theorem quadForm_eq_of_moments [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0)
    {J : ℕ} (hJ : ∀ j < J, moment mode xi j = 0) :
    xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ xi)
      = L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * ((((L : ℂ) * Cvs.ZeroCounting.zPoint rho) ^ (4 * J))⁻¹
              * Cvs.Finite.UniversalFunctionPairing.F mode (shift mode xi J)
                ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
  rw [Cvs.Finite.UniversalFunctionPairing.quadForm_eq_universal hL hinj hinv hmode hxieven hgen]
  refine congrArg (L * ·) (tsum_congr fun rho => ?_)
  rw [F_eq_of_moments mode xi hJ (q_sub_ne hL mode (hgen rho))]

end Cvs.Finite.VanishingMomentsDamping
