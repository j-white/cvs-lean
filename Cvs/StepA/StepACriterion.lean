import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.EvenBelowOdd
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.OddAboveUnderRH
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.OddSectorBottom
import Cvs.StepA.PosDefOffLattice
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.WeightExponentialChord
import Cvs.Zeta.ZeroSetsAgree

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step (a) criterion: its unconditional content and a converse below the first ordinate

An attained top, a tie at the top and a strictly top quadruple each refute RH, and step (a) at all
large scales gives a tie at the top or a top not attained. Under RH an odd bottom gap is `OddBottomBelow`
with step (a). For odd `o`, `Ω_h ≤ 2πN/L`, so `2πN/L < c ≤ |γ_ρ|` gives `OddBottomBelow`, and under RH
with more than `N` distinct squared off-lattice ordinates it gives step (a); `c = 6.24` qualifies.
-/

noncomputable section

open Matrix Real

namespace Cvs.StepA.StepACriterion
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx negI)
open Cvs.Finite.OddEigenvectorResolvent (xdiv)
open Cvs.StepA.OddAboveDisplacement (OddAbove)
open Cvs.Finite.ParitySectorDefect (MX)
open Cvs.StepA.EvenBelowOdd (omegaSq)
open Cvs.StepA.PosDefOffLattice (offLatticeSq)
open Cvs.StepA.OddBottomGapCriterion (OddBottomGap OddBottomBelow)

variable {L : ℝ} {N : ℕ}

/-! ### The top of the zero set refutes RH -/

/-! ### Step (a) alone -/

/-! ### The converse forms -/

/-- Under RH, an odd bottom gap at `(L, N)` is `OddBottomBelow L N` together with step (a) at
`(L, N)`. -/
theorem oddBottomGap_iff_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) :
    OddBottomGap L N ↔
      OddBottomBelow L N ∧ OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  constructor
  · intro h
    refine ⟨?_, Cvs.StepA.OddBottomGapCriterion.oddAbove_of_oddBottomGap hRH hL h⟩
    obtain ⟨μ, o, hodd, hne, hMo, hbot, -, hΩ⟩ := h
    exact ⟨μ, o, hodd, hne, hMo, hbot, hΩ⟩
  · rintro ⟨⟨μ, o, hodd, hne, hMo, hbot, hΩ⟩, hA⟩
    have hμ := (Cvs.StepA.OddAboveUnderRH.oddAbove_iff_pos_of_RH hRH hL hodd hne hMo hbot hΩ).mp hA
    exact ⟨μ, o, hodd, hne, hMo, hbot, hμ, hΩ⟩

/-! ### `Ω_h` is at most the top mode frequency -/

/-- For odd `o`, `|o|² ≤ (2πN/L)²·|xdiv o|²`. -/
theorem dotProduct_le_sq_mul_xdiv (hL : 0 < L) {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) :
    o ⬝ᵥ o ≤ (2 * π * N / L) ^ 2 * (xdiv L N o ⬝ᵥ xdiv L N o) := by
  have hterm : ∀ i : Idx N, o i * o i ≤ (2 * π * N / L) ^ 2 * (xdiv L N o i * xdiv L N o i) := by
    intro i
    have hb : Cvs.Finite.OddEigenvectorResolvent.om L N i ^ 2 ≤ (2 * π * N / L) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (Cvs.StepA.ModePolynomialFarEnvelope.abs_omega_le hL.le N i) 2
    rw [← Cvs.Finite.OddEigenvectorResolvent.om_mul_xdiv hL N hodd i]
    calc Cvs.Finite.OddEigenvectorResolvent.om L N i * xdiv L N o i * (Cvs.Finite.OddEigenvectorResolvent.om L N i * xdiv L N o i)
        = Cvs.Finite.OddEigenvectorResolvent.om L N i ^ 2 * (xdiv L N o i * xdiv L N o i) := by ring
      _ ≤ (2 * π * N / L) ^ 2 * (xdiv L N o i * xdiv L N o i) :=
        mul_le_mul_of_nonneg_right hb (mul_self_nonneg _)
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hterm i

/-- For odd `o`, `Ω_h² ≤ (2πN/L)²`. -/
theorem omegaSq_le_sq (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) :
    omegaSq L N o ≤ (2 * π * N / L) ^ 2 := by
  rcases (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' (xdiv L N o)).eq_or_lt with hx | hx
  · rw [omegaSq, ← hx, div_zero]
    exact sq_nonneg _
  · exact (div_le_iff₀ hx).mpr (dotProduct_le_sq_mul_xdiv hL hodd)

/-! ### Below the first ordinate -/

/-- For odd `o`, `2πN/L < c` and every zero ordinate at least `c` in absolute value, `Ω_h²` lies
below every squared zero ordinate. -/
theorem omegaSq_lt_sq_im_of_bandwidth (hL : 0 < L) {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) {c : ℝ}
    (hgap : ∀ ρ : nonTrivialZeroSet, c ≤ |(ρ : ℂ).im|) (hband : 2 * π * N / L < c)
    (ρ : nonTrivialZeroSet) : omegaSq L N o < ((ρ : ℂ).im) ^ 2 := by
  have hK : 0 ≤ 2 * π * N / L := by positivity
  have hc : 0 ≤ c := hK.trans hband.le
  calc omegaSq L N o ≤ (2 * π * N / L) ^ 2 := omegaSq_le_sq hL hodd
    _ < c ^ 2 := pow_lt_pow_left₀ hband hK two_ne_zero
    _ ≤ |(ρ : ℂ).im| ^ 2 := pow_le_pow_left₀ hc (hgap ρ) 2
    _ = ((ρ : ℂ).im) ^ 2 := sq_abs _

/-- With at least one mode pair, `2πN/L < c` and every zero ordinate at least `c` in absolute value,
the window matrix has an odd bottom eigenpair with `Ω_h` below every zero ordinate. -/
theorem oddBottomBelow_of_bandwidth (hL : 0 < L) (hN : 0 < N) {c : ℝ}
    (hgap : ∀ ρ : nonTrivialZeroSet, c ≤ |(ρ : ℂ).im|) (hband : 2 * π * N / L < c) :
    OddBottomBelow L N := by
  obtain ⟨μ, o, hodd, ho1, hbot, hMo⟩ :=
    Cvs.StepA.OddSectorBottom.exists_odd_bottom hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ N hN
  have hne : o ≠ 0 := by
    rintro rfl
    simp at ho1
  exact ⟨μ, o, hodd, hne, hMo, hbot, omegaSq_lt_sq_im_of_bandwidth hL hodd hgap hband⟩

/-- With no mode pair, every odd vector is zero. -/
theorem eq_zero_of_odd_zero {o : Idx 0 → ℝ} (hodd : ∀ i, o (negI 0 i) = -o i) : o = 0 := by
  funext i
  rcases i with _ | ⟨k, -⟩
  · have h := hodd none
    simp only [negI] at h
    simp only [Pi.zero_apply]
    linarith
  · exact k.elim0

/-- With no mode pair, step (a) holds. -/
theorem oddAbove_zero (P R : ℕ) (hL : 0 < L) : OddAbove P R L hL 0 :=
  fun _ hodd hne => absurd (eq_zero_of_odd_zero hodd) hne

/-- Under RH, with `2πN/L < c`, every zero ordinate at least `c` in absolute value and more than `N`
distinct squared off-lattice ordinates, step (a) holds at `(L, N)`. -/
theorem oddAbove_of_RH_of_bandwidth (hRH : RiemannHypothesis) (hL : 0 < L) {c : ℝ}
    (hgap : ∀ ρ : nonTrivialZeroSet, c ≤ |(ρ : ℂ).im|) (hband : 2 * π * N / L < c)
    (hZ : (N : ℕ∞) < (offLatticeSq L).encard) :
    OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact oddAbove_zero _ _ hL
  · exact Cvs.StepA.OddBottomGapCriterion.oddAbove_of_oddBottomGap hRH hL
      (Cvs.StepA.OddBottomGapCriterion.oddBottomGap_of_RH_offLattice hRH hL hZ
        (oddBottomBelow_of_bandwidth hL hN hgap hband))

/-! ### At the zero-free height `6.24` -/

/-- Every nontrivial zero has `|γ| > 6.24`. -/
theorem lt_abs_im (ρ : nonTrivialZeroSet) : (6.24 : ℝ) < |(ρ : ℂ).im| :=
  Cvs.Zeta.WeightExponentialChord.abs_im_gt_of_riemannXi_eq_zero (Cvs.Zeta.ZeroIndex.riemannXi_apply_eq_zero ρ)

end Cvs.StepA.StepACriterion
