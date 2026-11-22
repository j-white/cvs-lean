import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTruncationBound
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.SectorBottomsLowerBound
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The odd trial's on-line envelope
For `f ∈ C¹` vanishing at `±L/2`, `(1 + γ²)(∫ f sin γt)² ≤ (∫ f²)(∫ sin² γt) + (∫ f'²)(∫ cos² γt)`; for the
centred sine polynomial of an odd `o` on `0, ±1, …, ±N` this is `≤ L²(1 + (2πN/L)²) o⬝o`. So a zero on the
line adds at most `L(1 + (2πN/L)²) m_ρ/(1 + γ_ρ²) · L o⬝o` to `L oᵀ M_L o`, and any set of them at most
`onLineBound L N · L o⬝o`.
-/

noncomputable section

open Real MeasureTheory Matrix

namespace Cvs.StepA.OddTrialEnvelope
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Finite.OddSectorZeroSide (sinePoly sinePoly')
open Cvs.StepA.OneZeroParitySectors (uo vo)

/-! ### A profile vanishing at the ends of the window, against one sine -/

/-- For `f ∈ C¹` vanishing at `±L/2`, `γ ∫ f(t) sin(γt) dt = ∫ f'(t) cos(γt) dt` over `(−L/2, L/2)`. -/
theorem mul_integral_mul_sin_eq {L : ℝ} {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (h₁ : f (-(L / 2)) = 0) (h₂ : f (L / 2) = 0) (γ : ℝ) :
    γ * ∫ t in -(L / 2)..L / 2, f t * sin (γ * t)
      = ∫ t in -(L / 2)..L / 2, f' t * cos (γ * t) := by
  have hv : ∀ t, HasDerivAt (fun t => -cos (γ * t)) (sin (γ * t) * γ) t := fun t =>
    (((hasDerivAt_id' t).const_mul γ).cos.neg).congr_deriv (by ring)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -(L / 2)) (b := L / 2)
    (fun t _ => hf t) (fun t _ => hv t) (hf'.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => sin (γ * t) * γ).intervalIntegrable _ _)
  rw [h₁, h₂, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  rw [← intervalIntegral.integral_const_mul]
  calc ∫ t in -(L / 2)..L / 2, γ * (f t * sin (γ * t))
      = ∫ t in -(L / 2)..L / 2, f t * (sin (γ * t) * γ) :=
        intervalIntegral.integral_congr fun t _ => by ring
    _ = ∫ t in -(L / 2)..L / 2, f' t * cos (γ * t) := by
        rw [hibp, ← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun t _ => by ring

/-- For `f ∈ C¹` vanishing at `±L/2`,
`(1 + γ²)(∫ f sin γt)² ≤ (∫ f²)(∫ sin² γt) + (∫ f'²)(∫ cos² γt)` over `(−L/2, L/2)`. -/
theorem one_add_sq_mul_sq_integral_mul_sin_le {L : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (h₁ : f (-(L / 2)) = 0)
    (h₂ : f (L / 2) = 0) (γ : ℝ) :
    (1 + γ ^ 2) * (∫ t in -(L / 2)..L / 2, f t * sin (γ * t)) ^ 2
      ≤ (∫ t in -(L / 2)..L / 2, f t ^ 2) * (∫ t in -(L / 2)..L / 2, sin (γ * t) ^ 2)
        + (∫ t in -(L / 2)..L / 2, f' t ^ 2) * (∫ t in -(L / 2)..L / 2, cos (γ * t) ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have h1 := Cvs.StepA.OneZeroSectorBottoms.winForm_sq_le L ⟨f, hfc⟩ ⟨fun t => sin (γ * t), by fun_prop⟩
  have h2 := Cvs.StepA.OneZeroSectorBottoms.winForm_sq_le L ⟨f', hf'⟩ ⟨fun t => cos (γ * t), by fun_prop⟩
  rw [Cvs.StepA.OneZeroParitySectors.winForm_sq, Cvs.StepA.OneZeroParitySectors.winForm_sq,
    Cvs.StepA.OneZeroParitySectors.winForm_apply] at h1 h2
  simp only [ContinuousMap.coe_mk] at h1 h2
  have e : (1 + γ ^ 2) * (∫ t in -(L / 2)..L / 2, f t * sin (γ * t)) ^ 2
      = (∫ t in -(L / 2)..L / 2, f t * sin (γ * t)) ^ 2
        + (γ * ∫ t in -(L / 2)..L / 2, f t * sin (γ * t)) ^ 2 := by ring
  rw [e, mul_integral_mul_sin_eq hf hf' h₁ h₂ γ]
  exact add_le_add h1 h2

/-- For `f ∈ C¹` vanishing at `±L/2` and `L ≥ 0`,
`(1 + γ²)(∫ f sin γt)² ≤ L (∫ f² + ∫ f'²)` over `(−L/2, L/2)`. -/
theorem one_add_sq_mul_sq_integral_mul_sin_le_mul {L : ℝ} (hL : 0 ≤ L) {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (h₁ : f (-(L / 2)) = 0)
    (h₂ : f (L / 2) = 0) (γ : ℝ) :
    (1 + γ ^ 2) * (∫ t in -(L / 2)..L / 2, f t * sin (γ * t)) ^ 2
      ≤ L * ((∫ t in -(L / 2)..L / 2, f t ^ 2) + ∫ t in -(L / 2)..L / 2, f' t ^ 2) := by
  refine (one_add_sq_mul_sq_integral_mul_sin_le hf hf' h₁ h₂ γ).trans ?_
  have hab : -(L / 2) ≤ L / 2 := by linarith
  have hone : ∫ t in -(L / 2)..L / 2, (1 : ℝ) = L := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
  have hsin : ∫ t in -(L / 2)..L / 2, sin (γ * t) ^ 2 ≤ L :=
    (intervalIntegral.integral_mono_on (μ := volume) hab
      ((by fun_prop : Continuous fun t => sin (γ * t) ^ 2).intervalIntegrable _ _)
      intervalIntegrable_const fun t _ => sin_sq_le_one _).trans_eq hone
  have hcos : ∫ t in -(L / 2)..L / 2, cos (γ * t) ^ 2 ≤ L :=
    (intervalIntegral.integral_mono_on (μ := volume) hab
      ((by fun_prop : Continuous fun t => cos (γ * t) ^ 2).intervalIntegrable _ _)
      intervalIntegrable_const fun t _ => cos_sq_le_one _).trans_eq hone
  have hf2 : 0 ≤ ∫ t in -(L / 2)..L / 2, f t ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hf'2 : 0 ≤ ∫ t in -(L / 2)..L / 2, f' t ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  calc (∫ t in -(L / 2)..L / 2, f t ^ 2) * (∫ t in -(L / 2)..L / 2, sin (γ * t) ^ 2)
        + (∫ t in -(L / 2)..L / 2, f' t ^ 2) * (∫ t in -(L / 2)..L / 2, cos (γ * t) ^ 2)
      ≤ (∫ t in -(L / 2)..L / 2, f t ^ 2) * L + (∫ t in -(L / 2)..L / 2, f' t ^ 2) * L :=
        add_le_add (mul_le_mul_of_nonneg_left hsin hf2) (mul_le_mul_of_nonneg_left hcos hf'2)
    _ = L * ((∫ t in -(L / 2)..L / 2, f t ^ 2) + ∫ t in -(L / 2)..L / 2, f' t ^ 2) := by ring

/-! ### The centred sine polynomial -/

section Modes

variable {ι : Type*} [Fintype ι]

/-- The derivative of a sine polynomial is the cosine polynomial with coefficients `oᵢ ωᵢ`. -/
theorem sinePoly'_eq_cosPoly (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) :
    sinePoly' L mode o
      = Cvs.Finite.EvenSectorZeroSide.cosPoly L mode fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i := by
  funext y
  unfold sinePoly' Cvs.Finite.EvenSectorZeroSide.cosPoly
  exact Finset.sum_congr rfl fun i _ => by ring

/-- For a symmetric injective mode set and odd `o`, the centred sine polynomial `g` satisfies
`(1 + γ²)(∫ g sin γt)² ≤ L² (o⬝o + ∑ᵢ (oᵢ ωᵢ)²)` over `(−L/2, L/2)`. -/
theorem one_add_sq_mul_sq_integral_sinePoly_le {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i)
    {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) (γ : ℝ) :
    (1 + γ ^ 2) * (∫ t in -(L / 2)..L / 2, sinePoly L mode o (t + L / 2) * sin (γ * t)) ^ 2
      ≤ L ^ 2 * (o ⬝ᵥ o + (fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
          ⬝ᵥ fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i) := by
  have hd : ∀ t, HasDerivAt (fun t => sinePoly L mode o (t + L / 2))
      (sinePoly' L mode o (t + L / 2)) t := fun t =>
    HasDerivAt.comp_add_const t (L / 2) (Cvs.Finite.OddSectorZeroSide.hasDerivAt_sinePoly L mode o _)
  have hc' : Continuous fun t => sinePoly' L mode o (t + L / 2) :=
    (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly' L mode o).comp (continuous_add_const _)
  have h₁ : sinePoly L mode o (-(L / 2) + L / 2) = 0 := by
    rw [neg_add_cancel]; exact Cvs.Finite.OddSectorZeroSide.sinePoly_zero L mode o
  have h₂ : sinePoly L mode o (L / 2 + L / 2) = 0 := by
    rw [add_halves]; exact Cvs.Finite.OddSectorZeroSide.sinePoly_L hL mode o
  have h := one_add_sq_mul_sq_integral_mul_sin_le_mul hL.le hd hc' h₁ h₂ γ
  have hxi : ∀ i, (fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i) (neg i)
      = (fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i) i := by
    intro i
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega, hodd, hmode, Int.cast_neg]
    ring
  rw [Cvs.StepA.SectorBottomsLowerBound.integral_sinePoly_centred_sq hL.ne' hinj hmode hodd,
    sinePoly'_eq_cosPoly, Cvs.StepA.SectorBottomsLowerBound.integral_cosPoly_centred_sq hL.ne' hinj hmode hxi]
    at h
  calc (1 + γ ^ 2) * (∫ t in -(L / 2)..L / 2, sinePoly L mode o (t + L / 2) * sin (γ * t)) ^ 2
      ≤ L * (L * (o ⬝ᵥ o) + L * ((fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
          ⬝ᵥ fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)) := h
    _ = L ^ 2 * (o ⬝ᵥ o + (fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
          ⬝ᵥ fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i) := by ring

end Modes

/-- On the modes `0, ±1, …, ±N` and `L > 0`, every window frequency satisfies `ωᵢ² ≤ (2πN/L)²`. -/
theorem omega_sq_le {L : ℝ} (hL : 0 < L) (N : ℕ) (i : Idx N) :
    Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i ^ 2 ≤ (2 * π * N / L) ^ 2 := by
  have hm : |((mode N i : ℤ) : ℝ)| ≤ N := by exact_mod_cast Cvs.Finite.ModeTruncationBound.abs_mode_le N i
  have habs : |Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i| ≤ 2 * π * N / L := by
    rw [Cvs.Finite.TruncationZeroFreeOffAxes.omega, abs_div, abs_mul, abs_of_pos hL,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    gcongr
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- **The odd trial against one on-line sine**: for odd `o` on the modes `0, ±1, …, ±N` and `L > 0`,
`(1 + γ²)(∫ g sin γt)² ≤ L²(1 + (2πN/L)²) o⬝o`, `g` the sine polynomial centred at `L/2`. -/
theorem one_add_sq_mul_sq_integral_le {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ}
    (ho : ∀ i, o (negI N i) = -o i) (γ : ℝ) :
    (1 + γ ^ 2) * (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2) * sin (γ * t)) ^ 2
      ≤ L ^ 2 * (1 + (2 * π * N / L) ^ 2) * (o ⬝ᵥ o) := by
  refine (one_add_sq_mul_sq_integral_sinePoly_le hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) ho γ).trans ?_
  have hsum : ((fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i)
        ⬝ᵥ fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i)
      ≤ (2 * π * N / L) ^ 2 * (o ⬝ᵥ o) := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := mul_le_mul_of_nonneg_left (omega_sq_le hL N i) (mul_self_nonneg (o i))
    linarith
  calc L ^ 2 * (o ⬝ᵥ o + (fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i)
          ⬝ᵥ fun i => o i * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i)
      ≤ L ^ 2 * (o ⬝ᵥ o + (2 * π * N / L) ^ 2 * (o ⬝ᵥ o)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (sq_nonneg L)
    _ = L ^ 2 * (1 + (2 * π * N / L) ^ 2) * (o ⬝ᵥ o) := by ring

/-! ### The zeros on the critical line -/

/-- The on-line budget `L(1 + (2πN/L)²) ∑_ρ m_ρ/(1 + γ_ρ²)`. -/
def onLineBound (L : ℝ) (N : ℕ) : ℝ :=
  L * (1 + (2 * π * N / L) ^ 2) * ∑' ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
    (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))

/-- At a zero on the critical line the odd-sector weights are `uo = sin(γt)` and `vo = 0`. -/
theorem uo_vo_of_re_eq_half {ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (hρ : (ρ : ℂ).re = 1 / 2) (t : ℝ) :
    uo (Cvs.ZeroCounting.zPoint ρ) t = sin ((ρ : ℂ).im * t) ∧ vo (Cvs.ZeroCounting.zPoint ρ) t = 0 := by
  rw [Cvs.ZeroCounting.zPoint_of_re_eq_half hρ]
  exact ⟨by simp [uo], Cvs.StepA.OneZeroParitySectors.vo_eq_zero (by simp) t⟩

/-- At a zero on the critical line, the odd pairing difference of any profile `g` is `(∫ g sin γt)²`. -/
theorem sq_sub_sq_of_re_eq_half {L : ℝ} (g : ℝ → ℝ) {ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (hρ : (ρ : ℂ).re = 1 / 2) :
    (∫ t in -(L / 2)..L / 2, g t * uo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2
        - (∫ t in -(L / 2)..L / 2, g t * vo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2
      = (∫ t in -(L / 2)..L / 2, g t * sin ((ρ : ℂ).im * t)) ^ 2 := by
  simp only [(uo_vo_of_re_eq_half hρ _).1, (uo_vo_of_re_eq_half hρ _).2, mul_zero,
    intervalIntegral.integral_zero]
  ring

/-- **One zero on the line in the odd sector**: for odd `o`, `m_ρ` times the odd pairing difference is at
most `L(1 + (2πN/L)²) · m_ρ/(1 + γ_ρ²) · L o⬝o`. -/
theorem onLine_term_le {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ}
    (ho : ∀ i, o (negI N i) = -o i) {ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (hρ : (ρ : ℂ).re = 1 / 2) :
    (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ((∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2)
              * uo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2
          - (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2)
              * vo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2)
      ≤ L * (1 + (2 * π * N / L) ^ 2)
          * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))) * (L * (o ⬝ᵥ o)) := by
  rw [sq_sub_sq_of_re_eq_half _ hρ]
  set X := ∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2) * sin ((ρ : ℂ).im * t)
  have h := one_add_sq_mul_sq_integral_le hL N ho (ρ : ℂ).im
  have hpos : 0 < 1 + ((ρ : ℂ).im) ^ 2 := by positivity
  have hw : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2)) := by
    positivity
  calc (Cvs.Criterion.divisorWeight ρ : ℝ) * X ^ 2
      = (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))
          * ((1 + ((ρ : ℂ).im) ^ 2) * X ^ 2) := by field_simp
    _ ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))
          * (L ^ 2 * (1 + (2 * π * N / L) ^ 2) * (o ⬝ᵥ o)) := mul_le_mul_of_nonneg_left h hw
    _ = L * (1 + (2 * π * N / L) ^ 2)
          * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2)))
          * (L * (o ⬝ᵥ o)) := by ring

/-- At a zero on the critical line, `m_ρ` times the odd pairing difference is nonnegative. -/
theorem onLine_term_nonneg {L : ℝ} (g : ℝ → ℝ) {ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (hρ : (ρ : ℂ).re = 1 / 2) :
    0 ≤ (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ((∫ t in -(L / 2)..L / 2, g t * uo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2
          - (∫ t in -(L / 2)..L / 2, g t * vo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2) := by
  rw [sq_sub_sq_of_re_eq_half g hρ]
  positivity

/-- For odd `o` and a set `S` of zeros on the critical line, `m_ρ` times the odd pairing difference is
summable over `S`. -/
theorem summable_onLine {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ}
    (ho : ∀ i, o (negI N i) = -o i) {S : Set Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (hS : ∀ ρ ∈ S, (ρ : ℂ).re = 1 / 2) :
    Summable fun ρ : S => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ((∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2)
              * uo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2
          - (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2)
              * vo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2) := by
  have hg := ((Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left
    (L * (1 + (2 * π * N / L) ^ 2))).mul_right (L * (o ⬝ᵥ o))).subtype (· ∈ S)
  exact Summable.of_nonneg_of_le (fun ρ => onLine_term_nonneg _ (hS ρ ρ.2))
    (fun ρ => onLine_term_le hL N ho (hS ρ ρ.2)) hg

/-- **The zeros on the line in the odd sector**: for odd `o` and a set `S` of zeros on the critical line,
`∑_{ρ ∈ S} m_ρ` times the odd pairing difference is at most `onLineBound L N · L o⬝o`. -/
theorem tsum_onLine_le {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ}
    (ho : ∀ i, o (negI N i) = -o i) {S : Set Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (hS : ∀ ρ ∈ S, (ρ : ℂ).re = 1 / 2) :
    ∑' ρ : S, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ((∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2)
              * uo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2
          - (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2)
              * vo (Cvs.ZeroCounting.zPoint ρ) t) ^ 2)
      ≤ onLineBound L N * (L * (o ⬝ᵥ o)) := by
  set b : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℝ := fun ρ =>
    L * (1 + (2 * π * N / L) ^ 2)
      * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))) * (L * (o ⬝ᵥ o))
    with hb
  have hbs : Summable b := (Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left
    (L * (1 + (2 * π * N / L) ^ 2))).mul_right (L * (o ⬝ᵥ o))
  have hb0 : ∀ ρ, 0 ≤ b ρ := fun ρ => by
    have : 0 ≤ o ⬝ᵥ o := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (o i)
    simp only [hb]; positivity
  calc _ ≤ ∑' ρ : S, b ρ :=
        Summable.tsum_le_tsum (fun ρ => onLine_term_le hL N ho (hS ρ ρ.2))
          (summable_onLine hL N ho hS) (hbs.subtype (· ∈ S))
    _ ≤ ∑' ρ, b ρ := Summable.tsum_subtype_le b S hb0 hbs
    _ = onLineBound L N * (L * (o ⬝ᵥ o)) := by
        simp only [hb, onLineBound]
        rw [tsum_mul_right, tsum_mul_left]

end Cvs.StepA.OddTrialEnvelope
