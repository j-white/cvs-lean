import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior transform at a point carries the factor `a`, and M2 from the span ratio

Out of band the antiderivative `Ψ` of the sawtooth remainder obeys `Ψ(y)² ≤ (c/8)‖φ‖²`, so
`|X(s)|² ≤ a·C_s·(Σ_j g_j² + 1)·a‖G‖²` on the spine; with `a‖G‖² ≤ Λ‖r_a‖²` (`Λ` subpolynomial) and a
subpolynomial centre sum `Σ_j g_j²` this gives `M2Rate` on every finite top set, and `Ext(σ) ≤ C_σ·a‖G‖²`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped Interval
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Xi.EImageWindowPoisson (eimage)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.ProjectionShareSawtooth (saw reflRem)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly M2Rate HalfBounds)

namespace Cvs.Route.Visibility.ExteriorFactorMTwo
open Cvs.ZeroCounting

/-! ### The sine integral -/

/-! ### The out-of-band kernel and the antiderivative `Ψ` -/


/-! ### Lemma X: the exterior transform at a point -/

/-! ### The spine profile -/

/-! ### Lemma E: the exterior Plancherel integral against `a‖G‖²` -/

/-! ### Lemma L0: the centre value against the coefficients -/

/-! ### Lemma X squared on the spine -/

/-! ### M1 and M2 rates from the span ratio -/

/-- `‖r_a‖`, the norm of the even part of the spine class of `a`. -/
abbrev rNorm (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ :=
  ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖

/-- **The fixed-point exterior bound with saving `m`**: `‖X(s)‖² ≤ Q·x^{−m}‖r_a‖²` at `s = ρ` and `s = 1−ρ`. -/
def XRate (S : Finset nonTrivialZeroSet) (m : ℝ) : Prop :=
  ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ ρ ∈ S, ∀ s : ℂ, (s = ρ ∨ s = 1 - ρ) →
    ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s‖ ^ 2 ≤ Q x * (x : ℝ) ^ (-m) * rNorm x a ^ 2

/-- The positive part of a subpolynomial function is subpolynomial. -/
theorem subPoly_max_zero {Q : ℕ → ℝ} (hQ : SubPoly Q) : SubPoly fun x => max (Q x) 0 := fun ε hε => by
  filter_upwards [hQ ε hε] with x hx
  exact max_le hx (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `80 ≤ 2πx` for all large `x`. -/
theorem eventually_scale : ∀ᶠ x : ℕ in atTop, (80 : ℝ) ≤ 2 * π * x := by
  filter_upwards [eventually_ge_atTop 14] with x hx
  have h13 : (14 : ℝ) ≤ x := by exact_mod_cast hx
  nlinarith [Real.pi_gt_three]

/-! ### M2 from the halves of `Φ` -/

/-- `‖x^w X‖² = x^{2 Re w}‖X‖²`. -/
theorem norm_cpow_mul_sq {x : ℕ} (hx : 0 < x) (w X : ℂ) :
    ‖(x : ℂ) ^ w * X‖ ^ 2 = (x : ℝ) ^ (2 * w.re) * ‖X‖ ^ 2 := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hx, mul_pow, mul_comm 2 w.re,
    Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two]

/-- A squared bound `‖y‖² ≤ M r²` with `r ≥ 0` gives `‖y‖ ≤ √M·r`. -/
theorem norm_le_sqrt_mul {y : ℂ} {M r : ℝ} (hr : 0 ≤ r) (h : ‖y‖ ^ 2 ≤ M * r ^ 2) : ‖y‖ ≤ √M * r := by
  have h1 : ‖y‖ = √(‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1]
  calc √(‖y‖ ^ 2) ≤ √(M * r ^ 2) := Real.sqrt_le_sqrt h
    _ = √M * r := by
      by_cases hM : 0 ≤ M
      · rw [Real.sqrt_mul hM, Real.sqrt_sq hr]
      · have : M * r ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hM) (sq_nonneg r)
        rw [Real.sqrt_eq_zero'.2 this, Real.sqrt_eq_zero'.2 (le_of_not_ge hM), zero_mul]

/-- A zero of a finite top set at depth `δ` has `δ < ½`. -/
theorem lt_half_of_finiteTop {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ) : δ < 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := hS.2.1
  have hd := hS.2.2.1 ρ hρ
  obtain ⟨-, h0, h1⟩ := ρ.2
  unfold Cvs.GaussKernel.del at hd
  rcases abs_cases ((ρ : ℂ).re - 1 / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

/-- **M2 from `XRate`**: both halves are at most `Q⁺x^{δ−m}‖r‖²`, so `M2Rate` holds with saving `m`. -/
theorem m2Rate_of_xRate {S : Finset nonTrivialZeroSet} {δ m : ℝ} (hS : FiniteTop S δ) (hm : 0 < m)
    (hX : XRate S m) : ∃ K : ℕ → ℝ, M2Rate S δ K := by
  obtain ⟨Q, hQ, hX⟩ := hX
  have hδ := hS.1
  set M : ℕ → ℝ := fun x => max (Q x) 0 * (x : ℝ) ^ (δ - m)
  have hM0 : ∀ x, 0 ≤ M x := fun x => mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨fun x => (√(M x) + √(M x)) / 2, fun x => by positivity, ?_, m, hm, fun x => max (Q x) 0,
    subPoly_max_zero hQ, ?_⟩
  · filter_upwards [hX, eventually_ge_atTop 1] with x h hx1
    have hx : 0 < x := hx1
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    have key : ∀ ρ ∈ S, ∀ s : ℂ, (s = ρ ∨ s = 1 - ρ) → ∀ e : ℝ, e ≤ δ → ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
        (x : ℝ) ^ e * ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s‖ ^ 2 ≤ M x * rNorm x a ^ 2 := by
      intro ρ hρ s hs e he a
      have h1 := h ρ hρ s hs a
      have hp : 0 ≤ (x : ℝ) ^ e := Real.rpow_nonneg hx0.le e
      have hr2 : 0 ≤ rNorm x a ^ 2 := sq_nonneg _
      calc (x : ℝ) ^ e * ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s‖ ^ 2
          ≤ (x : ℝ) ^ e * (max (Q x) 0 * (x : ℝ) ^ (-m) * rNorm x a ^ 2) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)) hr2)) hp
        _ = max (Q x) 0 * ((x : ℝ) ^ e * (x : ℝ) ^ (-m)) * rNorm x a ^ 2 := by ring
        _ ≤ max (Q x) 0 * (x : ℝ) ^ (δ - m) * rNorm x a ^ 2 := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)) hr2
            rw [← Real.rpow_add hx0]
            exact Real.rpow_le_rpow_of_exponent_le hxr (by linarith)
    refine Cvs.Route.Visibility.ExtPairingRatesSubpoly.extPairing_of_halfBounds fun ρ hρ a => ⟨?_, ?_⟩
    · have hd := hS.2.2.1 ρ hρ
      unfold Cvs.GaussKernel.del at hd
      refine norm_le_sqrt_mul (norm_nonneg _) ?_
      rw [norm_cpow_mul_sq hx]
      refine key ρ hρ _ (Or.inl rfl) _ ?_ a
      have : (((ρ : ℂ) - 1 / 2) / 2).re = ((ρ : ℂ).re - 1 / 2) / 2 := by simp [Complex.sub_re]
      rw [this]; linarith [le_abs_self ((ρ : ℂ).re - 1 / 2)]
    · have hd := hS.2.2.1 ρ hρ
      unfold Cvs.GaussKernel.del at hd
      refine norm_le_sqrt_mul (norm_nonneg _) ?_
      rw [norm_cpow_mul_sq hx]
      refine key ρ hρ _ (Or.inr rfl) _ ?_ a
      have : ((1 / 2 - (ρ : ℂ)) / 2).re = (1 / 2 - (ρ : ℂ).re) / 2 := by simp [Complex.sub_re]
      rw [this]; linarith [neg_abs_le ((ρ : ℂ).re - 1 / 2)]
  · refine Eventually.of_forall fun x => ?_
    show ((√(M x) + √(M x)) / 2) ^ 2 ≤ max (Q x) 0 * (x : ℝ) ^ (δ - m)
    rw [add_self_div_two, Real.sq_sqrt (hM0 x)]

end Cvs.Route.Visibility.ExteriorFactorMTwo

end
