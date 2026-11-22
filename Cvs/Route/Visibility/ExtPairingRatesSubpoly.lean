import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.SpinePairingExteriorTransform
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior pairing and `R₁` Bessel rates from subpolynomial M1 and M2

With `Q` subpolynomial and some `m > 0`, `K² ≤ Q·x^{δ−m}` and `Bess ≤ Q·x^δ` give both rates of Cvs.Route.Visibility.ShareBesselFromExtPairing, and the
two halves of `Φ_ρ` within `Q·x^{δ−min(2δ,1)}` give the first with `m = min(2δ,1)`.
-/
noncomputable section

open Real Filter
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.SpinePairingExteriorTransform (extComb)
open Cvs.Route.Visibility.ShareBesselFromExtPairing (ExtPairing R1Bessel ExtPairingRate R1BesselRate)

namespace Cvs.Route.Visibility.ExtPairingRatesSubpoly
open Cvs.ZeroCounting

/-! ### Subpolynomial functions -/

/-- **Subpolynomial** (`f ≤ x^{o(1)}`): for every `ε > 0`, `f x ≤ x^ε` for all large `x`. -/
def SubPoly (f : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, f x ≤ (x : ℝ) ^ ε

/-- A function eventually below a subpolynomial one is subpolynomial. -/
theorem SubPoly.mono {f g : ℕ → ℝ} (hg : SubPoly g) (h : ∀ᶠ x : ℕ in atTop, f x ≤ g x) : SubPoly f :=
  fun ε hε => ((hg ε hε).and h).mono fun _ hx => hx.2.trans hx.1

/-- `x^ε → ∞` along the naturals for `ε > 0`. -/
theorem tendsto_natCast_rpow {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℕ => (x : ℝ) ^ ε) atTop atTop :=
  (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop

/-- Constants are subpolynomial. -/
theorem subPoly_const (C : ℝ) : SubPoly fun _ => C :=
  fun _ hε => (tendsto_natCast_rpow hε).eventually_ge_atTop C

/-- `log x` is subpolynomial. -/
theorem subPoly_log : SubPoly fun x => Real.log x := by
  intro ε hε
  have h := (isLittleO_log_rpow_atTop hε).bound one_pos
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with x hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 ε)] at hx
  exact (le_abs_self _).trans hx

/-- `x^{ε/2}·x^{ε/2} = x^ε` for `x ≥ 1`. -/
theorem rpow_half_mul_self {x : ℕ} (hx : 1 ≤ x) (ε : ℝ) :
    (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) = (x : ℝ) ^ ε := by
  rw [← Real.rpow_add (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hx)]; ring_nf

/-- A sum of subpolynomial functions is subpolynomial. -/
theorem SubPoly.add {f g : ℕ → ℝ} (hf : SubPoly f) (hg : SubPoly g) : SubPoly fun x => f x + g x := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by linarith), hg (ε / 2) (by linarith),
    (tendsto_natCast_rpow (by linarith : 0 < ε / 2)).eventually_ge_atTop 2, eventually_ge_atTop 1]
    with x h1 h2 h3 h4
  rw [← rpow_half_mul_self h4]
  nlinarith

/-- A product of eventually nonnegative subpolynomial functions is subpolynomial. -/
theorem SubPoly.mul {f g : ℕ → ℝ} (hf : SubPoly f) (hg : SubPoly g) (hf0 : ∀ᶠ x : ℕ in atTop, 0 ≤ f x)
    (hg0 : ∀ᶠ x : ℕ in atTop, 0 ≤ g x) : SubPoly fun x => f x * g x := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by linarith), hg (ε / 2) (by linarith), hf0, hg0, eventually_ge_atTop 1]
    with x h1 h2 h3 h4 h5
  rw [← rpow_half_mul_self h5]
  exact mul_le_mul h1 h2 h4 (h3.trans h1)

/-- **A subpolynomial factor is beaten by any power saving**: `Q·x^{d−m} ≤ ε·x^d` eventually, for `m > 0`. -/
theorem eventually_mul_rpow_le {Q : ℕ → ℝ} (hQ : SubPoly Q) {m : ℝ} (hm : 0 < m) (d : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x : ℕ in atTop, Q x * (x : ℝ) ^ (d - m) ≤ ε * (x : ℝ) ^ d := by
  have h0 : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(m / 2))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < m / 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hQ (m / 2) (by linarith), h0.eventually (ge_mem_nhds hε), eventually_ge_atTop 1]
    with x h1 h2 h3
  have hx : (0 : ℝ) < x := by exact_mod_cast Nat.lt_of_lt_of_le one_pos h3
  calc Q x * (x : ℝ) ^ (d - m) ≤ (x : ℝ) ^ (m / 2) * (x : ℝ) ^ (d - m) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx.le _)
    _ = (x : ℝ) ^ (-(m / 2)) * (x : ℝ) ^ d := by
        rw [← Real.rpow_add hx, ← Real.rpow_add hx]; ring_nf
    _ ≤ ε * (x : ℝ) ^ d := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx.le _)

/-! ### M1 and M2 as subpolynomial rates -/

/-- **M2's rate**: a pairing constant on `S` with `K² ≤ Q·x^{δ−m}` for some `m > 0`, `Q` subpolynomial. -/
def M2Rate (S : Finset nonTrivialZeroSet) (δ : ℝ) (K : ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ K x) ∧ (∀ᶠ x : ℕ in atTop, ExtPairing x S (K x))
    ∧ ∃ m : ℝ, 0 < m ∧ ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, K x ^ 2 ≤ Q x * (x : ℝ) ^ (δ - m)

/-- **M1's rate**: an `R₁` Bessel constant with `Bess ≤ Q·x^δ`, `Q` subpolynomial (Theorem B: `Q ~ log x`). -/
def M1Rate (δ : ℝ) (Bess : ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ Bess x) ∧ (∀ᶠ x : ℕ in atTop, R1Bessel x (Bess x))
    ∧ ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, Bess x ≤ Q x * (x : ℝ) ^ δ

/-- **M2 gives the pairing rate**: `K² ≤ Q·x^{δ−m}` with `m > 0` implies `K² = o(x^δ)`. -/
theorem extPairingRate_of_m2Rate {S : Finset nonTrivialZeroSet} {δ : ℝ} {K : ℕ → ℝ}
    (h : M2Rate S δ K) : ExtPairingRate S δ K := by
  obtain ⟨hK0, hKe, m, hm, Q, hQ, hKQ⟩ := h
  refine ⟨hK0, hKe, fun ε hε => ?_⟩
  filter_upwards [hKQ, eventually_mul_rpow_le hQ hm δ hε] with x h1 h2
  exact h1.trans h2

/-- From `0 ≤ y ≤ Q·x^e` with `x ≥ 1`: `0 ≤ Q`. -/
theorem nonneg_of_le_mul_rpow {y q : ℝ} {x : ℕ} (hx : 1 ≤ x) (e : ℝ) (hy : 0 ≤ y)
    (h : y ≤ q * (x : ℝ) ^ e) : 0 ≤ q := by
  have hp : 0 < (x : ℝ) ^ e := Real.rpow_pos_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hx) e
  exact le_of_not_gt fun hq => by nlinarith [mul_neg_of_neg_of_pos hq hp]

/-- **M1 and M2 give the Bessel rate**: `Bess·K² ≤ Q₁Q₂·x^{2δ−m} = o(x^{2δ})`. -/
theorem r1BesselRate_of_m1Rate {S : Finset nonTrivialZeroSet} {δ : ℝ} {K Bess : ℕ → ℝ}
    (hK : M2Rate S δ K) (hB : M1Rate δ Bess) : R1BesselRate δ K Bess := by
  obtain ⟨-, -, m, hm, Q₂, hQ₂, hKQ⟩ := hK
  obtain ⟨hB0, hBe, Q₁, hQ₁, hBQ⟩ := hB
  refine ⟨hB0, hBe, fun ε hε => ?_⟩
  have hQ1 : ∀ᶠ x : ℕ in atTop, 0 ≤ Q₁ x := by
    filter_upwards [hBQ, eventually_ge_atTop 1] with x h hx
    exact nonneg_of_le_mul_rpow hx δ (hB0 x) h
  have hQ2 : ∀ᶠ x : ℕ in atTop, 0 ≤ Q₂ x := by
    filter_upwards [hKQ, eventually_ge_atTop 1] with x h hx
    exact nonneg_of_le_mul_rpow hx _ (sq_nonneg _) h
  have hQ := hQ₁.mul hQ₂ hQ1 hQ2
  filter_upwards [hBQ, hKQ, hQ1, eventually_ge_atTop 1,
    eventually_mul_rpow_le hQ hm (2 * δ) hε] with x h1 h2 h3 h4 h5
  have hx : (0 : ℝ) < x := by exact_mod_cast Nat.lt_of_lt_of_le one_pos h4
  calc Bess x * K x ^ 2 ≤ (Q₁ x * (x : ℝ) ^ δ) * (Q₂ x * (x : ℝ) ^ (δ - m)) :=
        mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg h3 (Real.rpow_nonneg hx.le _))
    _ = Q₁ x * Q₂ x * (x : ℝ) ^ (2 * δ - m) := by
        rw [show 2 * δ - m = δ + (δ - m) by ring, Real.rpow_add hx]; ring
    _ ≤ ε * (x : ℝ) ^ (2 * δ) := h5

/-! ### M2 from the two halves of `Φ` -/

/-- **The two halves of `Φ_ρ`** at `x` on `S`: `‖x^{(ρ−½)/2}X(ρ)‖ ≤ A‖r_a‖` and `‖x^{(½−ρ)/2}X(1−ρ)‖ ≤ B‖r_a‖`. -/
def HalfBounds (x : ℕ) (S : Finset nonTrivialZeroSet) (A B : ℝ) : Prop :=
  ∀ ρ ∈ S, ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    ‖(x : ℂ) ^ (((ρ : ℂ) - 1 / 2) / 2) * mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) ρ‖
        ≤ A * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖
      ∧ ‖(x : ℂ) ^ ((1 / 2 - (ρ : ℂ)) / 2) * mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (1 - ρ)‖
        ≤ B * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖

/-- **The pairing bound from the halves**: `‖Φ_ρ‖ ≤ (A + B)‖r_a‖`, i.e. `ExtPairing` with `K = (A+B)/2`. -/
theorem extPairing_of_halfBounds {x : ℕ} {S : Finset nonTrivialZeroSet} {A B : ℝ} (h : HalfBounds x S A B) :
    ExtPairing x S ((A + B) / 2) := by
  intro ρ hρ a
  obtain ⟨h1, h2⟩ := h ρ hρ a
  refine (norm_add_le _ _).trans ?_
  linarith

end Cvs.Route.Visibility.ExtPairingRatesSubpoly

end
