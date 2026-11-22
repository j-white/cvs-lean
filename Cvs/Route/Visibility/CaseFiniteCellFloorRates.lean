import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.PlaneBridgePlateau
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Case F on route SEP: cell floors give M2 and M1, and the endpoints without `DepthToZero`

A cell floor `δ` bounds a linear functional by `(Σ_j ‖T e_j‖/√δ_j)‖r_a‖` (Cvs.Upstream.CoefficientFloorLinearBound); at a zero point `X` is linear in the
coefficients, so a floor sum `Σ_j ν_j/√δ_j ≤ C_ε x^{−1/2+ε}` gives `XRate S 1` and `M2Rate`, and the same sum over
`√Ext_{e_j}(σ)` gives `Ext(σ) ≤ x^{o(1)}‖r_a‖²`. The split `log(|g|+7/2) ≤ log(T₀+7/2) + log⁺(|g|/T₀)` with `ExteriorTransformHolomorphy`'s
Plancherel identity and a log-tail rate give the `Ψ_σ` rate, and the Bessel disc bound gives `M1Rate`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.ShareBesselFromExtPairing (ExtPairing R1Bessel)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly M2Rate M1Rate)
open Cvs.Route.Visibility.ExteriorFactorMTwo (XRate rNorm)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.CaseFiniteCellFloorRates
open Cvs.ZeroCounting

/-! ### Endpoints -/

/-! ### The per-`ε` forms -/

/-- **Per-`ε` constants give a subpolynomial function**: if for every `ε > 0` some `C` has `f ≤ C·x^ε`
eventually, then `f ≤ x^ε` eventually for every `ε > 0`. -/
theorem subPoly_of_forall_const {f : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ x : ℕ in atTop, f x ≤ C * (x : ℝ) ^ ε) : SubPoly f := by
  intro ε hε
  obtain ⟨C, hC⟩ := h (ε / 2) (by linarith)
  filter_upwards [hC, (Cvs.Route.Visibility.ExtPairingRatesSubpoly.tendsto_natCast_rpow (by linarith : 0 < ε / 2)).eventually_ge_atTop C,
    eventually_ge_atTop 1] with x h1 h2 h3
  rw [← Cvs.Route.Visibility.ExtPairingRatesSubpoly.rpow_half_mul_self h3]
  have hp : 0 ≤ (x : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hp)

/-! ### Cell floors and floor sums -/

/-- **A unit-coefficient cell floor** at `x`: `δ_j > 0`, and `δ_j ≤ cellEnergy x b` whenever `b_j = 1`. -/
def IsCellFloor (x : ℕ) (δ : Cvs.Approximant.SpineSubspace.SF x → ℝ) : Prop :=
  (∀ j, 0 < δ j) ∧ ∀ j (b : Cvs.Approximant.SpineSubspace.SF x → ℝ), b j = 1 → δ j ≤ Cvs.Upstream.CoefficientFloorLinearBound.cellEnergy x b

/-- **The floor sum rate** `Σ_j ν_j/√δ_j ≤ C_ε·x^{e+ε}` eventually, for every `ε > 0`. -/
def FloorSumRate (δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ) (e : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ x : ℕ in atTop, ∑ j, ν x j / √(δ x j) ≤ C * (x : ℝ) ^ (e + ε)

/-- **A floor sum, squared, is subpolynomial against `x^{2e}`**: with `S_x = Σ_j ν_j/√δ_j ≥ 0` eventually,
`S_x²·x^{−2e}` is subpolynomial. -/
theorem subPoly_sq_of_floorSumRate {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} {e : ℝ} (hs : FloorSumRate δ ν e)
    (h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ ∑ j, ν x j / √(δ x j)) :
    SubPoly fun x => (∑ j, ν x j / √(δ x j)) ^ 2 * (x : ℝ) ^ (-(2 * e)) := by
  refine subPoly_of_forall_const fun ε hε => ?_
  obtain ⟨C, hC⟩ := hs (ε / 2) (by linarith)
  refine ⟨C ^ 2, ?_⟩
  filter_upwards [hC, h0, eventually_ge_atTop 1] with x h1 h2 hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hx
  have hp : 0 ≤ (x : ℝ) ^ (-(2 * e)) := Real.rpow_nonneg hx0.le _
  have hsq : (∑ j, ν x j / √(δ x j)) ^ 2 ≤ (C * (x : ℝ) ^ (e + ε / 2)) ^ 2 :=
    pow_le_pow_left₀ h2 h1 2
  calc (∑ j, ν x j / √(δ x j)) ^ 2 * (x : ℝ) ^ (-(2 * e))
      ≤ (C * (x : ℝ) ^ (e + ε / 2)) ^ 2 * (x : ℝ) ^ (-(2 * e)) := mul_le_mul_of_nonneg_right hsq hp
    _ = C ^ 2 * ((x : ℝ) ^ (e + ε / 2) * (x : ℝ) ^ (e + ε / 2) * (x : ℝ) ^ (-(2 * e))) := by ring
    _ = C ^ 2 * (x : ℝ) ^ ε := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 2; ring

/-! ### Theorem M2 on route SEP -/

/-- **The exterior transform at a zero point is linear in the spine coefficients**:
`X_b(s) = Σ_j b_j X_{e_j}(s)` for `s ∈ {ρ, 1 − ρ}`. -/
theorem mellinR_ext_spine_eq_sum {x : ℕ} (hx : 80 ≤ 2 * π * x) (ρ : nonTrivialZeroSet) {s : ℂ}
    (hs : s = ρ ∨ s = 1 - ρ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) s
      = ∑ j, (b j : ℂ) * mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hxn : 0 < x := by exact_mod_cast hx0
  have key : ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s
      = -mellinR (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s := fun a => by
    obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx a
    obtain ⟨h1, h2⟩ := Cvs.Xi.WindowTransformExterior.mellinR_window_eq_neg_ext_of_zero (by positivity : (0 : ℝ) < 1 / x) hG hG₁ hGi
      ρ.2.2.1 ρ.2.2.2 ρ.2.1
    rcases hs with rfl | rfl
    · rw [h1, neg_neg]
    · rw [h2, neg_neg]
  rw [key b, Cvs.Approximant.SpineCoefficientMatrix.mellinR_window_spineG hxn b s]
  simp only [Cvs.Approximant.SpineCoefficientMatrix.uA, Cvs.Approximant.SpineCoefficientMatrix.uVec, key, mul_neg, Finset.sum_neg_distrib]

/-- The exterior transform at `s` on the rung basis, as a linear map of the coefficients. -/
def extAt (x : ℕ) (s : ℂ) : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] ℂ :=
  Fintype.linearCombination ℝ fun j => mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s

theorem extAt_apply (x : ℕ) (s : ℂ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    extAt x s b = ∑ j, (b j : ℂ) * mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s := by
  simp [extAt, Fintype.linearCombination_apply, Complex.real_smul]

theorem extAt_single (x : ℕ) (s : ℂ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    extAt x s (Pi.single j 1) = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s := by
  classical
  simp [extAt, Fintype.linearCombination_apply_single]

/-- **Theorem M2, step F7**: under a cell floor `δ` and per-rung bounds `‖X_{e_j}(s)‖ ≤ ν_j` at a zero point,
`‖X_b(s)‖ ≤ (Σ_j ν_j/√δ_j)·‖r_b‖`. -/
theorem norm_mellinR_ext_le_floorSum {x : ℕ} (hx : 80 ≤ 2 * π * x) {δ ν : Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (hδ : IsCellFloor x δ) (ρ : nonTrivialZeroSet) {s : ℂ} (hs : s = ρ ∨ s = 1 - ρ)
    (hν : ∀ j, ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s‖ ≤ ν j)
    (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) s‖ ≤ (∑ j, ν j / √(δ j)) * rNorm x b := by
  rw [mellinR_ext_spine_eq_sum hx ρ hs b, ← extAt_apply]
  refine (Cvs.Upstream.CoefficientFloorLinearBound.norm_le_of_cell_floor hx (extAt x s) δ hδ.1 hδ.2 b).trans
    (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (norm_nonneg _))
  rw [extAt_single]
  exact div_le_div_of_nonneg_right (hν j) (sqrt_nonneg _)

/-- **Theorem M2 (route SEP), the fixed-point form**: an eventual cell floor `δ`, per-rung bounds
`‖X_{e_j}(s)‖ ≤ ν_j` at `s ∈ {ρ, 1−ρ}`, `ρ ∈ S`, and the floor sum rate `Σ_j ν_j/√δ_j ≤ C_ε x^{−m/2+ε}` give
`XRate S m`. -/
theorem xRate_of_floorSum {S : Finset nonTrivialZeroSet} {m : ℝ} {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (δ x))
    (hν : ∀ᶠ x : ℕ in atTop, ∀ ρ ∈ S, ∀ s : ℂ, (s = ρ ∨ s = 1 - ρ) → ∀ j,
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s‖ ≤ ν x j)
    (hν0 : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j)
    (hs : FloorSumRate δ ν (-m / 2)) : XRate S m := by
  have h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ ∑ j, ν x j / √(δ x j) := by
    filter_upwards [hν0] with x h
    exact Finset.sum_nonneg fun j _ => div_nonneg (h j) (sqrt_nonneg _)
  refine ⟨_, subPoly_sq_of_floorSumRate hs h0, ?_⟩
  filter_upwards [hδ, hν, h0, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hδx hνx h0x hsc ρ hρ s hs' a
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc
  have h1 := norm_mellinR_ext_le_floorSum hsc hδx ρ hs' (hνx ρ hρ s hs') a
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : (x : ℝ) ^ (-(2 * (-m / 2))) * (x : ℝ) ^ (-m) = 1 := by
    rw [← Real.rpow_add hx0, show -(2 * (-m / 2)) + -m = 0 by ring, Real.rpow_zero]
  calc _ ≤ _ := h2
    _ = (∑ j, ν x j / √(δ x j)) ^ 2 * ((x : ℝ) ^ (-(2 * (-m / 2))) * (x : ℝ) ^ (-m)) * rNorm x a ^ 2 := by
        rw [e]; ring
    _ = _ := by ring

/-- **Theorem M2 (route SEP)**: on a finite top set, an eventual cell floor, nonnegative per-rung bounds
`‖X_{e_j}(s)‖ ≤ ν_j` at `s ∈ {ρ, 1−ρ}` and the floor sum rate `x^{−1/2+o(1)}` give `M2Rate` with saving 1. -/
theorem m2Rate_of_floorSum {S : Finset nonTrivialZeroSet} {δ' : ℝ} (hS : FiniteTop S δ')
    {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (δ x))
    (hν : ∀ᶠ x : ℕ in atTop, ∀ ρ ∈ S, ∀ s : ℂ, (s = ρ ∨ s = 1 - ρ) → ∀ j,
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s‖ ≤ ν x j)
    (hν0 : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) (hs : FloorSumRate δ ν (-1 / 2)) :
    ∃ K : ℕ → ℝ, M2Rate S δ' K :=
  Cvs.Route.Visibility.ExteriorFactorMTwo.m2Rate_of_xRate hS one_pos (xRate_of_floorSum hδ hν hν0 hs)

/-! ### Theorem R on route SEP -/

/-- The exterior space `L²((1, ∞))`. -/
abbrev L2e : Type := Lp ℝ 2 (volume.restrict (Ioi (1 : ℝ)))

/-- The weighted exterior profile `E_{G_b}(θ)·θ^{σ−1/2}` of the spine class `b`. -/
def extFun (x : ℕ) (σ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) : ℝ :=
  eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) θ * θ ^ (σ - 1 / 2)

theorem extFun_sq (x : ℕ) (σ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    extFun x σ b θ ^ 2 = eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) θ ^ 2 * θ ^ (2 * σ - 1) := by
  rw [extFun, mul_pow, sq (θ ^ (σ - 1 / 2)), ← Real.rpow_add hθ]
  congr 2; ring

theorem extFun_eq_sum (x : ℕ) (σ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) :
    extFun x σ b θ = ∑ j, b j * extFun x σ (Pi.single j 1) θ := by
  simp only [extFun]
  rw [Cvs.Approximant.SpineCoefficientMatrix.spineG_eq_sum, Cvs.Xi.EImageWindowPoisson.eimage_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- For `σ < 1` the weighted exterior profile is square integrable on `(1, ∞)`. -/
theorem memLp_extFun {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (extFun x σ b) 2 (volume.restrict (Ioi 1)) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have ha : (0 : ℝ) < 1 / x := by positivity
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx b
  have hGc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) (Icc 0 1) :=
    fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  have hm := Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc
  have hint := Cvs.Route.Visibility.ExteriorTransformPointBound.integrableOn_extInt hm (fun w hw => hK w (lt_trans one_pos hw)) hσ
  have hmeas : AEStronglyMeasurable (extFun x σ b) (volume.restrict (Ioi 1)) :=
    (hm.mul (measurable_id.pow_const _)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  refine hint.congr ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun θ (hθ : 1 < θ) => (extFun_sq x σ b (lt_trans one_pos hθ)).symm)

/-- The weighted exterior vector of rung `j` in `L²((1, ∞))`. -/
def extVec {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (j : Cvs.Approximant.SpineSubspace.SF x) : L2e :=
  (memLp_extFun hx hσ (Pi.single j 1)).toLp (extFun x σ (Pi.single j 1))

/-- **`Ext` is a squared norm**: `‖Σ_j b_j e_j‖² = Ext_{G_b}(σ)` for the weighted exterior vectors. -/
theorem norm_sq_sum_extVec {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ‖∑ j, b j • extVec hx hσ j‖ ^ 2 = Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) σ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have hae : (fun θ => ⟪(∑ j, b j • extVec hx hσ j) θ, (∑ j, b j • extVec hx hσ j) θ⟫_ℝ)
      =ᵐ[volume.restrict (Ioi (1 : ℝ))]
        fun θ => eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) θ ^ 2 * θ ^ (2 * σ - 1) := by
    filter_upwards [Cvs.L2a.PlaneBridgePlateau.coeFn_sum_smul_toLp _ (fun j => memLp_extFun hx hσ (Pi.single j 1)) b,
      ae_restrict_mem measurableSet_Ioi] with θ hθ hθ1
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    simp only [extVec] at hθ ⊢
    rw [hθ, ← extFun_eq_sum, extFun_sq x σ b (lt_trans one_pos hθ1)]
  rw [integral_congr_ae hae, Cvs.Route.Visibility.ExteriorTransformPointBound.extInt]

/-- The weighted exterior map of the coefficients, as a linear map into `L²((1, ∞))`. -/
def extMap {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] L2e :=
  Fintype.linearCombination ℝ (extVec hx hσ)

theorem norm_sq_extMap {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ‖extMap hx hσ b‖ ^ 2 = Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) σ := by
  rw [extMap, Fintype.linearCombination_apply, norm_sq_sum_extVec]

/-- **Theorem R, step F7**: under a cell floor `δ` and per-rung bounds `√Ext_{e_j}(σ) ≤ ν_j`,
`Ext_{G_b}(σ) ≤ (Σ_j ν_j/√δ_j)²·‖r_b‖²`. -/
theorem extInt_le_floorSum {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) {δ ν : Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (hδ : IsCellFloor x δ)
    (hν : ∀ j, √(Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ) ≤ ν j)
    (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) σ ≤ (∑ j, ν j / √(δ j)) ^ 2 * rNorm x b ^ 2 := by
  have h1 := Cvs.Upstream.CoefficientFloorLinearBound.norm_le_of_cell_floor hx (extMap hx hσ) δ hδ.1 hδ.2 b
  have hj : ∀ j, ‖extMap hx hσ (Pi.single j 1)‖ ≤ ν j := fun j => by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_extMap]; exact hν j
  have h2 : ‖extMap hx hσ b‖ ≤ (∑ j, ν j / √(δ j)) * rNorm x b :=
    h1.trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ =>
      div_le_div_of_nonneg_right (hj j) (sqrt_nonneg _)) (norm_nonneg _))
  rw [← norm_sq_extMap hx hσ, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- **Theorem R (route SEP)**: for `σ < 1`, an eventual cell floor, nonnegative per-rung bounds
`√Ext_{e_j}(σ) ≤ ν_j` and the floor sum rate `x^{o(1)}` give `Ext_{G_a}(σ) ≤ Q(x)‖r_a‖²`, `Q` subpolynomial. -/
theorem extRate_of_floorSum {σ : ℝ} (hσ : σ < 1) {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (δ x))
    (hν : ∀ᶠ x : ℕ in atTop, ∀ j,
      √(Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ) ≤ ν x j)
    (hν0 : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) (hs : FloorSumRate δ ν 0) :
    ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
      Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) σ ≤ Q x * rNorm x a ^ 2 := by
  have h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ ∑ j, ν x j / √(δ x j) := by
    filter_upwards [hν0] with x h
    exact Finset.sum_nonneg fun j _ => div_nonneg (h j) (sqrt_nonneg _)
  refine ⟨_, subPoly_sq_of_floorSumRate hs h0, ?_⟩
  filter_upwards [hδ, hν, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hδx hνx hsc a
  have h := extInt_le_floorSum hsc hσ hδx hνx a
  rwa [mul_zero, neg_zero, Real.rpow_zero, mul_one]

/-! ### The `Ψ_σ` split and Theorem M1 -/

/-- **The log-weighted line integral** `Ψ_σ = ∫_ℝ |X(σ + ig)|² log(|g| + 7/2) dg` of the spine class `b`. -/
def psiInt (x : ℕ) (σ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ :=
  ∫ g : ℝ, ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2)

/-- **The log tail** `∫_ℝ |X(σ + ig)|² log⁺(|g|/T₀) dg` of the spine class `b`. -/
def logTail (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ :=
  ∫ g : ℝ, ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0

/-- **The weight split**: `log(u + 7/2) ≤ log(T₀ + 7/2) + log⁺(u/T₀)` for `T₀ > 0`, `u ≥ 0`. -/
theorem log_add_le_split {T₀ u : ℝ} (hT : 0 < T₀) (hu : 0 ≤ u) :
    Real.log (u + 7 / 2) ≤ Real.log (T₀ + 7 / 2) + max (Real.log (u / T₀)) 0 := by
  rcases le_or_gt u T₀ with h | h
  · have := Real.log_le_log (by linarith) (by linarith : u + 7 / 2 ≤ T₀ + 7 / 2)
    linarith [le_max_right (Real.log (u / T₀)) 0]
  · have hu0 : 0 < u := lt_trans hT h
    have hle : u + 7 / 2 ≤ (T₀ + 7 / 2) * (u / T₀) := by
      rw [mul_div_assoc', le_div_iff₀ hT]; nlinarith
    have := Real.log_le_log (by linarith) hle
    rw [Real.log_mul (by linarith) (div_pos hu0 hT).ne'] at this
    linarith [le_max_left (Real.log (u / T₀)) 0]

/-- For `T₀ ≥ 1`, `0 ≤ log⁺(u/T₀) ≤ log(u + 7/2)` for `u ≥ 0`. -/
theorem logPos_le_log_add {T₀ u : ℝ} (hT : 1 ≤ T₀) (hu : 0 ≤ u) :
    max (Real.log (u / T₀)) 0 ≤ Real.log (u + 7 / 2) := by
  have h0 : 0 ≤ Real.log (u + 7 / 2) := Real.log_nonneg (by linarith)
  refine max_le ?_ h0
  have hT0 : 0 < T₀ := by linarith
  rcases le_or_gt (u / T₀) 1 with h | h
  · exact (Real.log_nonpos (div_nonneg hu hT0.le) h).trans h0
  · exact Real.log_le_log (by linarith) (by
      rw [div_le_iff₀ hT0]; nlinarith)

/-- **Lemma 9, the weight split** (`ExteriorTransformHolomorphy`'s Plancherel identity): for `σ < 1` and `T₀ ≥ 1`,
`Ψ_σ ≤ 2π log(T₀ + 7/2)·Ext(σ) + ∫|X(σ + ig)|² log⁺(|g|/T₀) dg`. -/
theorem psiInt_le_split {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ T₀ : ℝ} (hσ : σ < 1) (hT : 1 ≤ T₀)
    (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    psiInt x σ b ≤ 2 * π * Real.log (T₀ + 7 / 2) * Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) σ
      + logTail x σ T₀ b := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have ha : (0 : ℝ) < 1 / x := by positivity
  have hT0 : 0 < T₀ := by linarith
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx b
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  have hf : Integrable fun g : ℝ => ‖mellinR (ext (1 / x) G) (σ + g * I)‖ ^ 2 :=
    Cvs.Route.Visibility.ExteriorTransformPointBound.integrable_norm_sq_mellinR_indicator (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc)
      (fun w hw => hK w (lt_trans one_pos hw)) hσ
  have hP := Cvs.Route.Visibility.ExteriorTransformHolomorphy.integral_norm_sq_mellinR_ext ha hG hG₁ hGi hσ
  set f : ℝ → ℝ := fun g => ‖mellinR (ext (1 / x) G) (σ + g * I)‖ ^ 2
  have hExt0 : 0 ≤ Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) G σ :=
    setIntegral_nonneg measurableSet_Ioi fun θ (hθ : 1 < θ) =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans one_pos hθ).le _)
  have hL0 : 0 ≤ Real.log (T₀ + 7 / 2) := Real.log_nonneg (by linarith)
  have htail0 : 0 ≤ logTail x σ T₀ b :=
    integral_nonneg fun g => mul_nonneg (sq_nonneg _) (le_max_right _ _)
  by_cases hI : Integrable fun g => f g * Real.log (|g| + 7 / 2)
  · have hmeasT : AEStronglyMeasurable (fun g => f g * max (Real.log (|g| / T₀)) 0) volume :=
      hf.aestronglyMeasurable.mul
        ((Real.measurable_log.comp (continuous_abs.measurable.div_const T₀)).max measurable_const).aestronglyMeasurable
    have hIT : Integrable fun g => f g * max (Real.log (|g| / T₀)) 0 :=
      hI.mono' hmeasT (ae_of_all _ fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_max_right _ _))]
        exact mul_le_mul_of_nonneg_left (logPos_le_log_add hT (abs_nonneg g)) (sq_nonneg _))
    have hmono : psiInt x σ b ≤ ∫ g, (Real.log (T₀ + 7 / 2) * f g + f g * max (Real.log (|g| / T₀)) 0) :=
      integral_mono hI ((hf.const_mul _).add hIT) fun g => by
        have := log_add_le_split hT0 (abs_nonneg g)
        have hf0 : 0 ≤ f g := sq_nonneg _
        show f g * Real.log (|g| + 7 / 2) ≤ _
        nlinarith
    rw [integral_add (hf.const_mul _) hIT, integral_const_mul] at hmono
    calc psiInt x σ b ≤ _ := hmono
      _ = _ := by
        simp only [f] at hP ⊢
        rw [hP, logTail, Cvs.Route.Visibility.ExteriorTransformPointBound.extInt]; ring
  · rw [psiInt, integral_undef hI]
    positivity

/-- **`Ψ_σ` is finite when its log tail is**: for `σ < 1`, `T₀ ≥ 1`, an integrable log tail makes
`|X(σ + ig)|² log(|g| + 7/2)` integrable. -/
theorem integrable_psi_of_tail {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ T₀ : ℝ} (hσ : σ < 1) (hT : 1 ≤ T₀)
    (a : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    (ht : Integrable fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0) :
    Integrable fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2
        * Real.log (|g| + 7 / 2) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have ha : (0 : ℝ) < 1 / x := by positivity
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx a
  have hGc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (Icc 0 1) :=
    fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  have hf : Integrable fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2 :=
    Cvs.Route.Visibility.ExteriorTransformPointBound.integrable_norm_sq_mellinR_indicator (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc)
      (fun w hw => hK w (lt_trans one_pos hw)) hσ
  refine ((hf.const_mul (Real.log (T₀ + 7 / 2))).add ht).mono' (hf.aestronglyMeasurable.mul
    (Real.measurable_log.comp (continuous_abs.measurable.add_const _)).aestronglyMeasurable) ?_
  refine ae_of_all _ fun g => ?_
  have h0 : 0 ≤ Real.log (|g| + 7 / 2) := Real.log_nonneg (by linarith [abs_nonneg g])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h0)]
  have := log_add_le_split (by linarith : (0 : ℝ) < T₀) (abs_nonneg g)
  have hf0 : 0 ≤ ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2 := sq_nonneg _
  show _ ≤ Real.log (T₀ + 7 / 2) * _ + _
  nlinarith

/-- **The `Ψ_σ` rate**: `Ψ_σ` is finite and `Ψ_σ ≤ Q(x)‖r_a‖²` on `[σ₁, σ₂]` eventually, `Q` subpolynomial. -/
def PsiRate (σ₁ σ₂ : ℝ) : Prop :=
  ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ σ ∈ Icc σ₁ σ₂, ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    Integrable (fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2
        * Real.log (|g| + 7 / 2))
      ∧ psiInt x σ a ≤ Q x * rNorm x a ^ 2

/-- **The log-tail rate at `T₀ = 8πx`**: `∫|X(σ + ig)|² log⁺(|g|/(8πx)) dg` is finite and at most `Q(x)‖r_a‖²`
on `[σ₁, σ₂]` eventually, `Q` subpolynomial. -/
def LogTailRate (σ₁ σ₂ : ℝ) : Prop :=
  ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ σ ∈ Icc σ₁ σ₂, ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    Integrable (fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / (8 * π * x))) 0)
      ∧ logTail x σ (8 * π * x) a ≤ Q x * rNorm x a ^ 2

/-- `log(8πx + 7/2)` is subpolynomial. -/
theorem subPoly_log_eight_pi : SubPoly fun x : ℕ => Real.log (8 * π * x + 7 / 2) := by
  refine (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (Real.log (8 * π + 7 / 2)))).mono ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have h8 : 0 < 8 * π + 7 / 2 := by positivity
  rw [← Real.log_mul (by positivity) h8.ne']
  exact Real.log_le_log (by positivity) (by nlinarith [Real.pi_pos])

/-- **The `Ψ_σ` rate from Theorem R at `σ₂` and the log-tail rate**: for `σ₂ < 1`, an `Ext(σ₂)` rate and the
log-tail rate on `[σ₁, σ₂]` give `PsiRate σ₁ σ₂` (`Ext` is increasing in `σ`). -/
theorem psiRate_of_extRate {σ₁ σ₂ : ℝ} (hσ₂ : σ₂ < 1)
    (hE : ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
      Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) σ₂ ≤ Q x * rNorm x a ^ 2)
    (hT : LogTailRate σ₁ σ₂) : PsiRate σ₁ σ₂ := by
  obtain ⟨Q₁, hQ₁, hE⟩ := hE
  obtain ⟨Q₂, hQ₂, hT⟩ := hT
  set L : ℕ → ℝ := fun x => Real.log (8 * π * x + 7 / 2)
  have hL0 : ∀ x : ℕ, 0 ≤ L x := fun x => Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) x; nlinarith
    [Real.pi_pos])
  refine ⟨fun x => 2 * π * L x * max (Q₁ x) 0 + max (Q₂ x) 0, ?_, ?_⟩
  · refine (((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (2 * π)).mul subPoly_log_eight_pi
      (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall hL0)).mul
      (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ₁) (Eventually.of_forall fun x => by have := hL0 x; positivity)
      (Eventually.of_forall fun _ => le_max_right _ _)).add (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ₂) |>.mono ?_
    exact Eventually.of_forall fun x => le_of_eq (by ring)
  · filter_upwards [hE, hT, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hEx hTx hsc σ hσ a
    have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc
    have hT1 : 1 ≤ 8 * π * (x : ℝ) := by nlinarith [Real.pi_gt_three]
    have hσ1 : σ < 1 := lt_of_le_of_lt hσ.2 hσ₂
    have hs := psiInt_le_split hsc hσ1 hT1 a
    obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hsc a
    have hmono := Cvs.Route.Visibility.ExteriorTransformPointBound.extInt_mono (by positivity : (0 : ℝ) < 1 / x) hG hG₁ hGi hσ.2 hσ₂
    have hr : 0 ≤ rNorm x a ^ 2 := sq_nonneg _
    have h1 : Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) σ ≤ max (Q₁ x) 0 * rNorm x a ^ 2 :=
      hmono.trans ((hEx a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr))
    obtain ⟨hTi, hTb⟩ := hTx σ hσ a
    have h2 : logTail x σ (8 * π * x) a ≤ max (Q₂ x) 0 * rNorm x a ^ 2 :=
      hTb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
    have hc : 0 ≤ 2 * π * L x := by have := hL0 x; positivity
    refine ⟨integrable_psi_of_tail hsc hσ1 hT1 a hTi, ?_⟩
    calc psiInt x σ a ≤ 2 * π * L x * Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) σ
          + logTail x σ (8 * π * x) a := hs
      _ ≤ 2 * π * L x * (max (Q₁ x) 0 * rNorm x a ^ 2) + max (Q₂ x) 0 * rNorm x a ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hc) h2
      _ = _ := by ring

/-- **The Bessel disc bound with constant `A`**: for `80 ≤ 2πx`, `0 < δ`, `0 < r₀ ≤ (½ − δ)/2` and every zero
with `|Re ρ − ½| ≤ δ`, `Ψ_σ` finite and at most `M` on `|σ − ½| ≤ δ + r₀` give
`Σ_ρ m_ρ⟪r_a, U_ρ⟫² ≤ x^δ·(A(δ + r₀)/r₀²)·M`. -/
def BesselDisc (A : ℝ) : Prop :=
  ∀ (x : ℕ) (hx0 : (0 : ℝ) < x), 80 ≤ 2 * π * x → ∀ δ r₀ : ℝ, 0 < δ → 0 < r₀ → r₀ ≤ (1 / 2 - δ) / 2 →
    (∀ ρ : nonTrivialZeroSet, |Cvs.GaussKernel.del ρ| ≤ δ) → ∀ (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (M : ℝ),
    (∀ σ ∈ Icc (1 / 2 - (δ + r₀)) (1 / 2 + (δ + r₀)),
      Integrable (fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2
          * Real.log (|g| + 7 / 2)) ∧ psiInt x σ a ≤ M) →
    ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
            Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (x : ℝ) ^ δ * (A * (δ + r₀) / r₀ ^ 2) * M

/-- **Theorem M1 (route SEP)**: on a finite top set of depth `δ`, with `r₀ = (½ − δ)/2`, the Bessel disc bound and
the `Ψ_σ` rate on `|σ − ½| ≤ δ + r₀` give `M1Rate δ`. -/
theorem m1Rate_of_besselDisc {A : ℝ} (hA : 0 ≤ A) (hB : BesselDisc A) {S : Finset nonTrivialZeroSet} {δ : ℝ}
    (hS : FiniteTop S δ) (hP : PsiRate (1 / 2 - (δ + (1 / 2 - δ) / 2)) (1 / 2 + (δ + (1 / 2 - δ) / 2))) :
    ∃ Bess : ℕ → ℝ, M1Rate δ Bess := by
  obtain ⟨Q, hQ, hP⟩ := hP
  have hδ := hS.1
  have hδ' := Cvs.Route.Visibility.ExteriorFactorMTwo.lt_half_of_finiteTop hS
  set r₀ := (1 / 2 - δ) / 2
  have hr₀ : 0 < r₀ := by simp only [r₀]; linarith
  set C := A * (δ + r₀) / r₀ ^ 2
  have hC : 0 ≤ C := by have : 0 ≤ δ + r₀ := by linarith
                        positivity
  have hdel : ∀ ρ : nonTrivialZeroSet, |Cvs.GaussKernel.del ρ| ≤ δ := fun ρ => by
    by_cases h : ρ ∈ S
    · exact (hS.2.2.1 ρ h).le
    · exact (hS.2.2.2 ρ h).le
  refine ⟨fun x => (x : ℝ) ^ δ * C * max (Q x) 0, fun x => by
    have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) x) δ
    have := le_max_right (Q x) 0
    positivity, ?_, fun x => C * max (Q x) 0, ?_, ?_⟩
  · filter_upwards [hP, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hPx hsc hx0 r hr
    obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
    have h := hB x hx0 hsc δ r₀ hδ hr₀ le_rfl hdel a (max (Q x) 0 * rNorm x a ^ 2) fun σ hσ =>
      ⟨(hPx σ hσ a).1, (hPx σ hσ a).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
    calc _ ≤ _ := h
      _ = _ := by ring
  · exact (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const C).mul (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ) (Eventually.of_forall fun _ => hC)
      (Eventually.of_forall fun _ => le_max_right _ _)
  · exact Eventually.of_forall fun x => le_of_eq (by ring)

/-! ### Case F on route SEP, assembled -/

/-- **The `X` floor sum on `S`**: nonnegative per-rung bounds `‖X_{e_j}(s)‖ ≤ ν_j` at `s ∈ {ρ, 1 − ρ}`, `ρ ∈ S`,
whose floor sum against `δ` is `x^{−1/2+o(1)}`. -/
def XFloorSum (δ : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ) (S : Finset nonTrivialZeroSet) : Prop :=
  ∃ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ,
    (∀ᶠ x : ℕ in atTop, ∀ ρ ∈ S, ∀ s : ℂ, (s = ρ ∨ s = 1 - ρ) → ∀ j,
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s‖ ≤ ν x j)
    ∧ (∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) ∧ FloorSumRate δ ν (-1 / 2)

/-- **The `Ext` floor sum at `σ`**: nonnegative per-rung bounds `√Ext_{e_j}(σ) ≤ ν_j` whose floor sum against `δ`
is `x^{o(1)}`. -/
def ExtFloorSum (δ : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ) (σ : ℝ) : Prop :=
  ∃ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ,
    (∀ᶠ x : ℕ in atTop, ∀ j,
      √(Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ) ≤ ν x j)
    ∧ (∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) ∧ FloorSumRate δ ν 0

/-- **Case F's `h` on route SEP**: an eventual cell floor `δ`, the `X` floor sum on every finite top set, the
`Ext` floor sum at `σ₊ = ½ + δ' + (½ − δ')/2`, the log-tail rate on `|σ − ½| ≤ δ' + (½ − δ')/2` for every
`0 < δ' < ½`, and the Bessel disc bound give `Cvs.Route.Visibility.ExtPairingRatesSubpoly.rh_of_m1_m2`'s hypothesis `h`. -/
theorem caseF_h_of_floor {δ : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (δ x))
    (hX : ∀ (S : Finset nonTrivialZeroSet) (δ' : ℝ), FiniteTop S δ' → XFloorSum δ S)
    (hE : ∀ δ' : ℝ, 0 < δ' → δ' < 1 / 2 → ExtFloorSum δ (1 / 2 + (δ' + (1 / 2 - δ') / 2)))
    (hT : ∀ δ' : ℝ, 0 < δ' → δ' < 1 / 2 →
      LogTailRate (1 / 2 - (δ' + (1 / 2 - δ') / 2)) (1 / 2 + (δ' + (1 / 2 - δ') / 2)))
    {A : ℝ} (hA : 0 ≤ A) (hB : BesselDisc A) :
    ∀ (S : Finset nonTrivialZeroSet) (δ' : ℝ), FiniteTop S δ' →
      ∃ K Bess : ℕ → ℝ, M2Rate S δ' K ∧ M1Rate δ' Bess := fun S δ' hS => by
  have h0 := hS.1
  have h1 := Cvs.Route.Visibility.ExteriorFactorMTwo.lt_half_of_finiteTop hS
  obtain ⟨ν, hν, hν0, hs⟩ := hX S δ' hS
  obtain ⟨K, hK⟩ := m2Rate_of_floorSum hS hδ hν hν0 hs
  obtain ⟨μ, hμ, hμ0, hμs⟩ := hE δ' h0 h1
  have hσ : 1 / 2 + (δ' + (1 / 2 - δ') / 2) < 1 := by linarith
  obtain ⟨Bess, hB'⟩ := m1Rate_of_besselDisc hA hB hS
    (psiRate_of_extRate hσ (extRate_of_floorSum hσ hδ hμ hμ0 hμs) (hT δ' h0 h1))
  exact ⟨K, Bess, hK, hB'⟩

end Cvs.Route.Visibility.CaseFiniteCellFloorRates

end
