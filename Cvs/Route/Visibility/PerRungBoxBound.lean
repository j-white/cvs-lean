import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowImageMellinClosed
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
# One per-rung box bound feeds both Case F's `X` floor sum and Case ∞'s exterior data; (M1′) below `½`

For `Re s < 1`, `X_b(s)` is linear in the spine coefficients. Per-rung continuations `F_j` of
`X_{e_j} + aG_{e_j}(0)/(2(1 − s))` on `TransplantAngleHighZeros`'s box, bounded with `|aG_{e_j}(0)|` by `ν_j`, give under a cell floor
`TransplantAngleHighZeros`'s `ExtData x ((Σ_j ν_j/√δ_j)²)`, so `CaseInfinityJointRates`'s `SEPData m` from the rate `x^{−m/2+o(1)}`, and `CaseFiniteCellFloorRates`'s `X` floor
sum on finite sets when `m ≥ 1`. A summable Bessel disc bound gives `CaseInfinityJointRates`'s `M1Prime m` when `Θ' < ½`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open scoped InnerProductSpace ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop mult)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Route.Visibility.ExteriorFactorMTwo (rNorm)
open Cvs.StepA.Edge.TransplantAngleHighZeros (sbox ExtData g0)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (IsCellFloor FloorSumRate XFloorSum PsiRate BesselDisc psiInt)
open Cvs.StepA.Edge.CaseInfinityJointRates (SEPData M1Prime topDepth)

namespace Cvs.Route.Visibility.PerRungBoxBound
open Cvs.ZeroCounting

/-! ### Linearity of the exterior transform left of `Re s = 1` -/

/-- For `Re s < 1` the exterior part of a spine profile is Mellin-convergent. -/
theorem mellinConvergent_ext {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) {s : ℂ} (hs : s.re < 1) :
    MellinConvergent (fun θ => (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) θ : ℂ)) s := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have ha : (0 : ℝ) < 1 / x := by positivity
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx a
  have hGc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (Icc (1 / x) 1) := fun u hu =>
    (hG u ⟨ha.le.trans hu.1, hu.2⟩).continuousAt.continuousWithinAt
  have h1 := (Cvs.Xi.WindowTransformExterior.mellinR_eimage ha hG hG₁ hGi hs).1
  have h2 := Cvs.Xi.WindowImageMellinClosed.mellinConvergent_window ha hGc.integrableOn_Icc s
  have e : (fun θ : ℝ => (θ : ℂ) ^ (s - 1) • ((ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) θ : ℝ) : ℂ))
      = fun θ : ℝ => (θ : ℂ) ^ (s - 1) • ((eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) θ : ℝ) : ℂ)
        - (θ : ℂ) ^ (s - 1) • ((window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) θ : ℝ) : ℂ) := by
    funext θ
    rw [Cvs.Xi.WindowTransformExterior.eimage_eq_window_add_ext ha _ θ]
    simp only [smul_eq_mul]; push_cast; ring
  unfold MellinConvergent
  rw [e]
  exact h1.sub h2

/-- The exterior part of a spine profile is the coefficient sum of the unit profiles. -/
theorem ext_spine_eq_sum (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) :
    ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) θ
      = ∑ j, b j * ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) θ := by
  unfold Cvs.Xi.WindowTransformExterior.ext
  rw [Cvs.Approximant.SpineCoefficientMatrix.spineG_eq_sum, Cvs.Xi.EImageWindowPoisson.eimage_sum]
  by_cases h : θ ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h, mul_zero, Finset.sum_const_zero]

/-- **The exterior transform is linear for `Re s < 1`**: `X_b(s) = Σ_j b_j X_{e_j}(s)`. -/
theorem mellinR_ext_eq_sum {x : ℕ} (hx : 80 ≤ 2 * π * x) {s : ℂ} (hs : s.re < 1) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) s
      = ∑ j, (b j : ℂ) * mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s := by
  unfold mellinR mellin
  have e : (fun θ : ℝ => (θ : ℂ) ^ (s - 1) • ((ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b) θ : ℝ) : ℂ))
      = fun θ : ℝ => ∑ j, (b j : ℂ) * ((θ : ℂ) ^ (s - 1)
          • ((ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) θ : ℝ) : ℂ)) := by
    funext θ
    rw [ext_spine_eq_sum]
    simp only [smul_eq_mul]; push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ fun j _ => (mellinConvergent_ext hx (Pi.single j 1) hs).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- `aG_b(0)` is the coefficient sum of the unit values. -/
theorem g0_eq_sum (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : g0 x b = ∑ j, b j * g0 x (Pi.single j 1) := by
  simp only [g0]
  rw [Cvs.Approximant.SpineCoefficientMatrix.spineG_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The per-rung box -/

/-- **The per-rung box data at `x`**: on `TransplantAngleHighZeros`'s box of height `x`, `F_j` is holomorphic, conjugate-symmetric, equal
to `X_{e_j}(s) + aG_{e_j}(0)/(2(1 − s))` for `Re s < 1`, and `‖F_j‖ ≤ ν_j`, `|aG_{e_j}(0)| ≤ ν_j`. -/
def BoxData (x : ℕ) (F : Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ) (ν : Cvs.Approximant.SpineSubspace.SF x → ℝ) : Prop :=
  ∀ j, DifferentiableOn ℂ (F j) (sbox x) ∧ (∀ s ∈ sbox x, F j (conj s) = conj (F j s))
    ∧ (∀ s ∈ sbox x, s.re < 1 → F j s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
        + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)))
    ∧ (∀ s ∈ sbox x, ‖F j s‖ ≤ ν j) ∧ |g0 x (Pi.single j 1)| ≤ ν j

/-- **The per-rung box bound with saving `m`**: per-rung box data at all large `x` whose floor sum against
`σ'_j/x` is `x^{−m/2+o(1)}`. -/
def RungBox (m : ℝ) : Prop :=
  ∃ (F : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ) (ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ),
    (∀ᶠ x : ℕ in atTop, BoxData x (F x) (ν x)) ∧ FloorSumRate Cvs.Route.Visibility.CaseFiniteFromWindowChain.sigmaFloor ν (-m / 2)

/-- **Exterior data from a cell floor and per-rung box data**: `ExtData x ((Σ_j ν_j/√δ_j)²)`. -/
theorem extData_of_boxData {x : ℕ} (hx : 80 ≤ 2 * π * x) {δ ν : Cvs.Approximant.SpineSubspace.SF x → ℝ} {F : Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ}
    (hδ : IsCellFloor x δ) (hB : BoxData x F ν) : ExtData x ((∑ j, ν j / √(δ j)) ^ 2) := fun a => by
  set S := ∑ j, ν j / √(δ j)
  have hS : ∀ T : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] ℂ, (∀ j, ‖T (Pi.single j 1)‖ ≤ ν j) → ‖T a‖ ≤ S * rNorm x a :=
    fun T hT => (Cvs.Upstream.CoefficientFloorLinearBound.norm_le_of_cell_floor hx T δ hδ.1 hδ.2 a).trans (mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hT j) (sqrt_nonneg _)) (norm_nonneg _))
  have sq_le : ∀ {u : ℝ}, 0 ≤ u → u ≤ S * rNorm x a → u ^ 2 ≤ S ^ 2 * rNorm x a ^ 2 := fun h0 h => by
    rw [← mul_pow]; exact pow_le_pow_left₀ h0 h 2
  set Tg : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] ℂ := Fintype.linearCombination ℝ fun j => (g0 x (Pi.single j 1) : ℂ)
  have hTg : ∀ b, Tg b = (g0 x b : ℂ) := fun b => by
    simp [Tg, Fintype.linearCombination_apply, g0_eq_sum x b, Complex.real_smul]
  set Fa : ℂ → ℂ := fun s => ∑ j, (a j : ℂ) * F j s
  set Ts : ℂ → (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] ℂ := fun s => Fintype.linearCombination ℝ fun j => F j s
  have hTs : ∀ s b, Ts s b = ∑ j, (b j : ℂ) * F j s := fun s b => by
    simp [Ts, Fintype.linearCombination_apply, Complex.real_smul]
  refine ⟨?_, Fa, ?_, ?_, ?_, ?_⟩
  · have h := hS Tg fun j => by rw [hTg, Complex.norm_real, Real.norm_eq_abs]; exact (hB j).2.2.2.2
    rw [hTg, Complex.norm_real, Real.norm_eq_abs] at h
    rw [← sq_abs]; exact sq_le (abs_nonneg _) h
  · exact DifferentiableOn.fun_sum fun j _ => (hB j).1.const_mul _
  · intro s hs
    simp only [Fa, map_sum, map_mul, Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun j _ => by rw [(hB j).2.1 s hs]
  · intro s hs hre
    simp only [Fa]
    rw [Finset.sum_congr rfl fun j _ => by rw [(hB j).2.2.1 s hs hre], mellinR_ext_eq_sum hx hre a,
      g0_eq_sum x a]
    push_cast
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · intro s hs
    have h := hS (Ts s) fun j => by
      rw [hTs]; simp only [Pi.single_apply]
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp only [if_true, Complex.ofReal_one, one_mul]
      exact (hB j).2.2.2.1 s hs
    rw [hTs] at h
    exact sq_le (norm_nonneg _) h

/-- **`CaseInfinityJointRates`'s `SEPData m` from a cell floor and per-rung box data** with floor sum rate `x^{−m/2+o(1)}`. -/
theorem sepData_of_floor_box {m : ℝ} {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} {F : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ}
    (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (δ x)) (hB : ∀ᶠ x : ℕ in atTop, BoxData x (F x) (ν x))
    (hs : FloorSumRate δ ν (-m / 2)) : SEPData m := by
  have h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ ∑ j, ν x j / √(δ x j) := by
    filter_upwards [hB] with x h
    exact Finset.sum_nonneg fun j _ =>
      div_nonneg ((abs_nonneg _).trans (h j).2.2.2.2) (sqrt_nonneg _)
  refine ⟨_, Cvs.Route.Visibility.CaseFiniteCellFloorRates.subPoly_sq_of_floorSumRate hs h0, ?_⟩
  filter_upwards [hδ, hB, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hδx hBx hx
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  refine Cvs.StepA.Edge.CaseInfinityJointRates.extData_mono (extData_of_boxData hx hδx hBx) (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add hx0, show -(2 * (-m / 2)) + -m = 0 by ring, Real.rpow_zero, mul_one]

/-- A nontrivial zero has `0 < Re ρ < 1`. -/
theorem re_mem (ρ : nonTrivialZeroSet) : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ⟨ρ.2.2.1, ρ.2.2.2⟩

/-- The pole constant of a finite set of zeros, `k_S = 1 + Σ_{ρ ∈ S} (1/(2Re ρ) + 1/(2(1 − Re ρ)))`. -/
def poleConst (S : Finset nonTrivialZeroSet) : ℝ :=
  1 + ∑ ρ ∈ S, (1 / (2 * (ρ : ℂ).re) + 1 / (2 * (1 - (ρ : ℂ).re)))

/-- At `s ∈ {ρ, 1 − ρ}`, `ρ ∈ S`: `1 + 1/(2|1 − s|) ≤ k_S`. -/
theorem one_add_inv_le_poleConst {S : Finset nonTrivialZeroSet} {ρ : nonTrivialZeroSet} (hρ : ρ ∈ S) {s : ℂ}
    (hs : s = ρ ∨ s = 1 - ρ) : 1 + 1 / (2 * ‖1 - s‖) ≤ poleConst S := by
  obtain ⟨h0, h1⟩ := re_mem ρ
  have hterm : ∀ σ ∈ S, 0 ≤ 1 / (2 * (σ : ℂ).re) + 1 / (2 * (1 - (σ : ℂ).re)) := fun σ _ => by
    obtain ⟨g0, g1⟩ := re_mem σ
    have : 0 < 1 - (σ : ℂ).re := by linarith
    positivity
  have hle := Finset.single_le_sum hterm hρ
  have key : 1 / (2 * ‖1 - s‖) ≤ 1 / (2 * (ρ : ℂ).re) + 1 / (2 * (1 - (ρ : ℂ).re)) := by
    rcases hs with rfl | rfl
    · have hb : 1 - (ρ : ℂ).re ≤ ‖1 - (ρ : ℂ)‖ := by
        have := Complex.abs_re_le_norm (1 - (ρ : ℂ))
        simp only [Complex.sub_re, Complex.one_re] at this
        exact (le_abs_self _).trans this
      have : 0 < 1 - (ρ : ℂ).re := by linarith
      have h2 : 1 / (2 * ‖1 - (ρ : ℂ)‖) ≤ 1 / (2 * (1 - (ρ : ℂ).re)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have : 0 ≤ 1 / (2 * (ρ : ℂ).re) := by positivity
      linarith
    · have hb : (ρ : ℂ).re ≤ ‖1 - (1 - (ρ : ℂ))‖ := by
        rw [sub_sub_cancel]; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      have h2 : 1 / (2 * ‖1 - (1 - (ρ : ℂ))‖) ≤ 1 / (2 * (ρ : ℂ).re) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have : 0 ≤ 1 / (2 * (1 - (ρ : ℂ).re)) := by have : 0 < 1 - (ρ : ℂ).re := by linarith
                                                  positivity
      linarith
  unfold poleConst
  linarith

/-- Eventually every zero of a finite set and its reflection lie in the box of height `x`. -/
theorem eventually_mem_sbox (S : Finset nonTrivialZeroSet) :
    ∀ᶠ x : ℕ in atTop, ∀ ρ ∈ S, ∀ s : ℂ, (s = ρ ∨ s = 1 - ρ) → s ∈ sbox x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ ρ ∈ S, |(ρ : ℂ).im|)
  filter_upwards [eventually_ge_atTop N] with x hx ρ hρ s hs
  have hxN : (N : ℝ) ≤ x := by exact_mod_cast hx
  have him : |(ρ : ℂ).im| < x :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun σ : nonTrivialZeroSet => |(σ : ℂ).im|)
      (fun σ _ => abs_nonneg _) hρ) (hN.trans_le hxN)
  obtain ⟨h0, h1⟩ := re_mem ρ
  rcases hs with rfl | rfl
  · exact ⟨by linarith, by linarith, him⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simpa [Complex.sub_im] using him

/-- **`CaseFiniteCellFloorRates`'s `X` floor sum from per-rung box data**: on a finite set `S`, a floor sum rate `x^{−m/2+o(1)}`,
`m ≥ 1`, of the box bounds is an `X` floor sum, with per-rung bound `k_S ν_j`. -/
theorem xFloorSum_of_box {m : ℝ} (hm : 1 ≤ m) {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ}
    {F : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ} (hB : ∀ᶠ x : ℕ in atTop, BoxData x (F x) (ν x))
    (hs : FloorSumRate δ ν (-m / 2)) (S : Finset nonTrivialZeroSet) : XFloorSum δ S := by
  have hk : 0 ≤ poleConst S := by
    obtain ⟨-, h⟩ : (0 : ℝ) ≤ 1 / (2 * ‖(1 : ℂ) - 1‖) ∧ True := ⟨by positivity, trivial⟩
    unfold poleConst
    have : 0 ≤ ∑ ρ ∈ S, (1 / (2 * (ρ : ℂ).re) + 1 / (2 * (1 - (ρ : ℂ).re))) :=
      Finset.sum_nonneg fun σ _ => by
        obtain ⟨g0, g1⟩ := re_mem σ
        have : 0 < 1 - (σ : ℂ).re := by linarith
        positivity
    linarith
  refine ⟨fun x j => poleConst S * ν x j, ?_, ?_,
    Cvs.Route.Visibility.CaseFiniteFromWindowChain.floorSumRate_mono (by linarith) (Cvs.Route.Visibility.CaseFiniteFromWindowChain.floorSumRate_const_mul hk hs)⟩
  · filter_upwards [hB, eventually_mem_sbox S] with x hBx hS ρ hρ s hs' j
    have hmem := hS ρ hρ s hs'
    have hre : s.re < 1 := by
      rcases hs' with rfl | rfl
      · exact (re_mem ρ).2
      · simp only [Complex.sub_re, Complex.one_re]; linarith [(re_mem ρ).1]
    have hs1 : (1 : ℂ) - s ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    obtain ⟨-, -, hF, hFν, hgν⟩ := hBx j
    have hX : mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
        = F x j s - (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)) := by rw [hF s hmem hre]; ring
    have hn : ‖(1 : ℂ) - s‖ ≠ 0 := norm_ne_zero_iff.mpr hs1
    have hn' : 0 < ‖(1 : ℂ) - s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hν0 : 0 ≤ ν x j := (abs_nonneg _).trans hgν
    rw [hX]
    calc ‖F x j s - (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))‖
        ≤ ‖F x j s‖ + ‖(g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))‖ := norm_sub_le _ _
      _ = ‖F x j s‖ + |g0 x (Pi.single j 1)| * (1 / (2 * ‖1 - s‖)) := by
          rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]; ring
      _ ≤ ν x j + ν x j * (1 / (2 * ‖1 - s‖)) := add_le_add (hFν s hmem)
          (mul_le_mul_of_nonneg_right hgν (by positivity))
      _ = ν x j * (1 + 1 / (2 * ‖1 - s‖)) := by ring
      _ ≤ ν x j * poleConst S := mul_le_mul_of_nonneg_left (one_add_inv_le_poleConst hρ hs') hν0
      _ = poleConst S * ν x j := by ring
  · filter_upwards [hB] with x hBx j
    exact mul_nonneg hk ((abs_nonneg _).trans (hBx j).2.2.2.2)

/-- **The per-rung box under the window chain's floor**: `RungBox m` and `η₀ < 1` give the box data and the floor
sum rate `x^{−m/2+o(1)}` against `cellFloor η₀`. -/
theorem rungBox_cellFloor {m η₀ : ℝ} (hη₀ : η₀ < 1) (h : RungBox m) :
    ∃ (F : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ) (ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ),
      (∀ᶠ x : ℕ in atTop, BoxData x (F x) (ν x)) ∧ FloorSumRate (fun x => Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) ν (-m / 2) := by
  obtain ⟨F, ν, hB, hs⟩ := h
  refine ⟨F, ν, hB, Cvs.Route.Visibility.CaseFiniteFromWindowChain.floorSumRate_cellFloor hη₀ ?_ hs⟩
  filter_upwards [hB] with x hBx j
  exact (abs_nonneg _).trans (hBx j).2.2.2.2

/-! ### (M1′) below `½` -/

/-- **The summable Bessel disc bound with constant `A`**: `CaseFiniteCellFloorRates`'s `BesselDisc A` together with the summability of
`m_ρ⟪r_a, U_ρ⟫²` under the same hypotheses. -/
def BesselDiscS (A : ℝ) : Prop :=
  ∀ (x : ℕ) (hx0 : (0 : ℝ) < x), 80 ≤ 2 * π * x → ∀ δ r₀ : ℝ, 0 < δ → 0 < r₀ → r₀ ≤ (1 / 2 - δ) / 2 →
    (∀ ρ : nonTrivialZeroSet, |Cvs.GaussKernel.del ρ| ≤ δ) → ∀ (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (M : ℝ),
    (∀ σ ∈ Icc (1 / 2 - (δ + r₀)) (1 / 2 + (δ + r₀)),
      Integrable (fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (σ + g * I)‖ ^ 2
          * Real.log (|g| + 7 / 2)) ∧ psiInt x σ a ≤ M) →
    (Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
            Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
    ∧ ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
            Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (x : ℝ) ^ δ * (A * (δ + r₀) / r₀ ^ 2) * M

theorem besselDisc_of_besselDiscS {A : ℝ} (h : BesselDiscS A) : BesselDisc A :=
  fun x hx0 hx δ r₀ hδ hr₀ hr hdel a M hM => (h x hx0 hx δ r₀ hδ hr₀ hr hdel a M hM).2

/-- **(M1′) for `Θ' < ½`** (caseinf-W Proposition 8.1): off RH with `Θ' < ½`, the summable Bessel disc bound and the
`Ψ_σ` rate on `|σ − ½| ≤ Θ' + (½ − Θ')/2` give `M1Prime m` for every `m > 0`. -/
theorem m1Prime_of_besselDiscS {A : ℝ} (hA : 0 ≤ A) (hB : BesselDiscS A) (hRH : ¬ RiemannHypothesis)
    (hΘ : topDepth < 1 / 2)
    (hP : PsiRate (1 / 2 - (topDepth + (1 / 2 - topDepth) / 2)) (1 / 2 + (topDepth + (1 / 2 - topDepth) / 2)))
    {m : ℝ} (hm : 0 < m) : M1Prime m := by
  obtain ⟨Q, hQ, hP⟩ := hP
  have hδ := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_pos hRH
  set r₀ := (1 / 2 - topDepth) / 2
  have hr₀ : 0 < r₀ := by simp only [r₀]; linarith
  set C := A * (topDepth + r₀) / r₀ ^ 2
  have hC : 0 ≤ C := by have : 0 ≤ topDepth + r₀ := by linarith
                        positivity
  refine Cvs.StepA.Edge.CaseInfinityJointRates.m1Prime_of_bessel (Q := fun x => C * max (Q x) 0)
    ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const C).mul (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ) (Eventually.of_forall fun _ => hC)
      (Eventually.of_forall fun _ => le_max_right _ _)) ?_ hm
  filter_upwards [hP, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hPx hsc hx0 r hr
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  obtain ⟨h1, h2⟩ := hB x hx0 hsc topDepth r₀ hδ hr₀ le_rfl Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_le_topDepth a
    (max (Q x) 0 * rNorm x a ^ 2) fun σ hσ =>
      ⟨(hPx σ hσ a).1, (hPx σ hσ a).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
  exact ⟨h1, h2.trans (le_of_eq (by simp only [C, rNorm]; ring))⟩

end Cvs.Route.Visibility.PerRungBoxBound

end
