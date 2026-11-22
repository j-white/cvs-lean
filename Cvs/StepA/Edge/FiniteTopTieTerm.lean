import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.SectorGramBoxTransform
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tie term of a finite top set and the closing along phase returns

For `σ ∈ S` with `FiniteTop S δ`, `⟪V_σ, U_ρ⟫` and `⟪V_σ, V_ρ⟫` (`ρ ∈ S`) are closed forms in `Re ρ − Re σ`,
`Im ρ ± Im σ`, `δ` and `L = log x`; the `b`-side rest of Cvs.Route.Visibility.VisibilityClosingStep splits into this tie term and a sum over `ρ ∉ S`.
The closing inequality, needed only at `x` where the phases `e^{i Im ρ · L/2}`, `ρ ∈ S`, return near those
of a fixed `L₀`, gives `¬ EvenBulkFloor x 0` frequently and, with Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor, `RiemannHypothesis`.
-/

noncomputable section

open Real MeasureTheory Filter
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.StepA.TopQuadruple (quadWeight)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec ueProf)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.FiniteTopTieTerm
open Cvs.ZeroCounting

/-! ### Two closed window integrals -/

/-- `∫_{−L/2}^{L/2} sin(at) sinh(bt) dt`. -/
def sinSinhInt (a b L : ℝ) : ℝ := ∫ t in -(L / 2)..L / 2, sin (a * t) * sinh (b * t)

/-- `∫_{−L/2}^{L/2} cos(at) cosh(bt) dt`. -/
def cosCoshInt (a b L : ℝ) : ℝ := ∫ t in -(L / 2)..L / 2, cos (a * t) * cosh (b * t)

/-- The closed form `2(b sin(aL/2) cosh(bL/2) − a cos(aL/2) sinh(bL/2))/(a² + b²)`. -/
def sinSinhC (a b L : ℝ) : ℝ :=
  2 * (b * sin (a * L / 2) * cosh (b * L / 2) - a * cos (a * L / 2) * sinh (b * L / 2)) / (a ^ 2 + b ^ 2)

/-- The closed form `2(a sin(aL/2) cosh(bL/2) + b cos(aL/2) sinh(bL/2))/(a² + b²)`, and `L` at `a = b = 0`. -/
def cosCoshC (a b L : ℝ) : ℝ :=
  if a ^ 2 + b ^ 2 = 0 then L
  else 2 * (a * sin (a * L / 2) * cosh (b * L / 2) + b * cos (a * L / 2) * sinh (b * L / 2)) / (a ^ 2 + b ^ 2)

/-- `(a² + b²) ∫ sin(at) sinh(bt) = 2(b sin(aL/2) cosh(bL/2) − a cos(aL/2) sinh(bL/2))`. -/
theorem normSq_mul_sinSinhInt (a b L : ℝ) :
    (a ^ 2 + b ^ 2) * sinSinhInt a b L
      = 2 * (b * sin (a * L / 2) * cosh (b * L / 2) - a * cos (a * L / 2) * sinh (b * L / 2)) := by
  have h := Cvs.StepA.SectorGramBoxTransform.normSq_mul_integral_sin_sinh L ⟨a / 2, b / 2⟩
  dsimp only at h
  have e : ∀ t : ℝ, sin (2 * (a / 2) * t) * sinh (2 * (b / 2) * t) = sin (a * t) * sinh (b * t) := fun t => by
    rw [show 2 * (a / 2) * t = a * t by ring, show 2 * (b / 2) * t = b * t by ring]
  simp only [e] at h
  rw [show a * L / 2 = a / 2 * L by ring, show b * L / 2 = b / 2 * L by ring]
  unfold sinSinhInt
  linear_combination 4 * h

/-- `(a² + b²) ∫ cos(at) cosh(bt) = 2(a sin(aL/2) cosh(bL/2) + b cos(aL/2) sinh(bL/2))`. -/
theorem normSq_mul_cosCoshInt (a b L : ℝ) :
    (a ^ 2 + b ^ 2) * cosCoshInt a b L
      = 2 * (a * sin (a * L / 2) * cosh (b * L / 2) + b * cos (a * L / 2) * sinh (b * L / 2)) := by
  have h := Cvs.StepA.SectorGramBoxTransform.normSq_mul_integral_cos_cosh L ⟨a / 2, b / 2⟩
  dsimp only at h
  have e : ∀ t : ℝ, cos (2 * (a / 2) * t) * cosh (2 * (b / 2) * t) = cos (a * t) * cosh (b * t) := fun t => by
    rw [show 2 * (a / 2) * t = a * t by ring, show 2 * (b / 2) * t = b * t by ring]
  simp only [e] at h
  rw [show a * L / 2 = a / 2 * L by ring, show b * L / 2 = b / 2 * L by ring]
  unfold cosCoshInt
  linear_combination 4 * h

/-- **`∫ sin(at) sinh(bt)` in closed form**, for all `a, b, L`. -/
theorem sinSinhInt_eq (a b L : ℝ) : sinSinhInt a b L = sinSinhC a b L := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    subst ha hb
    simp [sinSinhInt, sinSinhC]
  · rw [sinSinhC, eq_div_iff h, mul_comm]
    exact normSq_mul_sinSinhInt a b L

/-- **`∫ cos(at) cosh(bt)` in closed form**, for all `a, b, L`. -/
theorem cosCoshInt_eq (a b L : ℝ) : cosCoshInt a b L = cosCoshC a b L := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    subst ha hb
    simp [cosCoshInt, cosCoshC]
  · rw [cosCoshC, if_neg h, eq_div_iff h, mul_comm]
    exact normSq_mul_cosCoshInt a b L

/-- **Size of the closed form**: `(a² + b²) sinSinhC(a, b, L)² ≤ 4 cosh²(bL/2)`. -/
theorem normSq_mul_sinSinhC_sq_le (a b L : ℝ) :
    (a ^ 2 + b ^ 2) * sinSinhC a b L ^ 2 ≤ 4 * cosh (b * L / 2) ^ 2 := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · rw [h, zero_mul]; positivity
  have hpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  set s := sin (a * L / 2) with hs
  set c := cos (a * L / 2) with hc
  set C := cosh (b * L / 2) with hC
  set S := sinh (b * L / 2) with hS
  have hsc : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
  have hCS : C ^ 2 = S ^ 2 + 1 := Real.cosh_sq _
  have hN : (b * s * C - a * c * S) ^ 2 ≤ (a ^ 2 + b ^ 2) * C ^ 2 := by
    have h1 : (b * s * C - a * c * S) ^ 2 ≤ (a ^ 2 + b ^ 2) * ((s * C) ^ 2 + (c * S) ^ 2) := by
      nlinarith [sq_nonneg (a * s * C + b * c * S)]
    have h2 : (s * C) ^ 2 + (c * S) ^ 2 ≤ C ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg s]
    nlinarith [mul_le_mul_of_nonneg_left h2 hpos.le]
  have e : (a ^ 2 + b ^ 2) * sinSinhC a b L ^ 2 = 4 * (b * s * C - a * c * S) ^ 2 / (a ^ 2 + b ^ 2) := by
    rw [sinSinhC, ← hs, ← hc, ← hC, ← hS]; field_simp; ring
  rw [e, div_le_iff₀ hpos]
  nlinarith [hN]

/-! ### Pairings of the pairing vector with the `ue` and pairing vectors -/

/-- `ve_z ue_{z'} = ¼ Σ sin((γ ± γ')t) sinh((y ± y')t)`, with `z = γ + iy`, `z' = γ' + iy'`. -/
theorem ve_mul_ue (z z' : ℂ) (t : ℝ) :
    ve z t * ue z' t = (1 / 4) * (sin ((z.re + z'.re) * t) * sinh ((z.im + z'.im) * t)
      + sin ((z.re + z'.re) * t) * sinh ((z.im - z'.im) * t)
      + sin ((z.re - z'.re) * t) * sinh ((z.im + z'.im) * t)
      + sin ((z.re - z'.re) * t) * sinh ((z.im - z'.im) * t)) := by
  simp only [ve, ue, add_mul, sub_mul, Real.sin_add, Real.sin_sub, Real.sinh_add, Real.sinh_sub]
  ring

/-- The closed form of `⟪V_z, U_{z'}⟫` at `L`: `¼ Σ sinSinhC(γ ± γ', y ± y', L)`. -/
def pairUe (L : ℝ) (z z' : ℂ) : ℝ :=
  (1 / 4) * (sinSinhC (z.re + z'.re) (z.im + z'.im) L + sinSinhC (z.re + z'.re) (z.im - z'.im) L
    + sinSinhC (z.re - z'.re) (z.im + z'.im) L + sinSinhC (z.re - z'.re) (z.im - z'.im) L)

/-- `∫ ve_z ue_{z'}` over the centred window is `pairUe`. -/
theorem integral_ve_mul_ue (L : ℝ) (z z' : ℂ) :
    ∫ t in -(L / 2)..L / 2, ve z t * ue z' t = pairUe L z z' := by
  simp_rw [ve_mul_ue]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [pairUe, ← sinSinhInt_eq, sinSinhInt]

/-- **`⟪V_z, U_{z'}⟫` in closed form**: `⟪pairVec z, ueVec z'⟫ = pairUe(log x, z, z')`. -/
theorem inner_pairVec_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z z' : ℂ) :
    ⟪Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z, ueVec hx0 z'⟫_ℝ = pairUe (Real.log x) z z' := by
  rw [Cvs.Route.Visibility.VisibilityClosingStep.inner_ueVec hx0 z' _ (Cvs.Route.Visibility.ZeroPairingVector.coe_pairVec_ae hx0 z), ← integral_ve_mul_ue]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(Set.countable_singleton (Real.log x / 2)).ae_notMem volume] with t ht hmem
  have ht : t ≠ Real.log x / 2 := ht
  rw [Set.uIoc_of_le (by linarith [Real.log_natCast_nonneg x])] at hmem
  have hm : t + Real.log x / 2 ∈ Set.Ico 0 (Real.log x) :=
    ⟨by linarith [hmem.1], by linarith [lt_of_le_of_ne hmem.2 ht]⟩
  rw [Set.indicator_of_mem hm, Cvs.Route.Visibility.ZeroPairingVector.pairProf, add_sub_cancel_right]

/-! ### Ties at the same distance from the line -/

/-! ### The closing step with the tie term made explicit -/

end Cvs.StepA.Edge.FiniteTopTieTerm

end
