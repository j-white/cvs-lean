import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.EvenBulkModeMatrices
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.L2a.FirstRungWindowFormUpper
import Cvs.L2a.TailLogScaleTest
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.Route.EvenBulkFloorSandwich
import Cvs.Route.EvenHyperplaneFloorCompress
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.TameCouplingBulkFloor
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes' vector is the first rung row

At `80 ≤ 2πx` Connes' test is the spine test of rung `1`, so its cosine coefficients are `(log x)⁻¹` times the
normal coefficients of the even rung `1`: `connesCoef x N = (log x)⁻¹ • normalCoeff(rung₁)`. Hence the even
rung vector `rungVec x N j₁` is `log x • connesCoef x N`, and Connes' unit vector is `rungVec j₁ / ‖rungVec j₁‖`,
an element of `Cvs.Route.EvenBulkFloorSandwich.R1N x N`, whenever the coefficient vector is nonzero.
-/

noncomputable section

open Real MeasureTheory Set Matrix Filter
open scoped InnerProductSpace

namespace Cvs.Approximant.ConnesVectorFirstRung
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive)

/-- At integer `x`, the spine test of the coordinate vector at rung `1` is Connes' test. -/
theorem kG_single_one {x : ℕ} (j1 : Cvs.Approximant.SpineSubspace.SF x) (hj1 : (j1 : ℕ) = 1) :
    Cvs.Approximant.SpineSubspace.kG x (Pi.single j1 (1 : ℝ)) = Cvs.Approximant.ConnesVectorRealScale.connesK x := by
  have h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x := hj1 ▸ j1.2
  obtain rfl : j1 = ⟨1, h1⟩ := Subtype.ext hj1
  rw [Cvs.Approximant.ConnesVectorRealScale.connesK_natCast]
  funext s
  unfold Cvs.Approximant.SpineSubspace.kG
  rw [Cvs.L2a.FirstRungWindowFormUpper.spineG_single_one]
  rfl

/-- The cut cosine sum of a coordinate vector is the indicator of `(0, L]` times one cosine. -/
theorem modeSum_single (L : ℝ) (N : ℕ) (i : Idx N) (s : ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (Pi.single i 1) s
      = (Ioc (0 : ℝ) L).indicator (fun s => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i * s)) s := by
  unfold Cvs.Finite.TruncationZeroFreeOffAxes.modeSum
  by_cases hs : s ∈ Ioc (0 : ℝ) L
  · rw [if_pos hs, indicator_of_mem hs, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hs, indicator_of_notMem hs]

/-- **Connes' coefficients as pairings**: `connesCoef x N i = (log x)⁻¹ ∫ k_x · modeSum(eᵢ)` for `1 < x`. -/
theorem connesCoef_eq_integral {x : ℝ} (hx : 1 < x) (N : ℕ) (i : Idx N) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N i = (Real.log x)⁻¹ *
      ∫ s, Cvs.Approximant.ConnesVectorRealScale.connesK x s * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) (Pi.single i 1) s := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hint : (∫ s, Cvs.Approximant.ConnesVectorRealScale.connesK x s * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) (Pi.single i 1) s)
      = ∫ s in (0 : ℝ)..Real.log x,
          Cvs.Approximant.ConnesVectorRealScale.connesK x s * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (Real.log x) (mode N) i * s) := by
    rw [intervalIntegral.integral_of_le hL.le, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext s
    rw [modeSum_single]
    by_cases hs : s ∈ Ioc (0 : ℝ) (Real.log x)
    · rw [indicator_of_mem hs, indicator_of_mem hs]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, mul_zero]
  rw [hint]
  rcases i with _ | ⟨k, b⟩
  · simp only [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Finset.mem_range, Nat.zero_lt_succ, if_true,
      Cvs.Finite.WindowCosineBessel.coef, Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode, Int.cast_zero, mul_zero, zero_div, zero_mul,
      Real.cos_zero, mul_one]
    rw [one_div]
  · have hk : (k : ℕ) + 1 ∈ Finset.range (N + 1) :=
      Finset.mem_range.2 (Nat.succ_lt_succ k.isLt)
    have hcos : ∀ s, Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (Real.log x) (mode N) (some (k, b)) * s)
        = Real.cos (2 * π * (((k : ℕ) + 1 : ℕ) : ℝ) / Real.log x * s) := by
      intro s
      simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode]
      cases b
      · simp only [Bool.false_eq_true, if_false]
        rw [← Real.cos_neg]
        congr 1
        push_cast
        ring
      · simp only [if_true]
        push_cast
        ring_nf
    simp only [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, hk, if_true, Cvs.Finite.WindowCosineBessel.coef, Nat.add_one_ne_zero,
      if_false]
    simp_rw [hcos]
    field_simp

/-- **The rung-1 normal is `log x` times Connes' coefficients**: `connesCoef x N = (log x)⁻¹ • normalCoeff(rung₁)`. -/
theorem connesCoef_eq_normalCoeff_rung {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
      = (Real.log x)⁻¹ • Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (Cvs.Route.L1FloorFromBulkD0.rung x j1) (mode N) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, Cvs.Finite.EvenBulkModeMatrices.normalCoeff_rung_eq_integral hx N j1 i, kG_single_one j1 hj1,
    connesCoef_eq_integral (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)]

/-- The rung-1 normal coefficients form an even vector. -/
theorem normalCoeff_rung_one_even {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) (i : Idx N) :
    Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (Cvs.Route.L1FloorFromBulkD0.rung x j1) (mode N) (negI N i)
      = Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (Cvs.Route.L1FloorFromBulkD0.rung x j1) (mode N) i := by
  have hL : Real.log x ≠ 0 := (Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)).ne'
  have h := congrFun (connesCoef_eq_normalCoeff_rung hx N j1 hj1)
  have e := Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N i
  rw [h, h] at e
  simp only [Pi.smul_apply, smul_eq_mul] at e
  exact mul_left_cancel₀ (inv_ne_zero hL) e

/-- **The even rung-1 vector is `log x` times Connes' coefficient vector.** -/
theorem rungVec_eq_smul_connesCoef {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) :
    WithLp.ofLp ((Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1 : Cvs.Route.GroundRouteJointGap.evenSub N) : EuclideanSpace ℝ (Idx N))
      = Real.log x • Cvs.Approximant.ConnesVectorRealScale.connesCoef x N := by
  have hL : Real.log x ≠ 0 := (Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)).ne'
  funext i
  show Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) _ i = _
  rw [Cvs.Finite.TruncationQuadraticForm.evenPart, normalCoeff_rung_one_even hx N j1 hj1, connesCoef_eq_normalCoeff_rung hx N j1 hj1]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Connes' unit vector at integer `x` and truncation `N`, as an element of the even sector. -/
abbrev vhat (x N : ℕ) : Cvs.Route.GroundRouteJointGap.evenSub N := Cvs.Route.EigenvectorCoordinateCompression.evenVec (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) (x : ℝ))

/-- `v̂` is a unit vector. -/
theorem norm_vhat (x N : ℕ) : ‖vhat x N‖ = 1 :=
  Cvs.Route.EigenvectorCoordinateCompression.norm_evenVec _ (Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self _ _)

/-- `‖rungVec j₁‖ = log x · √(α⬝α)`, `α = connesCoef x N`. -/
theorem norm_rungVec_one {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) :
    ‖Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1‖
      = Real.log x * √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) := by
  have hL : 0 < Real.log x := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)
  have h2 : ‖Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1‖ ^ 2
      = (Real.log x) ^ 2 * (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) := by
    rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub, rungVec_eq_smul_connesCoef hx N j1 hj1, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hq : 0 ≤ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL.le]

/-- **Connes' vector is the normalised rung-1 vector** whenever its coefficient vector is nonzero. -/
theorem evenVec_connesVec_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    vhat x N = ‖Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1‖⁻¹ • Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1 := by
  have hL : 0 < Real.log x := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)
  have hq : 0 < √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm hs))
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  show Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) (x : ℝ) = _
  rw [Submodule.coe_smul, WithLp.ofLp_smul, rungVec_eq_smul_connesCoef hx N j1 hj1,
    norm_rungVec_one hx N j1 hj1, smul_smul]
  unfold Cvs.Approximant.ConnesVectorRealScale.connesVec
  simp only [if_neg hs]
  congr 1
  field_simp

/-- **Connes' vector lies in the rung span** `R₁(N)` whenever its coefficient vector is nonzero. -/
theorem evenVec_connesVec_mem_R1N {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    vhat x N ∈ Cvs.Route.EvenBulkFloorSandwich.R1N x N := by
  have h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x := Finset.mem_filter.2
    ⟨Finset.mem_range.2 (by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx), le_rfl⟩
  rw [evenVec_connesVec_eq hx N ⟨1, h1⟩ rfl hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

/-- At all large integer `x`, every truncation has a nonzero rung-1 vector. -/
theorem eventually_rungVec_one_ne_zero :
    ∀ᶠ x : ℕ in atTop, ∀ (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x), (j1 : ℕ) = 1 → Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1 ≠ 0 := by
  filter_upwards [Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_nat_connesCoef_mass_ne_zero, Cvs.Route.TameCouplingBulkFloor.eventually_scale] with x hs hx N j1 hj1 h0
  have hn := norm_rungVec_one hx N j1 hj1
  rw [h0, norm_zero] at hn
  have hL : 0 < Real.log x := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)
  have hq : 0 < √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm (hs N)))
  nlinarith

/-- At all large integer `x`, Connes' vector lies in `R₁(N)` at every truncation `N`. -/
theorem eventually_vhat_mem_R1N :
    ∀ᶠ x : ℕ in atTop, 80 ≤ 2 * π * x ∧ ∀ N : ℕ, vhat x N ∈ Cvs.Route.EvenBulkFloorSandwich.R1N x N := by
  filter_upwards [Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_nat_connesCoef_mass_ne_zero, Cvs.Route.TameCouplingBulkFloor.eventually_scale] with x hs hx
  exact ⟨hx, fun N => evenVec_connesVec_mem_R1N hx N (hs N)⟩

end Cvs.Approximant.ConnesVectorFirstRung
