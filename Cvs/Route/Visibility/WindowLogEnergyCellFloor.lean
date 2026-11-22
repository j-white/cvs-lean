import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.LogTailRateCellFloor
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.Route.Visibility.WindowTransformPlancherel
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window log energy from a cell floor and a per-rung window log-tail law

On `R₁`, `b ↦ F_{r_b}(σ + i·)·√(log⁺(|·|/T₀))` is linear into `L²(ℝ; ℂ)` with squared norm the window log tail, so a
cell floor `δ` bounds it by `(Σ_j ν_j/√δ_j)·‖r_b‖` (Cvs.Upstream.CoefficientFloorLinearBound). The split `log(|g| + 7/2) ≤ log(T₀ + 7/2) + log⁺(|g|/T₀)`
with `WindowTransformPlancherel`'s window Plancherel bound and a per-rung law `log tail_{r_j}(σ) ≤ P(x)·x^{|σ|}·x⁻¹·(1 − λ_{4j})^{1/2+η}`
at `T₀ = 8πx`, fed through `CaseFiniteFromWindowChain`'s tunnelling floor sum, give `Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg 0`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Route.L1FloorFromBulkD0 (Dom rung)
open Cvs.Route.Visibility.WindowLaplaceUPairing (prof winLaplace)
open Cvs.Route.Visibility.MOnePrimeTopDepth (winLogEnergy WinLogReg)
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (IsCellFloor FloorSumRate)
open Cvs.Route.Visibility.CaseFiniteFromWindowChain (sigmaFloor)

namespace Cvs.Route.Visibility.WindowLogEnergyCellFloor
open Cvs.ZeroCounting

/-! ### Linearity of the window transform -/

/-- The window integrand `t ↦ u(t + L/2) e^{wt}` is interval integrable. -/
theorem intervalIntegrable_integrand {x : ℕ} (u : Dom x) (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ((prof u (t + Real.log x / 2) : ℝ) : ℂ) * Complex.exp (w * t)) volume a b := by
  have h1 : IntervalIntegrable (fun t : ℝ => ((prof u (t + Real.log x / 2) : ℝ) : ℂ)) volume a b :=
    ⟨(Cvs.Route.Visibility.WindowLaplaceUPairing.intervalIntegrable_prof u _ _).1.ofReal, (Cvs.Route.Visibility.WindowLaplaceUPairing.intervalIntegrable_prof u _ _).2.ofReal⟩
  exact h1.mul_continuousOn (by fun_prop)

/-- The shifted profile of a combination is a.e. the combination of the shifted profiles. -/
theorem prof_shift_ae {x : ℕ} (c : ℝ) (u v : Dom x) :
    (fun t => prof (c • u + v) (t + Real.log x / 2))
      =ᵐ[volume] fun t => c * prof u (t + Real.log x / 2) + prof v (t + Real.log x / 2) := by
  have h : prof (c • u + v) =ᵐ[volume] fun s => c * prof u s + prof v s := by
    filter_upwards [Lp.coeFn_add (c • u.1.1) v.1.1, Lp.coeFn_smul c u.1.1] with s h1 h2
    show ((c • u.1.1 + v.1.1 : Lp ℝ 2 volume) : ℝ → ℝ) s = _
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
    rfl
  have h2 := (measurePreserving_add_right volume (Real.log x / 2)).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h2] with t ht
  exact ht

/-- **The window transform is linear in `u`**: `F_{cu + v} = c F_u + F_v`. -/
theorem winLaplace_smul_add {x : ℕ} (c : ℝ) (u v : Dom x) (w : ℂ) :
    winLaplace (c • u + v) w = c * winLaplace u w + winLaplace v w := by
  unfold winLaplace
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((intervalIntegrable_integrand u w _ _).const_mul _)
      (intervalIntegrable_integrand v w _ _)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [prof_shift_ae c u v] with t ht _
  rw [ht]
  push_cast
  ring

/-- The window transform at `w` as a linear functional on the form domain. -/
def winL (x : ℕ) (w : ℂ) : Dom x →ₗ[ℝ] ℂ where
  toFun u := winLaplace u w
  map_add' u v := by
    have h := winLaplace_smul_add 1 u v w
    rwa [one_smul, Complex.ofReal_one, one_mul] at h
  map_smul' c u := by
    have h := winLaplace_smul_add c u 0 w
    have h0 : winLaplace (0 : Dom x) w = 0 := by
      have h2 := winLaplace_smul_add 1 (0 : Dom x) 0 w
      rw [smul_zero, add_zero, Complex.ofReal_one, one_mul] at h2
      linear_combination -h2
    rw [add_zero, h0, add_zero] at h
    rw [h, RingHom.id_apply, Complex.real_smul]

/-- The even part of the spine class as a linear map of the coefficients. -/
def rMap (x : ℕ) : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] Dom x :=
  (Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x)

/-- **The window transform on `R₁` is the coefficient combination of the rung transforms**. -/
theorem winLaplace_rMap {x : ℕ} (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (w : ℂ) :
    winLaplace (rMap x b) w = ∑ j, b j • winLaplace (rung x j) w := by
  conv_lhs => rw [← Cvs.Approximant.SpineCoefficientMatrix.sum_single x b]
  rw [map_sum]
  change winL x w (∑ j, rMap x (b j • Pi.single j 1)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  rfl

/-! ### The window log-tail map -/

/-- **The window log tail** `∫ ‖F_u(σ + ig)‖² log⁺(|g|/T₀) dg`. -/
def winTail {x : ℕ} (u : Dom x) (σ T₀ : ℝ) : ℝ :=
  ∫ g : ℝ, ‖winLaplace u (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0

/-- The weighted window line function `g ↦ F_{r_b}(σ + ig)·√(log⁺(|g|/T₀))`. -/
def wtFun (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (g : ℝ) : ℂ :=
  winLaplace (rMap x b) (σ + g * I) * (√(max (Real.log (|g| / T₀)) 0) : ℂ)

theorem norm_sq_wtFun (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (g : ℝ) :
    ‖wtFun x σ T₀ b g‖ ^ 2 = ‖winLaplace (rMap x b) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0 := by
  rw [wtFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), mul_pow,
    sq_sqrt (le_max_right _ _)]

/-- The rung transforms are the unit-coefficient transforms. -/
theorem rMap_single (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : rMap x (Pi.single j 1) = rung x j := rfl

/-- The weighted window line function is the coefficient combination of the unit ones. -/
theorem wtFun_eq_sum {x : ℕ} (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (g : ℝ) :
    wtFun x σ T₀ b g = ∑ j, b j • wtFun x σ T₀ (Pi.single j 1) g := by
  unfold wtFun
  rw [winLaplace_rMap, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rMap_single, Complex.real_smul, Complex.real_smul]
  ring

/-- The line `g ↦ F_u(σ + ig)` is continuous. -/
theorem continuous_winLaplace_line {x : ℕ} (u : Dom x) (σ : ℝ) :
    Continuous fun g : ℝ => winLaplace u (σ + g * I) :=
  (Cvs.Route.Visibility.WindowLaplaceUPairing.differentiable_winLaplace u).continuous.comp (by fun_prop)

/-- The weighted window line function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_wtFun (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    AEStronglyMeasurable (wtFun x σ T₀ b) volume := by
  have hm : Measurable fun g : ℝ => ((√(max (Real.log (|g| / T₀)) 0) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      ((Real.measurable_log.comp (measurable_abs.div_const T₀)).max measurable_const).sqrt
  exact (continuous_winLaplace_line _ σ).aestronglyMeasurable.mul hm.aestronglyMeasurable

/-- An integrable window log tail makes the weighted line function square integrable. -/
theorem memLp_wtFun (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    (hb : Integrable fun g : ℝ => ‖winLaplace (rMap x b) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0) :
    MemLp (wtFun x σ T₀ b) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_wtFun x σ T₀ b)]
  simpa only [norm_sq_wtFun] using hb

/-- The window log-tail map of the coefficients into `L²(ℝ; ℂ)`, from integrable unit window log tails. -/
def wtMap (x : ℕ) (σ T₀ : ℝ)
    (h : ∀ j : Cvs.Approximant.SpineSubspace.SF x, Integrable fun g : ℝ =>
      ‖winLaplace (rung x j) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0) :
    (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  Fintype.linearCombination ℝ fun j => (memLp_wtFun x σ T₀ _ (h j)).toLp (wtFun x σ T₀ (Pi.single j 1))

/-- **The window log-tail map is the weighted line function**: its value at `b` is a.e. `wtFun b`, so the window
log tail of `r_b` is integrable and equals `‖wtMap b‖²`. -/
theorem wtMap_spec (x : ℕ) (σ T₀ : ℝ)
    (h : ∀ j : Cvs.Approximant.SpineSubspace.SF x, Integrable fun g : ℝ =>
      ‖winLaplace (rung x j) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    (Integrable fun g : ℝ => ‖winLaplace (rMap x b) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0)
      ∧ ‖wtMap x σ T₀ h b‖ ^ 2 = winTail (rMap x b) σ T₀ := by
  have hae : ⇑(wtMap x σ T₀ h b) =ᵐ[volume] wtFun x σ T₀ b := by
    rw [wtMap, Fintype.linearCombination_apply]
    filter_upwards [Cvs.Route.Visibility.LogTailRateCellFloor.coeFn_sum_smul_toLp _ (fun j => memLp_wtFun x σ T₀ _ (h j)) b] with g hg
    rw [hg, wtFun_eq_sum]
  have hL : MemLp (wtFun x σ T₀ b) 2 volume := (Lp.memLp (wtMap x σ T₀ h b)).ae_eq hae
  refine ⟨?_, ?_⟩
  · have := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).1 hL
    simpa only [norm_sq_wtFun] using this
  · rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral, winTail]
    refine integral_congr_ae ?_
    filter_upwards [hae] with g hg
    rw [hg, norm_sq_wtFun]

/-- **The window log tail under a cell floor**: integrable unit window log tails with `√(log tail_{r_j}) ≤ ν_j` give
`log tail_{r_b} ≤ (Σ_j ν_j/√δ_j)²·‖r_b‖²`, the window log tail of `r_b` being integrable. -/
theorem winTail_le_floorSum {x : ℕ} (hx : 80 ≤ 2 * π * x) (σ T₀ : ℝ) {δ ν : Cvs.Approximant.SpineSubspace.SF x → ℝ} (hδ : IsCellFloor x δ)
    (h : ∀ j : Cvs.Approximant.SpineSubspace.SF x, Integrable fun g : ℝ =>
      ‖winLaplace (rung x j) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0)
    (hν : ∀ j, √(winTail (rung x j) σ T₀) ≤ ν j) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    (Integrable fun g : ℝ => ‖winLaplace (rMap x b) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0)
      ∧ winTail (rMap x b) σ T₀ ≤ (∑ j, ν j / √(δ j)) ^ 2 * ‖rMap x b‖ ^ 2 := by
  obtain ⟨hI, hn⟩ := wtMap_spec x σ T₀ h b
  refine ⟨hI, ?_⟩
  have h1 := Cvs.Upstream.CoefficientFloorLinearBound.norm_le_of_cell_floor hx (wtMap x σ T₀ h) δ hδ.1 hδ.2 b
  have hj : ∀ j, ‖wtMap x σ T₀ h (Pi.single j 1)‖ ≤ ν j := fun j => by
    rw [← Real.sqrt_sq (norm_nonneg _), (wtMap_spec x σ T₀ h _).2]; exact hν j
  have h2 : ‖wtMap x σ T₀ h b‖ ≤ (∑ j, ν j / √(δ j)) * ‖rMap x b‖ :=
    h1.trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ =>
      div_le_div_of_nonneg_right (hj j) (sqrt_nonneg _)) (norm_nonneg _))
  rw [← hn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-! ### The window log energy -/

/-- **The window log energy from the weight split**: for `T₀ > 0`, an integrable window log tail gives an
integrable log-weighted line energy with `∫ ‖F_u‖² log(|g| + 7/2) ≤ 2π log(T₀ + 7/2)·x^{|σ|}‖u‖² + log tail`. -/
theorem winLogEnergy_le_split {x : ℕ} (hx : 0 < x) (u : Dom x) (σ : ℝ) {T₀ : ℝ} (hT : 0 < T₀)
    (hI : Integrable fun g : ℝ => ‖winLaplace u (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0) :
    (Integrable fun g : ℝ => ‖winLaplace u (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2))
      ∧ winLogEnergy u σ ≤ 2 * π * Real.log (T₀ + 7 / 2) * (x : ℝ) ^ |σ| * ‖u‖ ^ 2 + winTail u σ T₀ := by
  obtain ⟨hP, hPle⟩ := Cvs.Route.Visibility.WindowTransformPlancherel.integral_norm_sq_winLaplace_le hx u σ
  have hR : Integrable fun g : ℝ => Real.log (T₀ + 7 / 2) * ‖winLaplace u (σ + g * I)‖ ^ 2
      + ‖winLaplace u (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0 := (hP.const_mul _).add hI
  have hpt : ∀ g : ℝ, ‖winLaplace u (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2)
      ≤ Real.log (T₀ + 7 / 2) * ‖winLaplace u (σ + g * I)‖ ^ 2
        + ‖winLaplace u (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0 := fun g => by
    have h := Cvs.Route.Visibility.CaseFiniteCellFloorRates.log_add_le_split hT (abs_nonneg g)
    have h0 : 0 ≤ ‖winLaplace u (σ + g * I)‖ ^ 2 := sq_nonneg _
    nlinarith
  have hm : AEStronglyMeasurable (fun g : ℝ => ‖winLaplace u (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2))
      volume :=
    (((continuous_winLaplace_line u σ).norm.pow 2).mul
      (Continuous.log (by fun_prop) fun g => by positivity)).aestronglyMeasurable
  have hL : Integrable fun g : ℝ => ‖winLaplace u (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2) := by
    refine hR.mono' hm (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by
      linarith [abs_nonneg g])))]
    exact hpt g
  refine ⟨hL, ?_⟩
  calc winLogEnergy u σ ≤ ∫ g : ℝ, (Real.log (T₀ + 7 / 2) * ‖winLaplace u (σ + g * I)‖ ^ 2
        + ‖winLaplace u (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0) := integral_mono hL hR hpt
    _ = Real.log (T₀ + 7 / 2) * (∫ g : ℝ, ‖winLaplace u (σ + g * I)‖ ^ 2) + winTail u σ T₀ := by
        rw [integral_add (hP.const_mul _) hI, integral_const_mul]; rfl
    _ ≤ Real.log (T₀ + 7 / 2) * (2 * π * (x : ℝ) ^ |σ| * ‖u‖ ^ 2) + winTail u σ T₀ := by
        gcongr
        exact Real.log_nonneg (by linarith)
    _ = _ := by ring

/-! ### The per-rung law and `WinLogReg 0` -/

/-- **The per-rung window log-tail law at exponent `½ + η`**: some subpolynomial `P` has, at all large `x`, for
`|σ| ≤ 1` and on every rung, an integrable window log tail at `T₀ = 8πx` with
`log tail_{r_j}(σ) ≤ P(x)·x^{|σ|}·x⁻¹·(1 − λ_{4j})^{1/2+η}`. -/
def WinTailProfile (η : ℝ) : Prop :=
  ∃ P : ℕ → ℝ, SubPoly P ∧ ∀ᶠ x : ℕ in atTop, ∀ σ : ℝ, |σ| ≤ 1 → ∀ j : Cvs.Approximant.SpineSubspace.SF x,
    (Integrable fun g : ℝ => ‖winLaplace (rung x j) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / (8 * π * x))) 0)
      ∧ winTail (rung x j) σ (8 * π * x)
          ≤ P x * (x : ℝ) ^ |σ| * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η)

/-- **The window log regularity from the window chain's cell floor, the tunnelling floor sum and the per-rung
window law**: for `η₀ < 1`, an eventual cell floor `cellFloor η₀`, `ExtTunnelSum η` and `WinTailProfile η` give
`WinLogReg 0`. -/
theorem winLogReg_of_profile {η η₀ : ℝ} (hη₀ : η₀ < 1)
    (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀)) (hT : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η)
    (hP : WinTailProfile η) : WinLogReg 0 := by
  obtain ⟨P, hP, hb⟩ := hP
  set ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ :=
    fun x j => √(max (P x) 0 * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
  have hν0 : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j := Eventually.of_forall fun _ _ => sqrt_nonneg _
  have hs : FloorSumRate (fun x => Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) ν 0 :=
    Cvs.Route.Visibility.CaseFiniteFromWindowChain.floorSumRate_cellFloor hη₀ hν0 (Cvs.Route.Visibility.LogTailRateCellFloor.floorSumRate_profile hT hP)
  have h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ ∑ j, ν x j / √(Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀ j) :=
    Eventually.of_forall fun x => Finset.sum_nonneg fun j _ => div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  set S : ℕ → ℝ := fun x => ∑ j, ν x j / √(Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀ j)
  have hS : SubPoly fun x => S x ^ 2 := by
    have := Cvs.Route.Visibility.CaseFiniteCellFloorRates.subPoly_sq_of_floorSumRate hs h0
    simpa only [mul_zero, neg_zero, Real.rpow_zero, mul_one] using this
  have hL : SubPoly fun x : ℕ => 2 * π * Real.log (8 * π * x + 7 / 2) :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (2 * π)).mul Cvs.Route.Visibility.CaseFiniteCellFloorRates.subPoly_log_eight_pi (Eventually.of_forall fun _ => by positivity)
      (by filter_upwards [eventually_ge_atTop 1] with x hx
          exact Real.log_nonneg (by
            have : (1 : ℝ) ≤ x := by exact_mod_cast hx
            nlinarith [Real.pi_pos]))
  refine ⟨fun x => 2 * π * Real.log (8 * π * x + 7 / 2) + S x ^ 2, hL.add hS, ?_⟩
  filter_upwards [hδ, hb, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hδx hbx hsc r hr σ hσ
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc
  have hxn : 0 < x := by exact_mod_cast hx0
  have hT0 : (0 : ℝ) < 8 * π * x := by positivity
  obtain ⟨b, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  have hpx : 0 ≤ (x : ℝ) ^ |σ| := Real.rpow_nonneg hx0.le _
  have hlam : ∀ j : Cvs.Approximant.SpineSubspace.SF x, 0 ≤ (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η) := fun j => by
    have hc0 : (0 : ℝ) < 2 * π * x := by positivity
    have := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 (Cvs.L2a.FullSpanIndexFloor.full_index x hsc (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)).1
    exact Real.rpow_nonneg (by linarith) _
  have hν : ∀ j, √(winTail (rung x j) σ (8 * π * x)) ≤ √((x : ℝ) ^ |σ|) * ν x j := fun j => by
    rw [← Real.sqrt_mul hpx]
    refine sqrt_le_sqrt ((hbx σ hσ j).2.trans ?_)
    have hx1 : (0 : ℝ) ≤ 1 / x := by positivity
    calc P x * (x : ℝ) ^ |σ| * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η)
        ≤ max (P x) 0 * (x : ℝ) ^ |σ| * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η) := by
          gcongr
          · exact hlam j
          · exact le_max_left _ _
      _ = _ := by ring
  have hW := winTail_le_floorSum hsc σ (8 * π * x) hδx (fun j => (hbx σ hσ j).1) hν b
  obtain ⟨hI, hE⟩ := winLogEnergy_le_split hxn (rMap x b) σ hT0 hW.1
  refine ⟨hI, hE.trans ?_⟩
  have hsum : ∑ j, √((x : ℝ) ^ |σ|) * ν x j / √(Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀ j) = √((x : ℝ) ^ |σ|) * S x := by
    simp only [S, Finset.mul_sum, mul_div_assoc]
  rw [hsum, mul_pow, Real.sq_sqrt hpx] at hW
  have := hW.2
  calc 2 * π * Real.log (8 * π * x + 7 / 2) * (x : ℝ) ^ |σ| * ‖rMap x b‖ ^ 2 + winTail (rMap x b) σ (8 * π * x)
      ≤ 2 * π * Real.log (8 * π * x + 7 / 2) * (x : ℝ) ^ |σ| * ‖rMap x b‖ ^ 2
        + (x : ℝ) ^ |σ| * S x ^ 2 * ‖rMap x b‖ ^ 2 := by linarith
    _ = (2 * π * Real.log (8 * π * x + 7 / 2) + S x ^ 2) * (x : ℝ) ^ (|σ| + 0) * ‖rMap x b‖ ^ 2 := by
        rw [add_zero]; ring

end Cvs.Route.Visibility.WindowLogEnergyCellFloor

end
