import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.Envelope.RungEdgeMassExterior
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.ForbiddenZoneClosedForm
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorImageSawtoothPoisson
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.SawtoothPlancherelBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Duhamel remainder on `(1, ∞)` and the per-rung exterior law

For a rung, `v = ξψ` solves `v'' + c²v = F` with `F = −2v'/(ξ(ξ² − 1)) − (2/ξ² + (D − 2)/(ξ² − 1))v`, so an energy
cap bounds `∫₁^∞ ξ²ρ²` in closed form; with Cvs.Prolate.Envelope.RungEdgeMassExterior–Cvs.Route.Visibility.ExteriorImageSawtoothPoisson, Cvs.Prolate.PlungeLawIntegral and Cvs.Prolate.ForbiddenZoneClosedForm this bounds `Ext_{G_j}(σ)` for
`G_j = h_{4j} − α_j h_0` by `x^ε·a·(1 − λ_{4j})^{1−η}` for every `ε, η > 0`, eventually in `x`, on every rung.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity
open scoped ENNReal
open Cvs.Prolate.RungOrthogonalityAtInfinity (ampl cst₁ cstU)
open Cvs.Route.Visibility.ExteriorImageSawtoothPoisson (rhoG)

namespace Cvs.Prolate.Envelope.RungDuhamelRemainder
open Cvs.ZeroCounting

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-! ### The rotated pair -/

/-- `v' = ψ + ξu/(ξ² − 1)`, the derivative of `v = ξψ`. -/
def dv (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ := psi c g ξ + ξ * rungU c g ξ / pP ξ

/-- The forcing `F = −2v'/(ξ(ξ² − 1)) − (2/ξ² + (c² − χ − 2)/(ξ² − 1))ξψ`. -/
def forceF (c χ : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  -(2 * dv c g ξ / (ξ * pP ξ)) - (2 / ξ ^ 2 + (c ^ 2 - χ - 2) / pP ξ) * (ξ * psi c g ξ)

/-- `P = v' cos(cξ) + cξψ sin(cξ) − A`, the cosine coordinate of `R' + icR`. -/
def rotP (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  dv c g ξ * Real.cos (c * ξ) + c * ξ * psi c g ξ * Real.sin (c * ξ) - ampl g

/-- `Q = cξψ cos(cξ) − v' sin(cξ)`, the sine coordinate of `R' + icR`. -/
def rotQ (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  c * ξ * psi c g ξ * Real.cos (c * ξ) - dv c g ξ * Real.sin (c * ξ)

/-- `cR = P sin(cξ) + Q cos(cξ)`, `R = ξψ − (A/c)sin(cξ)`. -/
theorem rot_identity (hc : c ≠ 0) (ξ : ℝ) :
    c * (ξ * psi c g ξ - ampl g / c * Real.sin (c * ξ))
      = rotP c g ξ * Real.sin (c * ξ) + rotQ c g ξ * Real.cos (c * ξ) := by
  unfold rotP rotQ
  have h := Real.sin_sq_add_cos_sq (c * ξ)
  field_simp
  linear_combination (-(c * ξ * psi c g ξ)) * h

/-- **The rotated pair moves with the forcing**: on `ξ > 1`, `P' = F cos(cξ)` and `Q' = −F sin(cξ)`. -/
theorem hasDerivAt_rot
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (rotP c g) (forceF c χ g ξ * Real.cos (c * ξ)) ξ ∧
      HasDerivAt (rotQ c g) (-(forceF c χ g ξ * Real.sin (c * ξ))) ξ := by
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hp : pP ξ ≠ 0 := (pP_pos hξ).ne'
  have hξ0 : ξ ≠ 0 := by linarith
  have hpd : HasDerivAt pP (2 * ξ) ξ := by
    have := (hasDerivAt_pow 2 ξ).sub_const 1; unfold pP; simpa using this
  have hψd := hψ ξ hξ
  have hud := hu ξ
  have hdv : HasDerivAt (dv c g) (rungU c g ξ / pP ξ + (rungU c g ξ / pP ξ
      + ξ * ((-(qP c χ ξ * psi c g ξ)) * pP ξ - rungU c g ξ * (2 * ξ)) / pP ξ ^ 2)) ξ := by
    have h2 := ((hasDerivAt_id' ξ).fun_mul hud).fun_div hpd hp
    refine hψd.add (h2.congr_deriv ?_)
    field_simp
    ring
  have hcos : HasDerivAt (fun t => Real.cos (c * t)) (-(Real.sin (c * ξ) * c)) ξ := by
    have := ((hasDerivAt_id' ξ).const_mul c).cos; simpa [mul_comm] using this
  have hsin : HasDerivAt (fun t => Real.sin (c * t)) (Real.cos (c * ξ) * c) ξ := by
    have := ((hasDerivAt_id' ξ).const_mul c).sin; simpa [mul_comm] using this
  have hcξψ : HasDerivAt (fun t => c * t * psi c g t) (c * psi c g ξ + c * ξ * (rungU c g ξ / pP ξ)) ξ := by
    exact (((hasDerivAt_id' ξ).const_mul c).fun_mul hψd).congr_deriv (by ring)
  have hq : qP c χ ξ = c ^ 2 * pP ξ + (c ^ 2 - χ) := by unfold qP pP; ring
  constructor
  · have h := ((hdv.mul hcos).add (hcξψ.mul hsin)).sub_const (ampl g)
    refine h.congr_deriv ?_
    unfold forceF dv
    rw [hq]
    field_simp
    unfold pP
    ring
  · have h := (hcξψ.mul hcos).sub (hdv.mul hsin)
    refine h.congr_deriv ?_
    unfold forceF dv
    rw [hq]
    field_simp
    unfold pP
    ring

/-! ### The rotated pair vanishes at infinity -/

/-- `|y₁ + y₂ + y₃ + y₄ + y₅| ≤ Σ|yᵢ|`. -/
theorem abs_add5_le (y₁ y₂ y₃ y₄ y₅ : ℝ) : |y₁ + y₂ + y₃ + y₄ + y₅| ≤ |y₁| + |y₂| + |y₃| + |y₄| + |y₅| := by
  have h1 := abs_add_le (y₁ + y₂ + y₃ + y₄) y₅
  have h2 := abs_add_le (y₁ + y₂ + y₃) y₄
  have h3 := abs_add_le (y₁ + y₂) y₃
  have h4 := abs_add_le y₁ y₂
  linarith

set_option maxHeartbeats 1000000 in
/-- **The rotated pair is `O(1/ξ)`**: for `c > 0`, `0 ≤ χ < c²` and `ξ ≥ 2`, `|P|, |Q| ≤ K/ξ` with
`K = |A|/c + C₁/c² + |A| + 2Σ + C₁/c`. -/
theorem abs_rot_le (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) {ξ : ℝ} (hξ : 2 ≤ ξ) :
    |rotP c g ξ| ≤ (|ampl g| / c + cst₁ g₁ g₂ / c ^ 2 + |ampl g| + 2 * cstU c g g₁ g₂ + cst₁ g₁ g₂ / c) / ξ ∧
      |rotQ c g ξ| ≤ (|ampl g| / c + cst₁ g₁ g₂ / c ^ 2 + |ampl g| + 2 * cstU c g g₁ g₂ + cst₁ g₁ g₂ / c) / ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hξ1 : 1 ≤ ξ := by linarith
  have hcξ : 0 < c * ξ := by positivity
  set A := ampl g with hA
  set C₁ := cst₁ g₁ g₂ with hC₁
  set Sg := cstU c g g₁ g₂ with hSg
  set e₁ := psi c g ξ - A * Real.sin (c * ξ) / (c * ξ) with he₁
  set e₂ := rungU c g ξ - A * ξ * Real.cos (c * ξ) with he₂
  have h1 : |e₁| ≤ C₁ / (c * ξ) ^ 2 := Cvs.Prolate.CosineTransformSecondOrder.psi_sub_le hg hg₁ hg₂c hcξ.ne'
  have h2 : |e₂| ≤ Sg := by
    refine (Cvs.Prolate.CosineTransformSecondOrder.u_sub_le hg hg₁ hg₂c hc hξ1).trans ?_
    rw [hSg]; unfold cstU ampl
    gcongr
    exact div_le_self (abs_nonneg _) hξ1
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]; unfold cst₁
    exact add_nonneg (abs_nonneg _) (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _)
  have hSg0 : 0 ≤ Sg := (abs_nonneg _).trans h2
  have hp : pP ξ = ξ ^ 2 - 1 := rfl
  have hp0 : 0 < pP ξ := pP_pos (by linarith)
  have hpξ : ξ ≤ pP ξ := by rw [hp]; nlinarith
  have hpξ2 : ξ ^ 2 ≤ 2 * pP ξ := by rw [hp]; nlinarith
  set s := Real.sin (c * ξ)
  set co := Real.cos (c * ξ)
  have hs := Real.abs_sin_le_one (c * ξ)
  have hco := Real.abs_cos_le_one (c * ξ)
  have hsc := Real.sin_sq_add_cos_sq (c * ξ)
  have hψ : psi c g ξ = A * s / (c * ξ) + e₁ := by rw [he₁]; ring
  have hu : rungU c g ξ = A * ξ * co + e₂ := by rw [he₂]; ring
  -- the five pieces
  have b1 : |A * s * co / (c * ξ)| ≤ |A| / c / ξ := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hcξ, div_div]
    gcongr
    calc |A| * |s| * |co| ≤ |A| * 1 * 1 := by gcongr
      _ = |A| := by ring
  have b2 : |e₁| ≤ C₁ / c ^ 2 / ξ := by
    refine h1.trans ?_
    rw [mul_pow, div_div]
    gcongr
    nlinarith
  have b3 : A * co ^ 2 / pP ξ ≤ |A| / ξ ∧ -(|A| / ξ) ≤ A * co ^ 2 / pP ξ := by
    have hco2 : co ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have k : |A * co ^ 2 / pP ξ| ≤ |A| / ξ := by
      rw [abs_div, abs_mul, abs_of_pos hp0, abs_of_nonneg (sq_nonneg co)]
      calc |A| * co ^ 2 / pP ξ ≤ |A| * 1 / pP ξ := by gcongr
        _ ≤ |A| / ξ := by rw [mul_one]; exact div_le_div_of_nonneg_left (abs_nonneg _) hξ0 hpξ
    exact ⟨(le_abs_self _).trans k, by linarith [neg_abs_le (A * co ^ 2 / pP ξ)]⟩
  have b4 : |ξ * e₂ / pP ξ| ≤ 2 * Sg / ξ := by
    rw [abs_div, abs_mul, abs_of_pos hξ0, abs_of_pos hp0, div_le_div_iff₀ hp0 hξ0]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ξ), abs_nonneg e₂]
  have b5 : |c * ξ * e₁| ≤ C₁ / c / ξ := by
    rw [abs_mul, abs_of_pos hcξ]
    calc c * ξ * |e₁| ≤ c * ξ * (C₁ / (c * ξ) ^ 2) := mul_le_mul_of_nonneg_left h1 hcξ.le
      _ = C₁ / c / ξ := by field_simp
  have hdv : dv c g ξ = A * s / (c * ξ) + e₁ + A * co + A * co / pP ξ + ξ * e₂ / pP ξ := by
    unfold dv
    have hk2 : ξ * (A * ξ * co + e₂) / pP ξ = A * co + A * co / pP ξ + ξ * e₂ / pP ξ := by
      field_simp; rw [hp]; ring
    rw [hψ, hu, hk2]; ring
  have hk : c * ξ * (A * s / (c * ξ)) = A * s := mul_div_cancel₀ _ hcξ.ne'
  constructor
  · have eP : rotP c g ξ = A * s * co / (c * ξ) + e₁ * co + A * co ^ 2 / pP ξ + ξ * e₂ / pP ξ * co
        + c * ξ * e₁ * s := by
      unfold rotP; rw [hdv, hψ]; linear_combination s * hk + A * hsc
    rw [eP]
    refine (abs_add5_le _ _ _ _ _).trans ?_
    have k2 : |e₁ * co| ≤ C₁ / c ^ 2 / ξ := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hco).trans b2
    have k3 : |A * co ^ 2 / pP ξ| ≤ |A| / ξ := abs_le.mpr ⟨b3.2, b3.1⟩
    have k4 : |ξ * e₂ / pP ξ * co| ≤ 2 * Sg / ξ := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hco).trans b4
    have k5 : |c * ξ * e₁ * s| ≤ C₁ / c / ξ := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans b5
    have e : (|A| / c + C₁ / c ^ 2 + |A| + 2 * Sg + C₁ / c) / ξ
        = |A| / c / ξ + C₁ / c ^ 2 / ξ + |A| / ξ + 2 * Sg / ξ + C₁ / c / ξ := by ring
    rw [e]; linarith
  · have eQ : rotQ c g ξ = c * ξ * e₁ * co - A * s ^ 2 / (c * ξ) - e₁ * s - A * co * s / pP ξ
        - ξ * e₂ / pP ξ * s := by
      unfold rotQ; rw [hdv, hψ]; linear_combination co * hk
    rw [eQ]
    have e5 : c * ξ * e₁ * co - A * s ^ 2 / (c * ξ) - e₁ * s - A * co * s / pP ξ - ξ * e₂ / pP ξ * s
        = c * ξ * e₁ * co + (-(A * s ^ 2 / (c * ξ))) + (-(e₁ * s)) + (-(A * co * s / pP ξ))
          + (-(ξ * e₂ / pP ξ * s)) := by ring
    rw [e5]
    refine (abs_add5_le _ _ _ _ _).trans ?_
    simp only [abs_neg]
    have k1 : |c * ξ * e₁ * co| ≤ C₁ / c / ξ := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hco).trans b5
    have k2 : |A * s ^ 2 / (c * ξ)| ≤ |A| / c / ξ := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg co]
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), abs_of_pos hcξ, div_div]
      calc |A| * s ^ 2 / (c * ξ) ≤ |A| * 1 / (c * ξ) := by gcongr
        _ = |A| / (c * ξ) := by ring
    have k3 : |e₁ * s| ≤ C₁ / c ^ 2 / ξ := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans b2
    have k4 : |A * co * s / pP ξ| ≤ |A| / ξ := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hp0]
      calc |A| * |co| * |s| / pP ξ ≤ |A| * 1 * 1 / pP ξ := by gcongr
        _ ≤ |A| / ξ := by rw [mul_one, mul_one]; exact div_le_div_of_nonneg_left (abs_nonneg _) hξ0 hpξ
    have k5 : |ξ * e₂ / pP ξ * s| ≤ 2 * Sg / ξ := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans b4
    have e : (|A| / c + C₁ / c ^ 2 + |A| + 2 * Sg + C₁ / c) / ξ
        = |A| / c / ξ + C₁ / c ^ 2 / ξ + |A| / ξ + 2 * Sg / ξ + C₁ / c / ξ := by ring
    rw [e]; linarith

/-- **The rotated pair vanishes at infinity**: `|P(ξ)| + |Q(ξ)| → 0`. -/
theorem tendsto_rot (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) :
    Tendsto (fun ξ => |rotP c g ξ| + |rotQ c g ξ|) atTop (𝓝 0) := by
  set K := |ampl g| / c + cst₁ g₁ g₂ / c ^ 2 + |ampl g| + 2 * cstU c g g₁ g₂ + cst₁ g₁ g₂ / c
  have hlim : Tendsto (fun ξ : ℝ => 2 * (K / ξ)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := K)).div_atTop (tendsto_id (α := ℝ))).const_mul 2
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with ξ hξ
  obtain ⟨h1, h2⟩ := abs_rot_le hc hg hg₁ hg₂c hξ
  linarith

/-! ### The forcing from the energy -/

/-- `|F|`'s cubic coefficient per `√E`: `(4/3)√(4/(3c)) + (32/9)√c`. -/
def kap3 (c : ℝ) : ℝ := 4 / 3 * √(4 / (3 * c)) + 32 / 9 * √c

/-- `|F|`'s quadratic coefficient per `√E`: `(2 + (4/3)|D − 2|)√(4/(3c))`. -/
def kap2 (c D : ℝ) : ℝ := (2 + 4 / 3 * |D - 2|) * √(4 / (3 * c))

set_option maxHeartbeats 1000000 in
/-- **The forcing from the energy**: for `c > 0`, `0 ≤ χ < c²`, `u ≥ 2` and `E(u) ≤ E`,
`|F(u)| ≤ √E(kap3 c/u³ + kap2 c D/u²)`, `D = c² − χ`. -/
theorem abs_forceF_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) {u E : ℝ} (hu : 2 ≤ u)
    (hE : energy (aP c χ) (psi c g) (rungU c g) u ≤ E) :
    |forceF c χ g u| ≤ √E * (kap3 c / u ^ 3 + kap2 c (c ^ 2 - χ) / u ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 < u := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hu1 hc2 hχc
  have hp0 : 0 < pP u := pP_pos hu1
  have hp : pP u = u ^ 2 - 1 := rfl
  have hp34 : 3 / 4 * u ^ 2 ≤ pP u := by rw [hp]; nlinarith
  have halo : c * pP u ≤ aP c χ u := Cvs.Prolate.RungConnectionIdentity.le_aP_far hχc.le hu1.le
  have hahi : aP c χ u ≤ c * u ^ 2 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.aP_le hc hχ0 hu1.le
  set ψ := psi c g u with hψdef
  set U := rungU c g u with hUdef
  have hEψ : aP c χ u * ψ ^ 2 ≤ E := by
    unfold energy at hE
    have : 0 ≤ U ^ 2 / aP c χ u := by positivity
    linarith
  have hEU : U ^ 2 ≤ aP c χ u * E := by
    unfold energy at hE
    have h0 : 0 ≤ aP c χ u * ψ ^ 2 := by positivity
    have : U ^ 2 / aP c χ u ≤ E := by linarith
    rwa [div_le_iff₀ ha, mul_comm] at this
  have hE0 : 0 ≤ E := le_trans (by positivity) hEψ
  set r := √(4 / (3 * c)) with hr
  have hr2 : r ^ 2 = 4 / (3 * c) := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hsE : √E ^ 2 = E := Real.sq_sqrt hE0
  have hsc : √c ^ 2 = c := Real.sq_sqrt hc.le
  have hsE0 : 0 ≤ √E := Real.sqrt_nonneg _
  have hsc0 : 0 ≤ √c := Real.sqrt_nonneg _
  -- `|ψ| ≤ √E r/u`
  have hψb : |ψ| ≤ √E * r / u := by
    have k : ψ ^ 2 * (c * (3 / 4 * u ^ 2)) ≤ E := by
      have := mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_left hp34 hc.le) halo)
        (sq_nonneg ψ)
      linarith
    have h1 : ψ ^ 2 ≤ (√E * r / u) ^ 2 := by
      rw [div_pow, mul_pow, hsE, hr2,
        show E * (4 / (3 * c)) / u ^ 2 = E / (c * (3 / 4 * u ^ 2)) by field_simp,
        le_div_iff₀ (by positivity)]
      exact k
    exact abs_le.mpr (abs_le_of_sq_le_sq' h1 (div_nonneg (mul_nonneg hsE0 hr0) hu0.le))
  -- `|U| ≤ √E √c u`
  have hUb : |U| ≤ √E * √c * u := by
    have h1 : U ^ 2 ≤ (√E * √c * u) ^ 2 := by
      rw [mul_pow, mul_pow, hsE, hsc]
      nlinarith [mul_le_mul_of_nonneg_right hahi hE0]
    exact abs_le.mpr (abs_le_of_sq_le_sq' h1 (by positivity))
  -- `|v'| ≤ √E r/u + (4/3)√E√c`
  have hdv : |dv c g u| ≤ √E * r / u + 4 / 3 * (√E * √c) := by
    unfold dv
    rw [← hψdef, ← hUdef]
    refine (abs_add_le _ _).trans (add_le_add hψb ?_)
    rw [abs_div, abs_mul, abs_of_pos hu0, abs_of_pos hp0, div_le_iff₀ hp0]
    have : u * |U| ≤ u * (√E * √c * u) := mul_le_mul_of_nonneg_left hUb hu0.le
    nlinarith [mul_nonneg hsE0 hsc0]
  set D := c ^ 2 - χ with hD
  unfold forceF
  rw [← hψdef, ← hD]
  -- the two pieces
  have hip : 1 / pP u ≤ 4 / 3 / u ^ 2 := by
    rw [div_le_div_iff₀ hp0 (by positivity)]; linarith
  have t1 : |2 * dv c g u / (u * pP u)| ≤ √E * (4 / 3 * r + 32 / 9 * √c) / u ^ 3 := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos (mul_pos hu0 hp0)]
    have hup : 3 / 4 * u ^ 3 ≤ u * pP u := by nlinarith
    rw [div_le_div_iff₀ (mul_pos hu0 hp0) (by positivity)]
    have k1 : 2 * |dv c g u| * u ^ 3 ≤ 2 * (√E * r / u + 4 / 3 * (√E * √c)) * u ^ 3 := by gcongr
    have k2 : 2 * (√E * r / u + 4 / 3 * (√E * √c)) * u ^ 3 = 2 * √E * r * u ^ 2 + 8 / 3 * √E * √c * u ^ 3 := by
      field_simp; ring
    have k3 : 2 * √E * r * u ^ 2 + 8 / 3 * √E * √c * u ^ 3 ≤ √E * (4 / 3 * r + 32 / 9 * √c) * (u * pP u) := by
      have h4 : 4 / 3 * (3 / 4 * u ^ 3) ≤ 4 / 3 * (u * pP u) := by linarith
      have hEr : 0 ≤ √E * r := mul_nonneg hsE0 hr0
      have hEc : 0 ≤ √E * √c := mul_nonneg hsE0 hsc0
      have h5 : 0 ≤ √E * r * u ^ 2 * (u - 2) := mul_nonneg (mul_nonneg hEr (sq_nonneg u)) (by linarith)
      have h6 := mul_le_mul_of_nonneg_left hup hEr
      have h7 := mul_le_mul_of_nonneg_left hup hEc
      have e : √E * (4 / 3 * r + 32 / 9 * √c) * (u * pP u)
          = 4 / 3 * (√E * r * (u * pP u)) + 32 / 9 * (√E * √c * (u * pP u)) := by ring
      rw [e]
      nlinarith
    linarith
  have t2 : |(2 / u ^ 2 + (D - 2) / pP u) * (u * ψ)| ≤ √E * ((2 + 4 / 3 * |D - 2|) * r) / u ^ 2 := by
    rw [abs_mul]
    have hc1 : |2 / u ^ 2 + (D - 2) / pP u| ≤ (2 + 4 / 3 * |D - 2|) / u ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_div, abs_two, abs_of_pos (by positivity : (0 : ℝ) < u ^ 2), abs_of_pos hp0]
      have : |D - 2| / pP u ≤ 4 / 3 * |D - 2| / u ^ 2 := by
        rw [div_le_div_iff₀ hp0 (by positivity)]; nlinarith [abs_nonneg (D - 2)]
      have e : (2 + 4 / 3 * |D - 2|) / u ^ 2 = 2 / u ^ 2 + 4 / 3 * |D - 2| / u ^ 2 := by ring
      linarith
    have hc2' : |u * ψ| ≤ √E * r := by
      rw [abs_mul, abs_of_pos hu0]
      calc u * |ψ| ≤ u * (√E * r / u) := mul_le_mul_of_nonneg_left hψb hu0.le
        _ = √E * r := by field_simp
    calc |2 / u ^ 2 + (D - 2) / pP u| * |u * ψ| ≤ (2 + 4 / 3 * |D - 2|) / u ^ 2 * (√E * r) :=
          mul_le_mul hc1 hc2' (abs_nonneg _) (by positivity)
      _ = √E * ((2 + 4 / 3 * |D - 2|) * r) / u ^ 2 := by ring
  have e : -(2 * dv c g u / (u * pP u)) - (2 / u ^ 2 + (D - 2) / pP u) * (u * ψ)
      = -(2 * dv c g u / (u * pP u)) + (-((2 / u ^ 2 + (D - 2) / pP u) * (u * ψ))) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_neg]
  unfold kap3 kap2
  rw [← hr]
  have e2 : √E * ((4 / 3 * r + 32 / 9 * √c) / u ^ 3 + (2 + 4 / 3 * |D - 2|) * r / u ^ 2)
      = √E * (4 / 3 * r + 32 / 9 * √c) / u ^ 3 + √E * ((2 + 4 / 3 * |D - 2|) * r) / u ^ 2 := by ring
  rw [e2]
  exact add_le_add t1 t2

/-! ### The Duhamel bound -/

/-- `F` is continuous on `ξ > 1`. -/
theorem continuousAt_forceF
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 < ξ) : ContinuousAt (forceF c χ g) ξ := by
  obtain ⟨-, -, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  have hp : pP ξ ≠ 0 := (pP_pos hξ).ne'
  have hξ0 : ξ ≠ 0 := by linarith
  have hpc : Continuous pP := by unfold pP; fun_prop
  have hdv : ContinuousAt (dv c g) ξ :=
    hψc.continuousAt.add ((continuous_id.mul huc).continuousAt.div hpc.continuousAt hp)
  unfold forceF
  refine (((continuousAt_const.mul hdv).div (continuous_id.mul hpc).continuousAt (mul_ne_zero hξ0 hp)).neg).sub
    ((((continuousAt_const.div (continuous_pow 2).continuousAt (pow_ne_zero 2 hξ0)).add
      (continuousAt_const.div hpc.continuousAt hp))).mul (continuous_id.mul hψc).continuousAt)

/-- **The Duhamel bound**: for a rung with `c > 0`, `ξ₀ ≥ 2` and `|F(u)| ≤ k₃/u³ + k₂/u²` on `[ξ₀, ∞)`,
`c|ξ₀ψ(ξ₀) − (A/c)sin(cξ₀)| ≤ k₃/(2ξ₀²) + k₂/ξ₀`. -/
theorem abs_R_le (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ₀ k₃ k₂ : ℝ} (hξ₀ : 2 ≤ ξ₀) (hk₃ : 0 ≤ k₃) (hk₂ : 0 ≤ k₂)
    (hF : ∀ u, ξ₀ ≤ u → |forceF c χ g u| ≤ k₃ / u ^ 3 + k₂ / u ^ 2) :
    c * |ξ₀ * psi c g ξ₀ - ampl g / c * Real.sin (c * ξ₀)| ≤ k₃ / (2 * ξ₀ ^ 2) + k₂ / ξ₀ := by
  have hξ₀0 : 0 < ξ₀ := by linarith
  set B := k₃ / (2 * ξ₀ ^ 2) + k₂ / ξ₀ with hB
  set L := c * |ξ₀ * psi c g ξ₀ - ampl g / c * Real.sin (c * ξ₀)| with hL
  have hstep : ∀ X, ξ₀ ≤ X → L ≤ |rotP c g X| + |rotQ c g X| + B := by
    intro X hX
    have hgt : ∀ u ∈ uIcc ξ₀ X, 1 < u := fun u hu => by
      rw [uIcc_of_le hX] at hu; linarith [hu.1]
    have hFc : ContinuousOn (forceF c χ g) (uIcc ξ₀ X) := fun u hu =>
      (continuousAt_forceF hg hg₁ hg₂c hang (hgt u hu)).continuousWithinAt
    have hcosI : IntervalIntegrable (fun u => forceF c χ g u * Real.cos (c * u)) volume ξ₀ X :=
      (hFc.mul (by fun_prop)).intervalIntegrable
    have hsinI : IntervalIntegrable (fun u => -(forceF c χ g u * Real.sin (c * u))) volume ξ₀ X :=
      (hFc.mul (by fun_prop)).neg.intervalIntegrable
    have hP := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => (hasDerivAt_rot hg hg₁ hg₂c hang (hgt u hu)).1) hcosI
    have hQ := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => (hasDerivAt_rot hg hg₁ hg₂c hang (hgt u hu)).2) hsinI
    have hsI' : IntervalIntegrable (fun u => forceF c χ g u * Real.sin (c * u)) volume ξ₀ X :=
      (hFc.mul (by fun_prop : ContinuousOn (fun u : ℝ => Real.sin (c * u)) _)).intervalIntegrable
    set s₀ := Real.sin (c * ξ₀)
    set c₀ := Real.cos (c * ξ₀)
    have hid := rot_identity (g := g) hc.ne' ξ₀
    have hkey : c * (ξ₀ * psi c g ξ₀ - ampl g / c * s₀)
        = rotP c g X * s₀ + rotQ c g X * c₀
          + ∫ u in ξ₀..X, forceF c χ g u * (Real.sin (c * u) * c₀ - Real.cos (c * u) * s₀) := by
      have e : ∫ u in ξ₀..X, forceF c χ g u * (Real.sin (c * u) * c₀ - Real.cos (c * u) * s₀)
          = c₀ * (-∫ u in ξ₀..X, -(forceF c χ g u * Real.sin (c * u)))
            - s₀ * ∫ u in ξ₀..X, forceF c χ g u * Real.cos (c * u) := by
        rw [intervalIntegral.integral_neg, neg_neg, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hsI'.const_mul c₀)
            (hcosI.const_mul s₀)]
        refine intervalIntegral.integral_congr fun u _ => ?_
        ring
      rw [e, hP, hQ, hid]; ring
    have hsin1 : ∀ u, |Real.sin (c * u) * c₀ - Real.cos (c * u) * s₀| ≤ 1 := fun u => by
      have : Real.sin (c * u) * c₀ - Real.cos (c * u) * s₀ = Real.sin (c * u - c * ξ₀) := by
        rw [Real.sin_sub]
      rw [this]; exact Real.abs_sin_le_one _
    have hmaj : IntervalIntegrable (fun u => k₃ / u ^ 3 + k₂ / u ^ 2) volume ξ₀ X := by
      refine ContinuousOn.intervalIntegrable fun u hu => ?_
      have : u ≠ 0 := by linarith [hgt u hu]
      exact ((continuousAt_const.div (continuous_pow 3).continuousAt (pow_ne_zero 3 this)).add
        (continuousAt_const.div (continuous_pow 2).continuousAt (pow_ne_zero 2 this))).continuousWithinAt
    have hint : ‖∫ u in ξ₀..X, forceF c χ g u * (Real.sin (c * u) * c₀ - Real.cos (c * u) * s₀)‖
        ≤ ∫ u in ξ₀..X, (k₃ / u ^ 3 + k₂ / u ^ 2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hX (ae_of_all _ fun u hu => ?_) hmaj
      rw [Real.norm_eq_abs, abs_mul]
      calc |forceF c χ g u| * |Real.sin (c * u) * c₀ - Real.cos (c * u) * s₀| ≤ |forceF c χ g u| * 1 :=
            mul_le_mul_of_nonneg_left (hsin1 u) (abs_nonneg _)
        _ ≤ k₃ / u ^ 3 + k₂ / u ^ 2 := by rw [mul_one]; exact hF u hu.1.le
    have hval : ∫ u in ξ₀..X, (k₃ / u ^ 3 + k₂ / u ^ 2) ≤ B := by
      have hd : ∀ u ∈ uIcc ξ₀ X, HasDerivAt (fun u => -(k₃ / (2 * u ^ 2)) - k₂ / u) (k₃ / u ^ 3 + k₂ / u ^ 2) u := by
        intro u hu
        have hu0 : u ≠ 0 := by linarith [hgt u hu]
        have h1 := ((hasDerivAt_pow 2 u).const_mul 2).inv (by positivity)
        have h2 := (hasDerivAt_id' u).inv hu0
        refine ((h1.const_mul k₃).neg.sub (h2.const_mul k₂)).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
        · field_simp; ring
        · exact Eventually.of_forall fun v => by simp [div_eq_mul_inv]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hmaj, hB]
      have h3 : 0 ≤ k₃ / (2 * X ^ 2) := by positivity
      have h4 : 0 ≤ k₂ / X := div_nonneg hk₂ (by linarith)
      linarith
    have habs : |c * (ξ₀ * psi c g ξ₀ - ampl g / c * s₀)| ≤ |rotP c g X| + |rotQ c g X| + B := by
      rw [hkey]
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ((Real.norm_eq_abs _ ▸ hint).trans hval)
      · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    rwa [abs_mul, abs_of_pos hc] at habs
  have hlim := (tendsto_rot hc hg hg₁ hg₂c).add_const B
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim ((eventually_ge_atTop ξ₀).mono fun X hX => hstep X hX)

/-- `kap3 c ≥ 0`. -/
theorem kap3_nonneg (c : ℝ) : 0 ≤ kap3 c := by unfold kap3; positivity

/-- `kap2 c D ≥ 0`. -/
theorem kap2_nonneg (c D : ℝ) : 0 ≤ kap2 c D := by unfold kap2; positivity

/-- `ξρ(ξ) = ξψ(ξ) − (A/c)sin(cξ)` for `c, ξ ≠ 0`. -/
theorem mul_rhoG (hc : c ≠ 0) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ξ * rhoG c g ξ = ξ * psi c g ξ - ampl g / c * Real.sin (c * ξ) := by
  unfold rhoG; field_simp

set_option maxHeartbeats 1000000 in
/-- **The Duhamel remainder on `(1, ∞)`**: for a rung with `c > 0`, `0 ≤ χ < c²` and `E ≤ E♯` on `[2, ∞)`,
`∫₁^∞ ξ²ρ² ≤ 8∫₁^∞ψ² + E♯(2/c + (kap3 c²/48 + kap2 c D²)/c²)`, `D = c² − χ`. -/
theorem lintegral_rho_sq_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {E : ℝ} (hE : ∀ ξ, 2 ≤ ξ → energy (aP c χ) (psi c g) (rungU c g) ξ ≤ E) :
    ∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2)
      ≤ ENNReal.ofReal (8 * (∫ ξ in Ioi 1, psi c g ξ ^ 2)
        + E * (2 / c + (kap3 c ^ 2 / 48 + kap2 c (c ^ 2 - χ) ^ 2) / c ^ 2)) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hc2 : 0 < c ^ 2 := by positivity
  have hψi := Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hgc
  set A := ampl g with hA
  set K3 := kap3 c with hK3
  set K2 := kap2 c (c ^ 2 - χ) with hK2
  have hK30 : 0 ≤ K3 := kap3_nonneg c
  have hK20 : 0 ≤ K2 := kap2_nonneg _ _
  have hE0 : 0 ≤ E := by
    refine le_trans ?_ (hE 2 le_rfl)
    unfold energy
    have := aP_pos (by norm_num : (1 : ℝ) < 2) hc2 hχc
    positivity
  have hAE : A ^ 2 / c ≤ E :=
    le_of_tendsto (Cvs.Prolate.RungConnectionIdentity.tendsto_energy hg hg₁ hg₂c hc hχ0 hχc)
      ((eventually_ge_atTop 2).mono fun ξ hξ => hE ξ hξ)
  have hR : ∀ ξ, 0 < ξ → ξ ^ 2 * rhoG c g ξ ^ 2 = (ξ * psi c g ξ - A / c * Real.sin (c * ξ)) ^ 2 :=
    fun ξ hξ => by rw [← mul_rhoG hc.ne' hξ.ne']; ring
  -- the edge piece `(1, 2]`
  have hnear : ∫⁻ ξ in Ioc 1 2, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2)
      ≤ ENNReal.ofReal (8 * (∫ ξ in Ioi 1, psi c g ξ ^ 2) + 2 * (A ^ 2 / c ^ 2)) := by
    have hint : IntegrableOn (fun ξ => 8 * psi c g ξ ^ 2 + 2 * (A ^ 2 / c ^ 2)) (Ioc 1 2) :=
      (hψi.integrableOn.const_mul 8).add (integrableOn_const (by simp))
    calc ∫⁻ ξ in Ioc 1 2, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2)
        ≤ ∫⁻ ξ in Ioc 1 2, ENNReal.ofReal (8 * psi c g ξ ^ 2 + 2 * (A ^ 2 / c ^ 2)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun ξ hξ => ENNReal.ofReal_le_ofReal ?_
          have hξ0 : 0 < ξ := by linarith [hξ.1]
          rw [hR ξ hξ0]
          have hs2 : Real.sin (c * ξ) ^ 2 ≤ 1 := Real.sin_sq_le_one _
          have hξ2 : ξ ^ 2 ≤ 4 := by nlinarith [hξ.2]
          have k1 : (ξ * psi c g ξ - A / c * Real.sin (c * ξ)) ^ 2
              ≤ 2 * (ξ * psi c g ξ) ^ 2 + 2 * (A / c * Real.sin (c * ξ)) ^ 2 := by
            nlinarith [sq_nonneg (ξ * psi c g ξ + A / c * Real.sin (c * ξ))]
          have k2 : (ξ * psi c g ξ) ^ 2 ≤ 4 * psi c g ξ ^ 2 := by
            rw [mul_pow]; exact mul_le_mul_of_nonneg_right hξ2 (sq_nonneg _)
          have k3 : (A / c * Real.sin (c * ξ)) ^ 2 ≤ A ^ 2 / c ^ 2 := by
            rw [mul_pow, div_pow]
            exact mul_le_of_le_one_right (by positivity) hs2
          linarith
      _ = ENNReal.ofReal (∫ ξ in Ioc 1 2, (8 * psi c g ξ ^ 2 + 2 * (A ^ 2 / c ^ 2))) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_add (hψi.integrableOn.const_mul 8) (integrableOn_const (by simp)), integral_const_mul,
            setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
          have : ∫ ξ in Ioc 1 2, psi c g ξ ^ 2 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 :=
            setIntegral_mono_set hψi.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
              (ae_of_all _ Ioc_subset_Ioi_self)
          norm_num
          linarith
  -- the far piece `(2, ∞)`
  set m : ℝ → ℝ := fun ξ => 2 * E / c ^ 2 * (K3 ^ 2 / 4 * ξ ^ (-4 : ℝ) + K2 ^ 2 * ξ ^ (-2 : ℝ)) with hm
  have hmi : IntegrableOn m (Ioi 2) :=
    (((integrableOn_Ioi_rpow_of_lt (by norm_num) two_pos).const_mul (K3 ^ 2 / 4)).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) two_pos).const_mul (K2 ^ 2))).const_mul _
  have hfar : ∫⁻ ξ in Ioi 2, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2)
      ≤ ENNReal.ofReal (E * ((K3 ^ 2 / 48 + K2 ^ 2) / c ^ 2)) := by
    calc ∫⁻ ξ in Ioi 2, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2) ≤ ∫⁻ ξ in Ioi 2, ENNReal.ofReal (m ξ) := by
          refine setLIntegral_mono' measurableSet_Ioi fun ξ hξ => ENNReal.ofReal_le_ofReal ?_
          have hξ2 : (2 : ℝ) < ξ := hξ
          have hξ0 : 0 < ξ := by linarith
          rw [hR ξ hξ0]
          have hF : ∀ u, ξ ≤ u → |forceF c χ g u| ≤ (√E * K3) / u ^ 3 + (√E * K2) / u ^ 2 := fun u hu => by
            have := abs_forceF_le hc hχ0 hχc (by linarith) (hE u (by linarith))
            rw [hK3, hK2]; linarith [show √E * (kap3 c / u ^ 3 + kap2 c (c ^ 2 - χ) / u ^ 2)
              = (√E * kap3 c) / u ^ 3 + (√E * kap2 c (c ^ 2 - χ)) / u ^ 2 by ring]
          have hb := abs_R_le hc hg hg₁ hg₂c hang hξ2.le (mul_nonneg (Real.sqrt_nonneg _) hK30)
            (mul_nonneg (Real.sqrt_nonneg _) hK20) hF
          set R := ξ * psi c g ξ - A / c * Real.sin (c * ξ)
          have hb' : |R| ≤ (√E * K3 / (2 * ξ ^ 2) + √E * K2 / ξ) / c := by
            rw [le_div_iff₀ hc, mul_comm]; exact hb
          have hR2 : R ^ 2 ≤ ((√E * K3 / (2 * ξ ^ 2) + √E * K2 / ξ) / c) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
          refine hR2.trans ?_
          have h4 : ξ ^ (-4 : ℝ) = 1 / ξ ^ 4 := by
            rw [Real.rpow_neg hξ0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
          have h2 : ξ ^ (-2 : ℝ) = 1 / ξ ^ 2 := by
            rw [Real.rpow_neg hξ0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
          simp only [hm]
          rw [h4, h2, div_pow, add_sq']
          have hsE : √E ^ 2 = E := Real.sq_sqrt hE0
          have e1 : (√E * K3 / (2 * ξ ^ 2)) ^ 2 = E * K3 ^ 2 / 4 / ξ ^ 4 := by
            rw [div_pow, mul_pow, hsE]; ring
          have e2 : (√E * K2 / ξ) ^ 2 = E * K2 ^ 2 / ξ ^ 2 := by rw [div_pow, mul_pow, hsE]
          rw [e1, e2]
          have hab : 2 * (√E * K3 / (2 * ξ ^ 2)) * (√E * K2 / ξ)
              ≤ E * K3 ^ 2 / 4 / ξ ^ 4 + E * K2 ^ 2 / ξ ^ 2 := by
            nlinarith [sq_nonneg (√E * K3 / (2 * ξ ^ 2) - √E * K2 / ξ), e1, e2]
          rw [div_le_iff₀ hc2]
          have e3 : 2 * E / c ^ 2 * (K3 ^ 2 / 4 * (1 / ξ ^ 4) + K2 ^ 2 * (1 / ξ ^ 2)) * c ^ 2
              = 2 * (E * K3 ^ 2 / 4 / ξ ^ 4 + E * K2 ^ 2 / ξ ^ 2) := by field_simp
          rw [e3]; linarith
      _ = ENNReal.ofReal (∫ ξ in Ioi 2, m ξ) :=
          (ofReal_integral_eq_lintegral_ofReal hmi (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => by
            have : (0 : ℝ) < ξ := lt_trans two_pos hξ
            simp only [hm]; positivity)).symm
      _ = _ := by
          congr 1
          simp only [hm]
          rw [integral_const_mul, integral_add ((integrableOn_Ioi_rpow_of_lt (by norm_num) two_pos).const_mul _)
            ((integrableOn_Ioi_rpow_of_lt (by norm_num) two_pos).const_mul _), integral_const_mul,
            integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) two_pos,
            integral_Ioi_rpow_of_lt (by norm_num) two_pos]
          norm_num
          field_simp
          ring
  -- assemble
  have hsplit : ∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2)
      = (∫⁻ ξ in Ioc 1 2, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2))
        + ∫⁻ ξ in Ioi 2, ENNReal.ofReal (ξ ^ 2 * rhoG c g ξ ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)]
    exact lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same
  rw [hsplit]
  refine (add_le_add hnear hfar).trans ?_
  have hI0 : 0 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 2 * (A ^ 2 / c ^ 2) ≤ E * (2 / c) := by
    have e : 2 * (A ^ 2 / c ^ 2) = 2 / c * (A ^ 2 / c) := by field_simp
    rw [e]; nlinarith [mul_le_mul_of_nonneg_left hAE (by positivity : (0 : ℝ) ≤ 2 / c)]
  nlinarith

/-! ### The exterior law on a rung and on the rung profile -/

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung lev muR lamR rung_spec psi_rung continuousOn_rung lev_spec)

/-- The per-rung remainder factor: `8 + (144/49)(2D + 3c)·E_c(D)·(2/c + (kap3 c²/48 + kap2 c D²)/c²)`, with
`E_c(D) = (1 + 2(c + 1)/D)(2c + 1)√((2c + 1)(D + 2c + 1))/c²` the energy cap at `1 + 1/c`. -/
def remFactor (c D : ℝ) : ℝ :=
  8 + 144 / 49 * (2 * D + 3 * c) * ((1 + 2 * (c + 1) / D) * ((2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) / c ^ 2))
    * (2 / c + (kap3 c ^ 2 / 48 + kap2 c D ^ 2) / c ^ 2)

/-- **The Poisson remainder of a rung**: for `c ≥ 1` and `0 < D = c² − χ_k`,
`∫₁^∞ ξ²ρ_{h_k}² ≤ (π/c)(1 − λ_k)·remFactor c D`. -/
theorem lintegral_rho_rung_le {c : ℝ} {k : ℕ} (hc : 1 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hχc : lev c k < c ^ 2) :
    ∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c (rung c k) ξ ^ 2)
      ≤ ENNReal.ofReal (π / c * (1 - lamR c k) * remFactor c (c ^ 2 - lev c k)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := rung_spec h
  have hχ0 : 0 ≤ lev c k := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (lev_spec h).1
  set D := c ^ 2 - lev c k with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set Ec := (1 + 2 * (c + 1) / D) * ((2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) / c ^ 2) with hEc
  have hEc0 : 0 ≤ Ec := by positivity
  obtain ⟨hW, hcap⟩ := Cvs.Prolate.Envelope.RungEdgeMassExterior.ecap_edge_le hc0 hχ0 hχc
  have h1 : 1 < 1 + 1 / c := lt_add_of_pos_right 1 (by positivity)
  have hm := Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc0 h
  have hω : 0 ≤ 1 - lamR c k := by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h]
  have hedge := Cvs.Prolate.Envelope.RungEdgeMassExterior.edge_mass hc hχc hg hg₁ hg₂c hang
  rw [hm] at hedge
  set E := Ec * (144 / 49 * (2 * D + 3 * c) * (π / c * (1 - lamR c k))) with hE
  have hEb : ∀ ξ, 2 ≤ ξ → energy (aP c (lev c k)) (psi c (rung c k)) (rungU c (rung c k)) ξ ≤ E := by
    intro ξ hξ
    have hξ' : 1 + 1 / c ≤ ξ := by
      have : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
      linarith
    refine (Cvs.Prolate.Envelope.RungEdgeMassExterior.energy_le_ecap hc0 hχ0 hχc hg hg₁ hg₂c hang h1 hξ' hW).trans ?_
    calc Cvs.Prolate.Envelope.RungEdgeMassExterior.ecap c (lev c k) (1 + 1 / c) * psi c (rung c k) 1 ^ 2
        ≤ Ec * psi c (rung c k) 1 ^ 2 := mul_le_mul_of_nonneg_right (by rw [hEc, hD]; exact hcap) (sq_nonneg _)
      _ ≤ E := mul_le_mul_of_nonneg_left hedge hEc0
  refine (lintegral_rho_sq_le hc0 hχ0 hχc hg hg₁ hg₂c hang hEb).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hm, hE]
  unfold remFactor
  rw [← hD, ← hEc]
  ring

/-- `ρ` is linear in the profile: `ρ_{G_j} = ρ_{h_{4j}} − α_j ρ_{h_0}`. -/
theorem rhoG_profile {c : ℝ} {j : ℕ} (h : ∃ χ, IsLevelIdx c (2 * j) χ) (ξ : ℝ) :
    rhoG c (fun s => rung c (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s) ξ
      = rhoG c (rung c (2 * j)) ξ - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rhoG c (rung c 0) ξ := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have h1 : ContinuousOn (rung c (2 * j)) (uIcc (-1) 1) := by rw [hI]; exact continuousOn_rung h
  have h0 : ContinuousOn (rung c 0) (uIcc (-1) 1) := by
    rw [hI]; exact continuousOn_rung (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  have hlin := Cvs.L2a.FullTailPolarisation.psi_add_smul h1 h0 c (-Cvs.Approximant.DeepIndexSpineSpan.alpha c j)
  have hp : (fun s => rung c (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s)
      = fun s => rung c (2 * j) s + -Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s := by
    funext s; ring
  unfold rhoG ampl
  rw [hp, hlin]
  simp only
  ring

set_option maxHeartbeats 1000000 in
/-- **The per-rung exterior law (Theorem PR)**: at `c = 2πx ≥ 80`, `a = 1/x`, `j < x` and `σ < 1`,
`Ext_{G_j}(σ) ≤ (a(|G_j(1)| + |G_j(0)|)/(2√(2(1 − σ))) + ζ(3/2)√M)²` with
`M = 2(π/c)(1 − λ_{4j})remFactor c D_j + 2α_j²(π/c)(1 − λ_0)remFactor c D_0`. -/
theorem extInt_profile_le (x : ℕ) (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) {σ : ℝ} (hσ : σ < 1) :
    Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x)
        (fun s => rung (2 * π * x) (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 s) σ
      ≤ (1 / x * (|rung (2 * π * x) (2 * j) 1 - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 1|
          + |rung (2 * π * x) (2 * j) 0 - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 0|)
          / (2 * √(2 * (1 - σ)))
        + Cvs.Route.Visibility.SawtoothPlancherelBounds.zeta32 * √(2 * (π / (2 * π * x) * (1 - lamR (2 * π * x) (2 * j))
            * remFactor (2 * π * x) ((2 * π * x) ^ 2 - lev (2 * π * x) (2 * j)))
          + 2 * Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 * (π / (2 * π * x) * (1 - lamR (2 * π * x) 0)
            * remFactor (2 * π * x) ((2 * π * x) ^ 2 - lev (2 * π * x) 0)))) ^ 2 := by
  obtain ⟨hex, hσj⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  obtain ⟨hex0, hσ0⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx (j := 0) (by omega)
  simp only [mul_zero] at hex0 hσ0
  have hx0 : (0 : ℝ) < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hx; linarith
    · exact_mod_cast h
  have hca : 2 * π / (1 / (x : ℝ)) = 2 * π * x := by field_simp
  set c := 2 * π * (x : ℝ) with hcdef
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have ha : (0 : ℝ) < 1 / x := by positivity
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < c)
  have hχj : lev c (2 * j) < c ^ 2 := by linarith
  have hχ0 : lev c 0 < c ^ 2 := by linarith
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha c j with hα
  set G : ℝ → ℝ := fun s => rung c (2 * j) s - α * rung c 0 s with hG
  obtain ⟨hh, hh₁, hh₂c, -, hheven, -⟩ := rung_spec hex
  obtain ⟨h0, h0₁, h0₂c, -, h0even, -⟩ := rung_spec hex0
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  set G₁ : ℝ → ℝ := fun s => Cvs.Prolate.EvenRungsByIndex.rung₁ c (2 * j) s - α * Cvs.Prolate.EvenRungsByIndex.rung₁ c 0 s
    with hG₁
  have hGd : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u := fun u hu => by
    have hu' : u ∈ uIcc (-1 : ℝ) 1 := by rw [hI]; exact ⟨by linarith [hu.1], hu.2⟩
    exact (hh u hu').sub ((h0 u hu').const_mul α)
  have hsub : Icc (0 : ℝ) 1 ⊆ uIcc (-1) 1 := by rw [hI]; exact Icc_subset_Icc (by norm_num) le_rfl
  have hc1' : ContinuousOn (Cvs.Prolate.EvenRungsByIndex.rung₁ c (2 * j)) (Icc 0 1) := fun s hs =>
    (hh₁ s (hsub hs)).continuousAt.continuousWithinAt
  have hc0' : ContinuousOn (Cvs.Prolate.EvenRungsByIndex.rung₁ c 0) (Icc 0 1) := fun s hs =>
    (h0₁ s (hsub hs)).continuousAt.continuousWithinAt
  have hG₁c : ContinuousOn G₁ (Icc 0 1) := hc1'.sub (continuousOn_const.mul hc0')
  have hGc : ContinuousOn G (Icc (-1) 1) :=
    (continuousOn_rung hex).sub (continuousOn_const.mul (continuousOn_rung hex0))
  have hGeven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s := fun s hs => by
    simp only [hG, hheven s hs, h0even s hs]
  have hGi : ∫ u in (0 : ℝ)..1, G u = 0 := by
    have hfold := Cvs.Prolate.SlepianEvenOrdering.integral_even_fold hGc fun s hs =>
      hGeven s ⟨by linarith [hs.1], hs.2⟩
    have hz := Cvs.Approximant.DeepIndexSpineSpan.integral_spineG (c := c) hc0 (S := {j}) (fun _ => 1)
    have e : (fun s => Cvs.Approximant.DeepIndexSpineSpan.spineG c (S := {j}) (fun _ => 1) s) = G := by
      funext s; simp [Cvs.Approximant.DeepIndexSpineSpan.spineG, hG, hα]
    rw [e] at hz
    linarith
  -- the remainder bound for `G`
  have hMh := lintegral_rho_rung_le hc1 hex hχj
  have hM0 := lintegral_rho_rung_le hc1 hex0 hχ0
  have hρh := Cvs.Route.Visibility.ExteriorImageSawtoothPoisson.measurable_rhoG (continuousOn_rung hex) c
  have hρ0 := Cvs.Route.Visibility.ExteriorImageSawtoothPoisson.measurable_rhoG (continuousOn_rung hex0) c
  set Mh := π / c * (1 - lamR c (2 * j)) * remFactor c (c ^ 2 - lev c (2 * j)) with hMhdef
  set M0 := π / c * (1 - lamR c 0) * remFactor c (c ^ 2 - lev c 0) with hM0def
  have hrem : ∀ D, 0 < D → 0 ≤ remFactor c D := fun D hD => by
    unfold remFactor
    have := kap3_nonneg c
    positivity
  have hMh0 : 0 ≤ Mh := by
    have := hrem _ (by linarith : 0 < c ^ 2 - lev c (2 * j))
    have : 0 ≤ 1 - lamR c (2 * j) := by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex]
    positivity
  have hM00 : 0 ≤ M0 := by
    have := hrem _ (by linarith : 0 < c ^ 2 - lev c 0)
    have : 0 ≤ 1 - lamR c 0 := by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex0]
    positivity
  have hMG : ∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c G ξ ^ 2) ≤ ENNReal.ofReal (2 * Mh + 2 * α ^ 2 * M0) := by
    calc ∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c G ξ ^ 2)
        ≤ ∫⁻ ξ in Ioi 1, (ENNReal.ofReal 2 * ENNReal.ofReal (ξ ^ 2 * rhoG c (rung c (2 * j)) ξ ^ 2)
            + ENNReal.ofReal (2 * α ^ 2) * ENNReal.ofReal (ξ ^ 2 * rhoG c (rung c 0) ξ ^ 2)) := by
          refine lintegral_mono fun ξ => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hG, hα, rhoG_profile hex, ← hα]
          nlinarith [sq_nonneg (ξ * (rhoG c (rung c (2 * j)) ξ + α * rhoG c (rung c 0) ξ))]
      _ = ENNReal.ofReal 2 * (∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c (rung c (2 * j)) ξ ^ 2))
            + ENNReal.ofReal (2 * α ^ 2) * ∫⁻ ξ in Ioi 1, ENNReal.ofReal (ξ ^ 2 * rhoG c (rung c 0) ξ ^ 2) := by
          rw [lintegral_add_left
            (f := fun ξ => ENNReal.ofReal 2 * ENNReal.ofReal (ξ ^ 2 * rhoG c (rung c (2 * j)) ξ ^ 2))
            (Measurable.const_mul (ENNReal.measurable_ofReal.comp
              ((measurable_id.pow_const 2).mul (hρh.pow_const 2))) _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal Mh + ENNReal.ofReal (2 * α ^ 2) * ENNReal.ofReal M0 := by gcongr
      _ = ENNReal.ofReal (2 * Mh + 2 * α ^ 2 * M0) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hfin := Cvs.Route.Visibility.ExteriorImageSawtoothPoisson.extInt_le (M := 2 * Mh + 2 * α ^ 2 * M0) hGd hG₁c hGc hGeven hGi ha hσ
    (by positivity)
    (by rw [hca]; exact hMG)
  exact hfin

/-! ### The depth is logarithmic in `1 − λ` -/

/-- **The plunge in closed form (P1′)**: for an even rung `g ≢ 0` with `ψ = μg` on `[−1, 1]`, `c ≥ 80`, `χ ≥ 0` and
`D = c² − χ ≥ 5c`, with `λ = (c/2π)μ²` and `w = (9D/(32c⁴))^{1/3}`,
`1 − λ ≤ (11/20)(π/(2√D) + 1/(2D))(e⁵/2)(πD/(4c) + 2)e^{−πD/(2c)}/w`. -/
theorem one_sub_lambda_le {μ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2
      ≤ 11 / 20 * (π / (2 * √(c ^ 2 - χ)) + 1 / (2 * (c ^ 2 - χ))) * (Real.exp 5 / 2)
        * (π * (c ^ 2 - χ) / (4 * c) + 2) * Real.exp (-(2 * (π * (c ^ 2 - χ) / (4 * c))))
        / (9 * (c ^ 2 - χ) / (32 * c ^ 4)) ^ (1 / 3 : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hχc : χ < c ^ 2 := by nlinarith
  set D := c ^ 2 - χ with hDdef
  have hD0 : 0 < D := by linarith
  set w := (9 * D / (32 * c ^ 4)) ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have hw3 : w ^ 3 = 9 * D / (32 * c ^ 4) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  -- `1 − √χ/c ≥ D/(2c²)`
  have hsχ : √χ ^ 2 = χ := Real.sq_sqrt hχ0
  have hsχc : √χ ≤ c := by rw [Real.sqrt_le_left hc0.le]; exact hχc.le
  have hsχ0 : 0 ≤ √χ := Real.sqrt_nonneg _
  have h1a : D / (2 * c ^ 2) ≤ 1 - √χ / c := by
    have : D = (c - √χ) * (c + √χ) := by rw [hDdef]; nlinarith
    rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, this]
    have e : √χ * (2 * c ^ 2) / c = 2 * c * √χ := by field_simp
    rw [e]; nlinarith [mul_nonneg (sub_nonneg.mpr hsχc) (sub_nonneg.mpr hsχc)]
  -- the window `w`
  have hwle : w ≤ D / (4 * c ^ 2) := by
    apply (pow_le_pow_iff_left₀ hw0.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hw3, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hD2 : 18 * c ^ 2 ≤ D ^ 2 := by nlinarith
    have : 0 ≤ D * c ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD2 (by positivity : (0 : ℝ) ≤ 9 * D * c ^ 4)]
  have hd1 : w ≤ (1 - √χ / c) / 2 := by
    have : D / (4 * c ^ 2) = D / (2 * c ^ 2) / 2 := by ring
    linarith
  have hdrop : 16 * c ^ 2 * w ^ 3 ≤ 9 * (1 - √χ / c) := by
    rw [hw3]
    have : 16 * c ^ 2 * (9 * D / (32 * c ^ 4)) = 9 * (D / (2 * c ^ 2)) := by field_simp; ring
    rw [this]; linarith
  have hJ := Cvs.Prolate.ForbiddenZoneClosedForm.forbJ_ge_window hc0 hχ0 hχc hw0 hd1 hdrop
  have hK := Cvs.Prolate.ForbiddenZoneClosedForm.ellK_le hc0 hχ0 hχc
  have hP := Cvs.Prolate.PlungeLawIntegral.plunge_P1 hg hg₁ hg₂c hang hc hχ0 hD heven hg0 hμ
  set Z := Cvs.Prolate.ForbiddenZoneGrowth.forbZ c χ (√χ / c)
  set Z₀ := π * D / (4 * c) with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := by positivity
  have hΦ := (Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC_forbZ_le hc0 hχ0 hχc).trans
    (Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC_le hZ₀0)
  -- `1/J ≤ e² e^{−2Φ_C(Z)}/w`
  have hJpos : 0 < Cvs.Prolate.PlungeLawIntegral.forbJ c χ := Cvs.Prolate.PlungeLawIntegral.forbJ_pos hc0 hχc
  have hJinv : 1 / Cvs.Prolate.PlungeLawIntegral.forbJ c χ
      ≤ Real.exp 2 * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z)) / w := by
    rw [div_le_div_iff₀ hJpos hw0, one_mul]
    have h1 : Real.exp 2 * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z))
        * Real.exp (2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z - 2) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
    have e : Real.exp 2 * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z))
        * (w * Real.exp (2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z - 2)) = w := by
      calc _ = (Real.exp 2 * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z))
            * Real.exp (2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z - 2)) * w := by ring
        _ = w := by rw [h1, one_mul]
    calc w = Real.exp 2 * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z))
          * (w * Real.exp (2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z - 2)) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by positivity)
  -- combine
  have hKc : Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D) ≤ c * (π / (2 * √D) + 1 / (2 * D)) := by
    have hsD : 0 < √D := Real.sqrt_pos.mpr hD0
    have : c / √D * (π / 2) = c * (π / (2 * √D)) := by field_simp
    have e2 : c / (2 * D) = c * (1 / (2 * D)) := by ring
    rw [hDdef] at this e2 ⊢; linarith
  have hK0 : 0 ≤ Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D) := by
    unfold Cvs.Prolate.PlungeLawIntegral.ellK
    have : 0 ≤ ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ := setIntegral_nonneg measurableSet_Ioi fun ξ hξ =>
      (one_div_pos.mpr (aP_pos hξ (by positivity) hχc)).le
    positivity
  have hΦ' : Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC Z))
      ≤ Real.exp 3 / 2 * (Z₀ + 2) * Real.exp (-(2 * Z₀)) := by rw [hZ₀, hDdef]; exact hΦ
  have hA : 11 / 20 * (Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D)) / c
      ≤ 11 / 20 * (c * (π / (2 * √D) + 1 / (2 * D))) / c :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKc (by norm_num)) hc0.le
  have hB : 1 / Cvs.Prolate.PlungeLawIntegral.forbJ c χ
      ≤ Real.exp 2 * (Real.exp 3 / 2 * (Z₀ + 2) * Real.exp (-(2 * Z₀))) / w :=
    hJinv.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΦ' (Real.exp_pos _).le) hw0.le)
  have hA0 : 0 ≤ 11 / 20 * (c * (π / (2 * √D) + 1 / (2 * D))) / c := by positivity
  refine hP.trans ?_
  calc 11 / 10 / 2 * (Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D)) / (c * Cvs.Prolate.PlungeLawIntegral.forbJ c χ)
      = 11 / 20 * (Cvs.Prolate.PlungeLawIntegral.ellK c χ + c / (2 * D)) / c * (1 / Cvs.Prolate.PlungeLawIntegral.forbJ c χ) := by
        field_simp; ring
    _ ≤ 11 / 20 * (c * (π / (2 * √D) + 1 / (2 * D))) / c
          * (Real.exp 2 * (Real.exp 3 / 2 * (Z₀ + 2) * Real.exp (-(2 * Z₀))) / w) :=
        mul_le_mul hA hB (by positivity) hA0
    _ = _ := by
        rw [show Real.exp 5 = Real.exp 2 * Real.exp 3 by rw [← Real.exp_add]; norm_num]
        field_simp

/-- **The plunge on a rung, crude form**: for `c ≥ 80` and `D = c² − χ_k ≥ 5c`,
`1 − λ_k ≤ (33/20)e⁵·c·e^{−πD/(4c)}`. -/
theorem one_sub_lamR_le_exp {k : ℕ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ)
    (hD : 5 * c ≤ c ^ 2 - lev c k) :
    1 - lamR c k ≤ 33 / 20 * Real.exp 5 * c * Real.exp (-(π * (c ^ 2 - lev c k) / (4 * c))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec h
  have hχ0 : 0 ≤ lev c k := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (lev_spec h).1
  have hP := one_sub_lambda_le hg hg₁ hg₂c hang hc hχ0 hD heven (Cvs.Prolate.EvenRungsByIndex.rung_ne_zero h)
    (psi_rung h)
  rw [← mul_comm (muR c k ^ 2), ← Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc0] at hP
  refine hP.trans ?_
  set D := c ^ 2 - lev c k with hDdef
  have hD0 : 400 ≤ D := by nlinarith
  set Z₀ := π * D / (4 * c) with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := by positivity
  set w := (9 * D / (32 * c ^ 4)) ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have hw3 : w ^ 3 = 9 * D / (32 * c ^ 4) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hwc : 1 / c ≤ w := by
    apply (pow_le_pow_iff_left₀ (by positivity) hw0.le (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hw3, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hc0 4]
  have hinvw : 1 / w ≤ c := by
    rw [div_le_iff₀ hw0]; rw [div_le_iff₀ hc0] at hwc; linarith
  have hsD : 1 ≤ √D := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hA : π / (2 * √D) + 1 / (2 * D) ≤ 3 := by
    have h1 : π / (2 * √D) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
    have h2 : 1 / (2 * D) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hB : (Z₀ + 2) * Real.exp (-(2 * Z₀)) ≤ 2 * Real.exp (-Z₀) := by
    have h1 : Z₀ + 2 ≤ 2 * Real.exp Z₀ := by linarith [Real.add_one_le_exp Z₀]
    have h2 : (Z₀ + 2) * Real.exp (-Z₀) ≤ 2 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos Z₀)]; linarith
    have e : Real.exp (-(2 * Z₀)) = Real.exp (-Z₀) * Real.exp (-Z₀) := by rw [← Real.exp_add]; ring_nf
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hA0 : 0 ≤ π / (2 * √D) + 1 / (2 * D) := by positivity
  calc 11 / 20 * (π / (2 * √D) + 1 / (2 * D)) * (Real.exp 5 / 2) * (Z₀ + 2) * Real.exp (-(2 * Z₀)) / w
      = 11 / 20 * (π / (2 * √D) + 1 / (2 * D)) * (Real.exp 5 / 2) * ((Z₀ + 2) * Real.exp (-(2 * Z₀)))
          * (1 / w) := by ring
    _ ≤ 11 / 20 * 3 * (Real.exp 5 / 2) * (2 * Real.exp (-Z₀)) * c := by gcongr
    _ = 33 / 20 * Real.exp 5 * c * Real.exp (-Z₀) := by ring

/-- **Polynomial against an exponentially small factor**: for `t ≥ 0`, `0 ≤ y ≤ min(1, K e^{−t})`, `K ≥ 1`, `κ > 0`,
`(1 + t)^m y^κ ≤ (1 + 2 log K)^m + m!(2/κ)^m e^{κ/2}`. -/
theorem one_add_pow_mul_rpow_le {t y K κ : ℝ} (m : ℕ) (ht : 0 ≤ t) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hK : 1 ≤ K)
    (hκ : 0 < κ) (hyK : y ≤ K * Real.exp (-t)) :
    (1 + t) ^ m * y ^ κ ≤ (1 + 2 * Real.log K) ^ m + m.factorial * (2 / κ) ^ m * Real.exp (κ / 2) := by
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hB0 : 0 ≤ (m.factorial : ℝ) * (2 / κ) ^ m * Real.exp (κ / 2) := by positivity
  have hyk0 : 0 ≤ y ^ κ := Real.rpow_nonneg hy0 _
  by_cases hT : t ≤ 2 * Real.log K
  · have h1 : (1 + t) ^ m ≤ (1 + 2 * Real.log K) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have h2 : y ^ κ ≤ 1 := Real.rpow_le_one hy0 hy1 hκ.le
    calc (1 + t) ^ m * y ^ κ ≤ (1 + 2 * Real.log K) ^ m * 1 := mul_le_mul h1 h2 hyk0 (by positivity)
      _ ≤ _ := by linarith
  · push Not at hT
    have hK' : K ≤ Real.exp (t / 2) := by
      rw [← Real.exp_log (by linarith : 0 < K)]; exact Real.exp_le_exp.mpr (by linarith)
    have hy' : y ≤ Real.exp (-(t / 2)) := by
      refine hyK.trans ?_
      calc K * Real.exp (-t) ≤ Real.exp (t / 2) * Real.exp (-t) := by gcongr
        _ = Real.exp (-(t / 2)) := by rw [← Real.exp_add]; ring_nf
    have h2 : y ^ κ ≤ Real.exp (-(κ * t / 2)) := by
      calc y ^ κ ≤ Real.exp (-(t / 2)) ^ κ := Real.rpow_le_rpow hy0 hy' hκ.le
        _ = Real.exp (-(κ * t / 2)) := by rw [← Real.exp_mul]; ring_nf
    have hf := Real.pow_div_factorial_le_exp (κ * (1 + t) / 2) (by positivity) m
    have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have h1 : (1 + t) ^ m ≤ m.factorial * (2 / κ) ^ m * Real.exp (κ * (1 + t) / 2) := by
      rw [div_le_iff₀ hfac, div_pow, mul_pow] at hf
      have e : (2 / κ) ^ m * (κ ^ m / 2 ^ m) = 1 := by
        rw [div_pow]; field_simp
      calc (1 + t) ^ m = (2 / κ) ^ m * (κ ^ m / 2 ^ m) * (1 + t) ^ m := by rw [e, one_mul]
        _ = (2 / κ) ^ m * (κ ^ m * (1 + t) ^ m / 2 ^ m) := by ring
        _ ≤ (2 / κ) ^ m * (Real.exp (κ * (1 + t) / 2) * m.factorial) := by gcongr
        _ = _ := by ring
    calc (1 + t) ^ m * y ^ κ
        ≤ (m.factorial * (2 / κ) ^ m * Real.exp (κ * (1 + t) / 2)) * Real.exp (-(κ * t / 2)) :=
          mul_le_mul h1 h2 hyk0 (by positivity)
      _ = m.factorial * (2 / κ) ^ m * Real.exp (κ / 2) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ _ := by linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * Real.log K) m]

set_option maxHeartbeats 1000000 in
/-- **The remainder factor is polynomial in the depth**: for `c ≥ 80` and `4c/log c ≤ D ≤ c²`,
`remFactor c D ≤ 728(1 + log c)(D/c + 1)⁴`. -/
theorem remFactor_le {c D : ℝ} (hc : 80 ≤ c) (hD1 : 4 * c / Real.log c ≤ D) (hD2 : D ≤ c ^ 2) :
    remFactor c D ≤ 728 * (1 + Real.log c) * (D / c + 1) ^ 4 := by
  have hc0 : 0 < c := by linarith
  set L := Real.log c with hL
  have hL4 : 4 ≤ L := Cvs.Prolate.EvenLevelIndexLemma.four_le_log hc
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD1
  have hDL : 4 * c ≤ D * L := by rwa [div_le_iff₀ (by linarith)] at hD1
  set d := D / c with hd
  have hd0 : 0 ≤ d := by positivity
  have hDd : D = c * d := by rw [hd]; field_simp
  -- the energy cap
  have hE1 : 1 + 2 * (c + 1) / D ≤ 1 + L := by
    have : 2 * (c + 1) / D ≤ L := by rw [div_le_iff₀ hD0]; nlinarith
    linarith
  have hE2 : (2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) / c ^ 2 ≤ 3 * (d + 3) := by
    have hs : √((2 * c + 1) * (D + 2 * c + 1)) ≤ c * (d + 3) := by
      rw [Real.sqrt_le_left (by positivity)]
      rw [hDd]; nlinarith [mul_nonneg hc0.le hd0]
    rw [div_le_iff₀ (by positivity)]
    calc (2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) ≤ (3 * c) * (c * (d + 3)) :=
          mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by positivity)
      _ = 3 * (d + 3) * c ^ 2 := by ring
  have hE20 : 0 ≤ (2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) / c ^ 2 := by positivity
  have hEc : (1 + 2 * (c + 1) / D) * ((2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) / c ^ 2)
      ≤ (1 + L) * (3 * (d + 3)) := mul_le_mul hE1 hE2 hE20 (by linarith)
  -- the Duhamel factor
  have hk3 : kap3 c ^ 2 ≤ 48 * c := by
    unfold kap3
    have h1 : √(4 / (3 * c)) ≤ 1 := Real.sqrt_le_one.mpr (by rw [div_le_one (by positivity)]; linarith)
    have hsc : 1 ≤ √c := by rw [Real.le_sqrt (by norm_num) hc0.le]; linarith
    have hsc2 : √c ^ 2 = c := Real.sq_sqrt hc0.le
    have h2 : 4 / 3 * √(4 / (3 * c)) + 32 / 9 * √c ≤ 5 * √c := by nlinarith [Real.sqrt_nonneg (4 / (3 * c))]
    have h3 := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  have hk2 : kap2 c D ^ 2 ≤ 6 * (D + 3) ^ 2 / c := by
    unfold kap2
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h1 : 2 + 4 / 3 * |D - 2| ≤ 2 * (D + 3) := by
      have : |D - 2| ≤ D + 2 := by rw [abs_le]; constructor <;> linarith
      linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    calc (2 + 4 / 3 * |D - 2|) ^ 2 * (4 / (3 * c)) ≤ (2 * (D + 3)) ^ 2 * (4 / (3 * c)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 16 / 3 * (D + 3) ^ 2 / c := by field_simp; norm_num
      _ ≤ 6 * (D + 3) ^ 2 / c := by gcongr; norm_num
  have hD3 : D + 3 ≤ c * (d + 1) := by rw [hDd]; nlinarith
  have hF : 2 / c + (kap3 c ^ 2 / 48 + kap2 c D ^ 2) / c ^ 2 ≤ 9 * (d + 1) ^ 2 / c := by
    have h1 : (kap3 c ^ 2 / 48 + kap2 c D ^ 2) / c ^ 2 ≤ (c + 6 * (D + 3) ^ 2 / c) / c ^ 2 := by
      gcongr; linarith
    have h2 : (D + 3) ^ 2 ≤ (c * (d + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) hD3 2
    have h3 : (c + 6 * (D + 3) ^ 2 / c) / c ^ 2 ≤ 1 / c + 6 * (d + 1) ^ 2 / c := by
      rw [div_le_iff₀ (by positivity)]
      have e : (1 / c + 6 * (d + 1) ^ 2 / c) * c ^ 2 = c + 6 * (c * (d + 1)) ^ 2 / c := by field_simp
      rw [e]; gcongr
    have h4 : 2 / c + (1 / c + 6 * (d + 1) ^ 2 / c) ≤ 9 * (d + 1) ^ 2 / c := by
      have e : 2 / c + (1 / c + 6 * (d + 1) ^ 2 / c) = (3 + 6 * (d + 1) ^ 2) / c := by field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg d]) hc0.le
    linarith
  have hF0 : 0 ≤ 2 / c + (kap3 c ^ 2 / 48 + kap2 c D ^ 2) / c ^ 2 := by positivity
  unfold remFactor
  have hmain : 144 / 49 * (2 * D + 3 * c)
      * ((1 + 2 * (c + 1) / D) * ((2 * c + 1) * √((2 * c + 1) * (D + 2 * c + 1)) / c ^ 2))
      * (2 / c + (kap3 c ^ 2 / 48 + kap2 c D ^ 2) / c ^ 2)
      ≤ 144 / 49 * (c * (2 * d + 3)) * ((1 + L) * (3 * (d + 3))) * (9 * (d + 1) ^ 2 / c) := by
    have e : 2 * D + 3 * c = c * (2 * d + 3) := by rw [hDd]; ring
    rw [e]
    gcongr
  have hval : 144 / 49 * (c * (2 * d + 3)) * ((1 + L) * (3 * (d + 3))) * (9 * (d + 1) ^ 2 / c)
      = 144 / 49 * 27 * (1 + L) * ((2 * d + 3) * (d + 3) * (d + 1) ^ 2) := by field_simp; ring
  have hpoly : (2 * d + 3) * (d + 3) * (d + 1) ^ 2 ≤ 9 * (d + 1) ^ 4 := by
    have h1 : (2 * d + 3) * (d + 3) ≤ 9 * (d + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (d + 1)]
  have hL0 : 0 ≤ 1 + L := by linarith
  have h1 : (1 : ℝ) ≤ (1 + L) * (d + 1) ^ 4 := by
    have : 1 ≤ (d + 1) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ 144 / 49 * 27 * (1 + L))]

/-! ### The profile's values at `0` and `1`, and the ground weight -/

/-- `λ_k h_k(0)² ≤ c/π`. -/
theorem rung_zero_sq_le {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    rung c k 0 ^ 2 * lamR c k ≤ c / π := by
  obtain ⟨hg, -, -, -, -, hnorm⟩ := rung_spec h
  have hgc : ContinuousOn (rung c k) (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hψ := Cvs.Prolate.RungSpanBernsteinNikolskii.psi_sq_le (c := c) hgc 0
  rw [hnorm, psi_rung h 0 ⟨by norm_num, by norm_num⟩] at hψ
  rw [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc]
  have e : rung c k 0 ^ 2 * (muR c k ^ 2 * (c / (2 * π))) = (muR c k * rung c k 0) ^ 2 * (c / (2 * π)) := by ring
  rw [e]
  calc (muR c k * rung c k 0) ^ 2 * (c / (2 * π)) ≤ 2 * 1 * (c / (2 * π)) :=
        mul_le_mul_of_nonneg_right hψ (by positivity)
    _ = c / π := by field_simp

/-- `h_0(0)² ≥ ½`. -/
theorem half_le_rung_zero_sq (c : ℝ) : 1 / 2 ≤ rung c 0 0 ^ 2 := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  obtain ⟨hg, hg₁, -, hang, heven, hnorm⟩ := rung_spec h0
  exact Cvs.Prolate.AngularBesselInequality.half_le_ground_sq hg hg₁ hang heven (lev_spec h0).2 hnorm

/-- **The ground weight**: `α_j h_0(0) = (μ_{4j}/μ_0) h_{4j}(0)`. -/
theorem alpha_mul_rung_zero {j : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c (2 * j) χ) :
    Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 0 = muR c (2 * j) / muR c 0 * rung c (2 * j) 0 := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hμ0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 (⟨0, rfl⟩ : Even 0)
  have hr0 : rung c 0 0 ≠ 0 := fun he => by
    have := half_le_rung_zero_sq c; rw [he] at this; norm_num at this
  unfold Cvs.Approximant.DeepIndexSpineSpan.alpha
  rw [Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (psi_rung h), Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (psi_rung h0)]
  field_simp

/-- **The ground weight is `O(√c)`**: for `λ_{4j} ≥ ½`, `α_j² ≤ 4c/π`. -/
theorem alpha_sq_le {j : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c (2 * j) χ) (hlam : 1 / 2 ≤ lamR c (2 * j)) :
    Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 ≤ 4 * c / π := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hμ0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 (⟨0, rfl⟩ : Even 0)
  have hh0 := half_le_rung_zero_sq c
  have hanti := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc h (Nat.zero_le (2 * j))
  have hz := rung_zero_sq_le hc h
  have hk : 0 < c / (2 * π) := by positivity
  have hrat : (muR c (2 * j) / muR c 0) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    have e1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := 2 * j) hc
    have e0 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := 0) hc
    rw [e1, e0] at hanti
    exact le_of_mul_le_mul_right hanti hk
  have e := alpha_mul_rung_zero hc h
  have hA : Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * rung c 0 0 ^ 2 ≤ rung c (2 * j) 0 ^ 2 := by
    rw [← mul_pow, e, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) hrat
  have e2 : 2 * c / π = 2 * (c / π) := by ring
  have hz' : rung c (2 * j) 0 ^ 2 ≤ 2 * c / π := by
    have : rung c (2 * j) 0 ^ 2 * (1 / 2) ≤ c / π := le_trans (mul_le_mul_of_nonneg_left hlam (sq_nonneg _)) hz
    linarith
  have h3 := mul_le_mul_of_nonneg_left hh0 (sq_nonneg (Cvs.Approximant.DeepIndexSpineSpan.alpha c j))
  have e4 : 4 * c / π = 4 * (c / π) := by ring
  linarith

/-- **The profile at `0`**: for `λ_{4j}, λ_0 ≥ ½`, `G_j(0)² ≤ (8c/π)(1 − λ_{4j})²`. -/
theorem profile_zero_sq_le {j : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c (2 * j) χ)
    (hlam : 1 / 2 ≤ lamR c (2 * j)) (hlam0 : 1 / 2 ≤ lamR c 0) :
    (rung c (2 * j) 0 - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 0) ^ 2 ≤ 8 * c / π * (1 - lamR c (2 * j)) ^ 2 := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hμ0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 (⟨0, rfl⟩ : Even 0)
  have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h (⟨j, by ring⟩ : Even (2 * j))
  have hanti := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc h (Nat.zero_le (2 * j))
  have hl01 := Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc
  have hk : 0 < c / (2 * π) := by positivity
  have e1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := 2 * j) hc
  have e0 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := 0) hc
  set μ := muR c (2 * j)
  set μ₀ := muR c 0
  set r := μ / μ₀ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = lamR c (2 * j) / lamR c 0 := by
    rw [e1, e0, hr, div_pow]; field_simp
  have hr1 : r ≤ 1 := by
    have : r ^ 2 ≤ 1 := by rw [hr2, div_le_one (by linarith)]; exact hanti
    nlinarith
  -- `0 ≤ 1 − r ≤ 2(1 − λ)`
  have hgap : 1 - r ≤ 2 * (1 - lamR c (2 * j)) := by
    have h1 : 1 - r ≤ 1 - r ^ 2 := by nlinarith
    have h2 : 1 - r ^ 2 ≤ 2 * (1 - lamR c (2 * j)) := by
      rw [hr2]
      have k : (2 * lamR c (2 * j) - 1) * lamR c 0 ≤ lamR c (2 * j) := by nlinarith
      have := (le_div_iff₀ (by linarith : (0 : ℝ) < lamR c 0)).mpr k
      linarith
    linarith
  have hz := rung_zero_sq_le hc h
  have e2 : 2 * c / π = 2 * (c / π) := by ring
  have hz' : rung c (2 * j) 0 ^ 2 ≤ 2 * c / π := by
    have : rung c (2 * j) 0 ^ 2 * (1 / 2) ≤ c / π := le_trans (mul_le_mul_of_nonneg_left hlam (sq_nonneg _)) hz
    linarith
  have e : rung c (2 * j) 0 - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 0 = (1 - r) * rung c (2 * j) 0 := by
    rw [alpha_mul_rung_zero hc h]; ring
  rw [e, mul_pow]
  have h1r : (1 - r) ^ 2 ≤ (2 * (1 - lamR c (2 * j))) ^ 2 := pow_le_pow_left₀ (by linarith) hgap 2
  calc (1 - r) ^ 2 * rung c (2 * j) 0 ^ 2 ≤ (2 * (1 - lamR c (2 * j))) ^ 2 * (2 * c / π) :=
        mul_le_mul h1r hz' (sq_nonneg _) (sq_nonneg _)
    _ = 8 * c / π * (1 - lamR c (2 * j)) ^ 2 := by ring

/-! ### The exterior law in two terms -/

/-- The arithmetic of `a²(G(1)² + G(0)²)`: with `ac = 2π`, `a ≤ 1 ≤ c`, `α² ≤ 4c/π`,
`h(1)² ≤ (144/49)c(2d + 3)ω`, `h₀(1)² ≤ (144/49)·5c²ω₀`, `G(1)² ≤ 2h(1)² + 2α²h₀(1)²` and `G(0)² ≤ (8c/π)ω²`,
`a²(G(1)² + G(0)²) ≤ 128aω(d + 1) + 60ω₀(c + 1)⁴`. -/
theorem arith_edge {a c d ω ω₀ α2 r1 r01 G1s G0s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc1 : 1 ≤ c)
    (hac : a * c = 2 * π) (hd0 : 0 ≤ d) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hω0 : 0 ≤ ω₀) (hα0 : 0 ≤ α2)
    (hα2 : α2 ≤ 4 * c / π) (hr1 : r1 ≤ 2 * (72 / 49 * (c * (2 * d + 3)) * ω)) (hr010 : 0 ≤ r01)
    (hr01 : r01 ≤ 2 * (72 / 49 * (5 * c ^ 2) * ω₀)) (hG1 : G1s ≤ 2 * r1 + 2 * (α2 * r01))
    (hG0 : G0s ≤ 8 * c / π * ω ^ 2) :
    a ^ 2 * (G1s + G0s) ≤ 128 * (a * ω * (d + 1)) + 60 * (ω₀ * (c + 1) ^ 4) := by
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi4 : π < 3.15 := Real.pi_lt_d2
  have hc0 : 0 < c := by linarith
  have ha2c : a ^ 2 * c = 2 * π * a := by rw [sq, mul_assoc, hac]; ring
  have ha2 : a ^ 2 ≤ 1 := by nlinarith only [ha0, ha1]
  -- `a²·2h(1)² ≤ 112 aω(d + 1)`
  have k1 : a ^ 2 * (2 * r1) ≤ 112 * (a * ω * (d + 1)) := by
    have h1 : a ^ 2 * (2 * r1) ≤ a ^ 2 * (4 * (72 / 49 * (c * (2 * d + 3)) * ω)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hr1]) (sq_nonneg a)
    have e : a ^ 2 * (4 * (72 / 49 * (c * (2 * d + 3)) * ω)) = 576 / 49 * π * (2 * d + 3) * (a * ω) := by
      have : a ^ 2 * (4 * (72 / 49 * (c * (2 * d + 3)) * ω)) = 288 / 49 * (a ^ 2 * c) * (2 * d + 3) * ω := by ring
      rw [this, ha2c]; ring
    have h2 : 576 / 49 * π * (2 * d + 3) ≤ 112 * (d + 1) := by nlinarith only [hpi4, hd0, hpi3]
    have haω : 0 ≤ a * ω := mul_nonneg ha0 hω
    have h3 := mul_le_mul_of_nonneg_right h2 haω
    rw [e] at h1
    linarith only [h1, h3]
  -- `a²·2α²h₀(1)² ≤ 40c³ω₀`
  have k2 : a ^ 2 * (2 * (α2 * r01)) ≤ 40 * c ^ 3 * ω₀ := by
    have h1 : α2 * r01 ≤ 4 * c / π * (2 * (72 / 49 * (5 * c ^ 2) * ω₀)) :=
      mul_le_mul hα2 hr01 hr010 (by positivity)
    have h2 : 4 * c / π * (2 * (72 / 49 * (5 * c ^ 2) * ω₀)) ≤ 20 * c ^ 3 * ω₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : 0 ≤ c ^ 3 * ω₀ := by positivity
      nlinarith only [this, hpi3]
    have h3 : 0 ≤ 2 * (α2 * r01) := by positivity
    calc a ^ 2 * (2 * (α2 * r01)) ≤ 1 * (2 * (20 * c ^ 3 * ω₀)) :=
          mul_le_mul ha2 (by linarith only [h1, h2]) h3 zero_le_one
      _ = 40 * c ^ 3 * ω₀ := by ring
  -- `a²G(0)² ≤ 16aω`
  have k3 : a ^ 2 * G0s ≤ 16 * (a * ω * (d + 1)) := by
    have hω2 : ω ^ 2 ≤ ω := by nlinarith only [hω, hω1]
    have h1 : a ^ 2 * G0s ≤ a ^ 2 * (8 * c / π * ω ^ 2) := mul_le_mul_of_nonneg_left hG0 (sq_nonneg a)
    have e : a ^ 2 * (8 * c / π * ω ^ 2) = 16 * a * ω ^ 2 := by
      have : a ^ 2 * (8 * c / π * ω ^ 2) = 8 / π * (a ^ 2 * c) * ω ^ 2 := by ring
      rw [this, ha2c]; field_simp; ring
    have h2 : 16 * a * ω ^ 2 ≤ 16 * (a * ω * (d + 1)) := by
      have : a * ω ^ 2 ≤ a * ω := mul_le_mul_of_nonneg_left hω2 ha0
      have : a * ω ≤ a * ω * (d + 1) := le_mul_of_one_le_right (mul_nonneg ha0 hω) (by linarith only [hd0])
      linarith
    linarith only [h1, e, h2]
  have k4 : 40 * c ^ 3 * ω₀ ≤ 60 * (ω₀ * (c + 1) ^ 4) := by
    have h1 : c ^ 3 ≤ (c + 1) ^ 4 := by
      have := pow_le_pow_left₀ hc0.le (by linarith only : c ≤ c + 1) 3
      have h2 : (c + 1) ^ 3 ≤ (c + 1) ^ 4 := pow_le_pow_right₀ (by linarith only [hc0]) (by norm_num)
      linarith
    have h3 := mul_le_mul_of_nonneg_left h1 hω0
    have h4 : 0 ≤ ω₀ * (c + 1) ^ 4 := by positivity
    linarith only [h3, h4]
  have hG1' : a ^ 2 * G1s ≤ a ^ 2 * (2 * r1) + a ^ 2 * (2 * (α2 * r01)) := by
    have := mul_le_mul_of_nonneg_left hG1 (sq_nonneg a)
    linarith only [this]
  have e : a ^ 2 * (G1s + G0s) = a ^ 2 * G1s + a ^ 2 * G0s := by ring
  rw [e]
  linarith only [hG1', k1, k2, k3, k4]

/-- The arithmetic of the Poisson remainder: with `π/c = a/2`, `α² ≤ 4c/π`, `R ≤ 728(1 + L)(d + 1)⁴` and
`R₀ ≤ 728(1 + L)(c + 1)⁴`, `2ζ²[2(π/c)ωR + 2α²(π/c)ω₀R₀] ≤ 1456ζ²aω(1 + L)(d + 1)⁴
+ 11648ζ²ω₀(1 + L)(c + 1)⁴`. -/
theorem arith_rem {a c d ω ω₀ α2 R R₀ L ζ : ℝ} (ha0 : 0 ≤ a) (hc0 : 0 < c) (hπc : π / c = a / 2)
    (hω : 0 ≤ ω) (hω0 : 0 ≤ ω₀) (hα2 : α2 ≤ 4 * c / π) (hR0 : 0 ≤ R₀)
    (hR : R ≤ 728 * (1 + L) * (d + 1) ^ 4) (hR₀ : R₀ ≤ 728 * (1 + L) * (c + 1) ^ 4) :
    2 * (ζ ^ 2 * (2 * (π / c * ω * R) + 2 * α2 * (π / c * ω₀ * R₀)))
      ≤ 1456 * ζ ^ 2 * (a * ω * ((1 + L) * (d + 1) ^ 4)) + 11648 * ζ ^ 2 * (ω₀ * ((1 + L) * (c + 1) ^ 4)) := by
  have hζ2 : 0 ≤ ζ ^ 2 := sq_nonneg ζ
  rw [hπc]
  have m1 : a / 2 * ω * R ≤ 364 * (a * ω * ((1 + L) * (d + 1) ^ 4)) := by
    have := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ a / 2 * ω)
    linarith only [this]
  have hac : c * a = 2 * π := by
    have := hπc; field_simp at this; linarith
  have m2 : α2 * (a / 2 * ω₀ * R₀) ≤ 2912 * (ω₀ * ((1 + L) * (c + 1) ^ 4)) := by
    have h1 : α2 * (a / 2 * ω₀ * R₀) ≤ 4 * c / π * (a / 2 * ω₀ * (728 * (1 + L) * (c + 1) ^ 4)) :=
      mul_le_mul hα2 (mul_le_mul_of_nonneg_left hR₀ (by positivity)) (by positivity) (by positivity)
    have e : 4 * c / π * (a / 2 * ω₀ * (728 * (1 + L) * (c + 1) ^ 4))
        = 2912 * (ω₀ * ((1 + L) * (c + 1) ^ 4)) := by
      have hπ : π ≠ 0 := Real.pi_ne_zero
      field_simp
      linear_combination (2912 * ω₀ * (1 + L)) * hac
    linarith only [h1, e]
  have e : 2 * (ζ ^ 2 * (2 * (a / 2 * ω * R) + 2 * α2 * (a / 2 * ω₀ * R₀)))
      = 4 * (ζ ^ 2 * (a / 2 * ω * R)) + 4 * (ζ ^ 2 * (α2 * (a / 2 * ω₀ * R₀))) := by ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left m1 hζ2
  have h2 := mul_le_mul_of_nonneg_left m2 hζ2
  linarith only [h1, h2]

set_option maxHeartbeats 1000000 in
/-- **The exterior law in two terms**: at `c = 2πx ≥ 80`, `a = 1/x`, `j < x`, `σ < 1`, with `ω = 1 − λ_{4j}`,
`ω₀ = 1 − λ_0`, `d = D_j/c`, `L = log c`, `Ext_{G_j}(σ) ≤ aω(64/(1 − σ) + 1456ζ(3/2)²)(1 + L)(d + 1)⁴
+ ω₀(30/(1 − σ) + 11648ζ(3/2)²)(1 + L)(c + 1)⁴`. -/
theorem extInt_profile_le_two (x : ℕ) (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) {σ : ℝ} (hσ : σ < 1) :
    Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x)
        (fun s => rung (2 * π * x) (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 s) σ
      ≤ 1 / x * (1 - lamR (2 * π * x) (2 * j))
          * ((64 / (1 - σ) + 1456 * Cvs.Route.Visibility.SawtoothPlancherelBounds.zeta32 ^ 2) * (1 + Real.log (2 * π * x))
            * (((2 * π * x) ^ 2 - lev (2 * π * x) (2 * j)) / (2 * π * x) + 1) ^ 4)
        + (1 - lamR (2 * π * x) 0) * ((30 / (1 - σ) + 11648 * Cvs.Route.Visibility.SawtoothPlancherelBounds.zeta32 ^ 2)
          * (1 + Real.log (2 * π * x)) * (2 * π * x + 1) ^ 4) := by
  have hmain := extInt_profile_le x hx hj hσ
  obtain ⟨hex, hσj⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  obtain ⟨hex0, hσ0⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx (j := 0) (by omega)
  simp only [mul_zero] at hex0 hσ0
  have hlam := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hlam0 : 1 / 2 ≤ lamR (2 * π * x) 0 := by
    simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (j := 0) (by omega)
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hx; linarith
    · exact h
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  set c := 2 * π * (x : ℝ) with hcdef
  set a := 1 / (x : ℝ) with hadef
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [hadef, div_le_one (by linarith)]; exact hx1
  have hac : a * c = 2 * π := by rw [hadef, hcdef]; field_simp
  have hπc : π / c = a / 2 := by rw [hadef, hcdef]; field_simp
  set L := Real.log c with hL
  have hL4 : 4 ≤ L := Cvs.Prolate.EvenLevelIndexLemma.four_le_log hx
  set ζ := Cvs.Route.Visibility.SawtoothPlancherelBounds.zeta32 with hζ
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha c j with hα
  set lam := lamR c (2 * j) with hlamdef
  set lam0 := lamR c 0 with hlam0def
  set D := c ^ 2 - lev c (2 * j) with hD
  set D₀ := c ^ 2 - lev c 0 with hD₀
  have hχ0 : 0 ≤ lev c (2 * j) := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (lev_spec hex).1
  have hχ00 : 0 ≤ lev c 0 := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (lev_spec hex0).1
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < c)
  have hχc : lev c (2 * j) < c ^ 2 := by linarith
  have hχc0 : lev c 0 < c ^ 2 := by linarith
  have hω0 : 0 ≤ 1 - lam0 := by linarith [Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0]
  have hω : 0 ≤ 1 - lam := by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex]
  have hL0 : 0 ≤ 1 + L := by linarith
  set d := D / c with hd
  have hd0 : 0 ≤ d := div_nonneg (by linarith) hc0.le
  have hDd : D = c * d := by rw [hd]; field_simp
  have hd₀c : D₀ / c ≤ c := by rw [div_le_iff₀ hc0]; nlinarith only [hχ00]
  -- the inputs
  have hrem := remFactor_le hx hσj (by linarith : D ≤ c ^ 2)
  have hrem0 := remFactor_le hx hσ0 (by linarith : D₀ ≤ c ^ 2)
  have hremp0 : 0 ≤ remFactor c D₀ := by unfold remFactor; have := kap3_nonneg c; positivity
  have hrem0' : remFactor c D₀ ≤ 728 * (1 + L) * (c + 1) ^ 4 :=
    hrem0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 4) (by positivity))
  have hα2 : α ^ 2 ≤ 4 * c / π := alpha_sq_le hc0 hex hlam
  have hG0b := profile_zero_sq_le hc0 hex hlam hlam0
  have hh1 : rung c (2 * j) 1 ^ 2 ≤ 2 * (72 / 49 * (c * (2 * d + 3)) * (1 - lam)) := by
    have h := Cvs.Prolate.Envelope.RungExteriorLaw.edge_sq_le hc1 hex hχc
    have h2 := mul_le_mul_of_nonneg_left hlam (sq_nonneg (rung c (2 * j) 1))
    have e : 2 * (c ^ 2 - lev c (2 * j)) + 3 * c = c * (2 * d + 3) := by rw [← hD, hDd]; ring
    rw [e] at h
    linarith only [h, h2]
  have hh01 : rung c 0 1 ^ 2 ≤ 2 * (72 / 49 * (5 * c ^ 2) * (1 - lam0)) := by
    have h := Cvs.Prolate.Envelope.RungExteriorLaw.edge_sq_le hc1 hex0 hχc0
    have h2 := mul_le_mul_of_nonneg_left hlam0 (sq_nonneg (rung c 0 1))
    have hb : 2 * (c ^ 2 - lev c 0) + 3 * c ≤ 5 * c ^ 2 := by nlinarith only [hχ00, hc1]
    have h3 : 72 / 49 * (2 * (c ^ 2 - lev c 0) + 3 * c) * (1 - lam0) ≤ 72 / 49 * (5 * c ^ 2) * (1 - lam0) :=
      mul_le_mul_of_nonneg_right (by linarith only [hb]) hω0
    linarith only [h, h2, h3]
  set G1 := rung c (2 * j) 1 - α * rung c 0 1 with hG1
  set G0 := rung c (2 * j) 0 - α * rung c 0 0 with hG0
  have hG1b : G1 ^ 2 ≤ 2 * rung c (2 * j) 1 ^ 2 + 2 * (α ^ 2 * rung c 0 1 ^ 2) := by
    rw [hG1]; nlinarith only [sq_nonneg (rung c (2 * j) 1 + α * rung c 0 1)]
  have hX := arith_edge ha0.le ha1 hc1 hac hd0 hω (by linarith) hω0 (sq_nonneg α) hα2 hh1 (sq_nonneg _) hh01
    hG1b hG0b
  set M := 2 * (π / c * (1 - lam) * remFactor c D) + 2 * α ^ 2 * (π / c * (1 - lam0) * remFactor c D₀) with hM
  have hY := arith_rem (ζ := ζ) ha0.le hc0 hπc hω hω0 hα2 hremp0 hrem hrem0'
  have hM0 : 0 ≤ M := by
    have : 0 ≤ remFactor c D := by unfold remFactor; have := kap3_nonneg c; positivity
    positivity
  -- `Ext ≤ 2A² + 2ζ²M`
  set A := a * (|G1| + |G0|) / (2 * √(2 * (1 - σ))) with hA
  have h1σ : 0 < 1 - σ := by linarith
  have hs2 : √(2 * (1 - σ)) ^ 2 = 2 * (1 - σ) := Real.sq_sqrt (by linarith)
  have hsσ : 0 < √(2 * (1 - σ)) := Real.sqrt_pos.mpr (by linarith)
  have hstep1 : (A + ζ * √M) ^ 2 ≤ 2 * A ^ 2 + 2 * (ζ ^ 2 * M) := by
    have e : (ζ * √M) ^ 2 = ζ ^ 2 * M := by rw [mul_pow, Real.sq_sqrt hM0]
    nlinarith only [sq_nonneg (A - ζ * √M), e]
  have hA2 : 2 * A ^ 2 ≤ a ^ 2 * (G1 ^ 2 + G0 ^ 2) / (2 * (1 - σ)) := by
    have hab : (|G1| + |G0|) ^ 2 ≤ 2 * (G1 ^ 2 + G0 ^ 2) := by
      nlinarith only [sq_nonneg (|G1| - |G0|), sq_abs G1, sq_abs G0]
    have e : 2 * A ^ 2 = a ^ 2 * (|G1| + |G0|) ^ 2 / (4 * (1 - σ)) := by
      rw [hA, div_pow, mul_pow, mul_pow, hs2]; field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hab (sq_nonneg a)
    nlinarith only [this, h1σ, sq_nonneg a, sq_nonneg G1, sq_nonneg G0]
  have hfin : Cvs.Route.Visibility.ExteriorTransformPointBound.extInt a (fun s => rung c (2 * j) s - α * rung c 0 s) σ
      ≤ 2 * A ^ 2 + 2 * (ζ ^ 2 * M) := hmain.trans hstep1
  refine hfin.trans ?_
  have hz1 : a ^ 2 * (G1 ^ 2 + G0 ^ 2) / (2 * (1 - σ))
      ≤ a * (1 - lam) * (64 / (1 - σ) * ((1 + L) * (d + 1) ^ 4))
        + (1 - lam0) * (30 / (1 - σ) * ((1 + L) * (c + 1) ^ 4)) := by
    have hdL : d + 1 ≤ (1 + L) * (d + 1) ^ 4 := by
      have h1 : d + 1 ≤ (d + 1) ^ 4 := by
        have := pow_le_pow_right₀ (by linarith only [hd0] : (1 : ℝ) ≤ d + 1) (by norm_num : 1 ≤ 4)
        simpa using this
      nlinarith only [h1, hL4, pow_nonneg (by linarith only [hd0] : (0 : ℝ) ≤ d + 1) 4]
    have hcL : (c + 1) ^ 4 ≤ (1 + L) * (c + 1) ^ 4 := by
      nlinarith only [hL4, pow_nonneg (by linarith only [hc0] : (0 : ℝ) ≤ c + 1) 4]
    have h2 : a ^ 2 * (G1 ^ 2 + G0 ^ 2) / (2 * (1 - σ))
        ≤ (128 * (a * (1 - lam) * (d + 1)) + 60 * ((1 - lam0) * (c + 1) ^ 4)) / (2 * (1 - σ)) :=
      div_le_div_of_nonneg_right hX (by linarith)
    have e : (128 * (a * (1 - lam) * (d + 1)) + 60 * ((1 - lam0) * (c + 1) ^ 4)) / (2 * (1 - σ))
        = 64 / (1 - σ) * (a * (1 - lam) * (d + 1)) + 30 / (1 - σ) * ((1 - lam0) * (c + 1) ^ 4) := by
      field_simp; ring
    have hq1 : 0 ≤ 64 / (1 - σ) := by positivity
    have hq2 : 0 ≤ 30 / (1 - σ) := by positivity
    have haω : 0 ≤ a * (1 - lam) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdL haω) hq1
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcL hω0) hq2
    have e2 : a * (1 - lam) * (64 / (1 - σ) * ((1 + L) * (d + 1) ^ 4))
        = 64 / (1 - σ) * (a * (1 - lam) * ((1 + L) * (d + 1) ^ 4)) := by ring
    have e3 : (1 - lam0) * (30 / (1 - σ) * ((1 + L) * (c + 1) ^ 4))
        = 30 / (1 - σ) * ((1 - lam0) * ((1 + L) * (c + 1) ^ 4)) := by ring
    rw [e2, e3]
    linarith only [h2, e, h3, h4]
  have e' : a * (1 - lam) * ((64 / (1 - σ) + 1456 * ζ ^ 2) * (1 + L) * (d + 1) ^ 4)
      + (1 - lam0) * ((30 / (1 - σ) + 11648 * ζ ^ 2) * (1 + L) * (c + 1) ^ 4)
      = a * (1 - lam) * (64 / (1 - σ) * ((1 + L) * (d + 1) ^ 4))
        + (1 - lam0) * (30 / (1 - σ) * ((1 + L) * (c + 1) ^ 4))
        + (1456 * ζ ^ 2 * (a * (1 - lam) * ((1 + L) * (d + 1) ^ 4))
          + 11648 * ζ ^ 2 * ((1 - lam0) * ((1 + L) * (c + 1) ^ 4))) := by ring
  rw [e']
  linarith only [hA2, hz1, hY]

/-! ### The subpolynomial form (Corollary PR_σ) -/

open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly subPoly_const subPoly_log)

/-- Powers of an eventually nonnegative subpolynomial function are subpolynomial. -/
theorem subPoly_pow {f : ℕ → ℝ} (hf : SubPoly f) (h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ f x) (n : ℕ) :
    SubPoly fun x => f x ^ n := by
  induction n with
  | zero => simpa using subPoly_const 1
  | succ n ih =>
    simpa [pow_succ] using Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul ih hf (h0.mono fun x hx => pow_nonneg hx n) h0

/-- `x ↦ 1 + 2 log(Kx)` is subpolynomial for `K > 0`. -/
theorem subPoly_one_add_two_log {K : ℝ} (hK : 0 < K) : SubPoly fun x => 1 + 2 * Real.log (K * x) := by
  have h2 : SubPoly fun x : ℕ => 2 * Real.log x :=
    Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul (subPoly_const 2) subPoly_log (Eventually.of_forall fun _ => by norm_num)
      ((eventually_ge_atTop 1).mono fun x hx => Real.log_nonneg (by exact_mod_cast hx))
  refine (Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.add (subPoly_const (1 + 2 * Real.log K)) h2).mono ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hx
  rw [Real.log_mul hK.ne' hx0.ne']; ring_nf; rfl

/-- **The rung term against its depth**: for `c ≥ 80`, `λ_k ≥ ½`, `4c/log c ≤ D = c² − χ_k`, `d = D/c` and `η > 0`,
`(1 − λ_k)^η(d + 1)⁴ ≤ 16((1 + 2 log(K₁c))⁴ + 4!(2/η)⁴e^{η/2}) + 1296`, `K₁ = (33/20)e⁵`. -/
theorem rung_term_le {k : ℕ} {η : ℝ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hη0 : 0 < η)
    (hlam : 1 / 2 ≤ lamR c k) (hσ : 4 * c / Real.log c ≤ c ^ 2 - lev c k) :
    (1 - lamR c k) ^ η * ((c ^ 2 - lev c k) / c + 1) ^ 4
      ≤ 16 * ((1 + 2 * Real.log (33 / 20 * Real.exp 5 * c)) ^ 4
        + (Nat.factorial 4 : ℝ) * (2 / η) ^ 4 * Real.exp (η / 2)) + 1296 := by
  have hc0 : 0 < c := by linarith
  set K₁ := 33 / 20 * Real.exp 5 with hK₁
  have hK₁1 : 1 ≤ K₁ := by
    have h2 : (20 : ℝ) / 33 ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
    rw [hK₁]; linarith
  set ω := 1 - lamR c k with hωdef
  have hω : 0 ≤ ω := by rw [hωdef]; linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h]
  have hω1 : ω ≤ 1 := by rw [hωdef]; linarith
  set D := c ^ 2 - lev c k with hD
  have hD0 : 0 < D := lt_of_lt_of_le (by have := Cvs.Prolate.EvenLevelIndexLemma.four_le_log hc; positivity) hσ
  set d := D / c with hd
  have hd0 : 0 ≤ d := by positivity
  set B := (Nat.factorial 4 : ℝ) * (2 / η) ^ 4 * Real.exp (η / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have hℓ1 : 0 ≤ 1 + 2 * Real.log (K₁ * c) := by
    have : 1 ≤ K₁ * c := by nlinarith
    linarith [Real.log_nonneg this]
  have hℓ4 : 0 ≤ (1 + 2 * Real.log (K₁ * c)) ^ 4 := pow_nonneg hℓ1 4
  have hωη0 : 0 ≤ ω ^ η := Real.rpow_nonneg hω _
  by_cases h5 : 5 * c ≤ D
  · have hexp := one_sub_lamR_le_exp hc h h5
    set t := π * D / (4 * c) with ht
    have ht0 : 0 ≤ t := by positivity
    have hK1c : 1 ≤ K₁ * c := by nlinarith
    have hkey := one_add_pow_mul_rpow_le 4 ht0 hω hω1 hK1c hη0 hexp
    have hdt : d + 1 ≤ 2 * (1 + t) := by
      have e : t = π / 4 * d := by rw [ht, hd]; field_simp
      rw [e]; nlinarith [Real.pi_gt_three]
    have hdt4 : (d + 1) ^ 4 ≤ 16 * (1 + t) ^ 4 := by
      have := pow_le_pow_left₀ (by linarith) hdt 4
      linarith [show (2 * (1 + t)) ^ 4 = 16 * (1 + t) ^ 4 by ring]
    calc ω ^ η * (d + 1) ^ 4 ≤ ω ^ η * (16 * (1 + t) ^ 4) := mul_le_mul_of_nonneg_left hdt4 hωη0
      _ = 16 * ((1 + t) ^ 4 * ω ^ η) := by ring
      _ ≤ 16 * ((1 + 2 * Real.log (K₁ * c)) ^ 4 + B) := by linarith
      _ ≤ _ := by linarith
  · push Not at h5
    have hd5 : d + 1 ≤ 6 := by
      have : d < 5 := by rw [hd, div_lt_iff₀ hc0]; linarith
      linarith
    have h1 : (d + 1) ^ 4 ≤ 1296 := by
      have := pow_le_pow_left₀ (by linarith) hd5 4
      norm_num at this ⊢; linarith
    have hωη1 : ω ^ η ≤ 1 := Real.rpow_le_one hω hω1 hη0.le
    calc ω ^ η * (d + 1) ^ 4 ≤ 1 * 1296 := mul_le_mul hωη1 h1 (by positivity) zero_le_one
      _ ≤ _ := by linarith

/-- **The ground term is exponentially small**: for `c ≥ 80`, `0 < η ≤ 1`, `C ≥ 0`,
`(1 − λ_0)^η·C(1 + log c)(c + 1)⁴ ≤ 16CK₁c⁶e^{−(ηπ/6)c}`, `K₁ = (33/20)e⁵`. -/
theorem ground_term_le {η C : ℝ} (hc : 80 ≤ c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hC : 0 ≤ C) :
    (1 - lamR c 0) ^ η * (C * (1 + Real.log c) * (c + 1) ^ 4)
      ≤ 16 * C * (33 / 20 * Real.exp 5) * (c ^ 6 * Real.exp (-(η * π / 6 * c))) := by
  have hc0 : 0 < c := by linarith
  set K₁ := 33 / 20 * Real.exp 5 with hK₁
  have hK₁1 : 1 ≤ K₁ := by
    have h2 : (20 : ℝ) / 33 ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
    rw [hK₁]; linarith
  have hex0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  set ω₀ := 1 - lamR c 0 with hω₀def
  have hω0 : 0 ≤ ω₀ := by rw [hω₀def]; linarith [Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0]
  have hlev0 : lev c 0 ≤ c ^ 2 / 3 := by
    rw [Cvs.Prolate.EvenRungsByIndex.lev_zero]; exact Cvs.Prolate.EvenSpectrumGroundLevel.groundLevel_le c
  have hD0 : 5 * c ≤ c ^ 2 - lev c 0 := by nlinarith
  have hexp0 := one_sub_lamR_le_exp hc hex0 hD0
  have hexp0' : ω₀ ≤ K₁ * c * Real.exp (-(π * c / 6)) := by
    refine hexp0.trans ?_
    have : π * c / 6 ≤ π * (c ^ 2 - lev c 0) / (4 * c) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith [Real.pi_pos]
    gcongr
  have hω0η : ω₀ ^ η ≤ (K₁ * c * Real.exp (-(π * c / 6))) ^ η := Real.rpow_le_rpow hω0 hexp0' hη0.le
  have hK1c : 1 ≤ K₁ * c := by nlinarith
  have hrp : (K₁ * c * Real.exp (-(π * c / 6))) ^ η ≤ K₁ * c * Real.exp (-(η * π / 6 * c)) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
    have h1 : (K₁ * c) ^ η ≤ K₁ * c := by
      calc (K₁ * c) ^ η ≤ (K₁ * c) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1c hη1
        _ = K₁ * c := Real.rpow_one _
    have h2 : Real.exp (-(π * c / 6) * η) = Real.exp (-(η * π / 6 * c)) := by ring_nf
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hLc : 1 + Real.log c ≤ c := by have := Real.log_le_sub_one_of_pos hc0; linarith
  have hc1' : (c + 1) ^ 4 ≤ 16 * c ^ 4 := by
    have := pow_le_pow_left₀ (by linarith) (by linarith : c + 1 ≤ 2 * c) 4
    linarith [show (2 * c) ^ 4 = 16 * c ^ 4 by ring]
  have hL0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ c)]
  calc ω₀ ^ η * (C * (1 + Real.log c) * (c + 1) ^ 4)
      ≤ K₁ * c * Real.exp (-(η * π / 6 * c)) * (C * c * (16 * c ^ 4)) :=
        mul_le_mul (hω0η.trans hrp) (mul_le_mul (mul_le_mul_of_nonneg_left hLc hC) hc1' (by positivity)
          (by positivity)) (by positivity) (by positivity)
    _ = 16 * C * K₁ * (c ^ 6 * Real.exp (-(η * π / 6 * c))) := by ring

/-- The arithmetic of the ground term: for `c > 0`, `ca = 2π`, `K ≥ 0` and `c⁷E ≤ 1/(K + 1)`,
`K·c⁶E ≤ a`. -/
theorem arith_ground {c a K E : ℝ} (hc0 : 0 < c) (hca : c * a = 2 * π) (hK : 0 ≤ K)
    (h : c ^ 7 * E ≤ 1 / (K + 1)) : K * (c ^ 6 * E) ≤ a := by
  have e : c ^ 6 * E = c ^ 7 * E / c := by field_simp
  rw [e]
  have h2 : K * (c ^ 7 * E / c) ≤ 1 / c := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hc0]
    calc K * (c ^ 7 * E) ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left h hK
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  have h3 : 1 / c ≤ a := by
    have ha : a = 2 * π / c := by field_simp; linarith
    rw [ha]; exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_gt_three]) hc0.le
  linarith

/-- `Cℓ(16(ℓ⁴ + B) + 1296) + 1 ≤ (C(16 + 16B + 1296) + 1)ℓ⁵` for `ℓ ≥ 1`, `C, B ≥ 0`. -/
theorem arith_poly {C B ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    C * ℓ * (16 * (ℓ ^ 4 + B) + 1296) + 1 ≤ (C * (16 + 16 * B + 1296) + 1) * ℓ ^ 5 := by
  have h5 : 1 ≤ ℓ ^ 5 := one_le_pow₀ hℓ
  have hl5 : ℓ ≤ ℓ ^ 5 := by
    have := pow_le_pow_right₀ hℓ (by norm_num : 1 ≤ 5); simpa using this
  have k : C * (16 * B + 1296) * ℓ ≤ C * (16 * B + 1296) * ℓ ^ 5 :=
    mul_le_mul_of_nonneg_left hl5 (by positivity)
  have e1 : C * ℓ * (16 * (ℓ ^ 4 + B) + 1296) = 16 * C * ℓ ^ 5 + C * (16 * B + 1296) * ℓ := by ring
  have e2 : (C * (16 + 16 * B + 1296) + 1) * ℓ ^ 5 = 16 * C * ℓ ^ 5 + C * (16 * B + 1296) * ℓ ^ 5 + ℓ ^ 5 := by
    ring
  rw [e1, e2]
  linarith only [k, h5]

set_option maxHeartbeats 1000000 in
/-- **The exterior law with subpolynomial loss (Corollary PR_σ)**: for `σ < 1` and `0 < η < 1`, for every `ε > 0`,
eventually in `x`, every `j < x` has `Ext_{G_j}(σ) ≤ x^ε·a·(1 − λ_{4j})^{1−η}`, `a = 1/x`, `c = 2πx`. -/
theorem extInt_profile_le_rpow {σ η : ℝ} (hσ : σ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j < x,
      Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x)
          (fun s => rung (2 * π * x) (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 s) σ
        ≤ (x : ℝ) ^ ε * (1 / x) * (1 - lamR (2 * π * x) (2 * j)) ^ (1 - η) := by
  intro ε hε
  set C₁ := 64 / (1 - σ) + 1456 * Cvs.Route.Visibility.SawtoothPlancherelBounds.zeta32 ^ 2 with hC₁
  set C₀ := 30 / (1 - σ) + 11648 * Cvs.Route.Visibility.SawtoothPlancherelBounds.zeta32 ^ 2 with hC₀
  set K₁ := 33 / 20 * Real.exp 5 with hK₁
  set B := (Nat.factorial 4 : ℝ) * (2 / η) ^ 4 * Real.exp (η / 2) with hB
  have h1σ : 0 < 1 - σ := by linarith
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hK₁1 : 1 ≤ K₁ := by
    have h2 : (20 : ℝ) / 33 ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
    rw [hK₁]; linarith
  have hB0 : 0 ≤ B := by positivity
  set Ĉ := C₁ * (16 + 16 * B + 1296) + 1 with hĈ
  -- the subpolynomial factor `Ĉℓ⁵`, `ℓ = 1 + 2 log(K₁·2πx)`
  have hℓ := subPoly_one_add_two_log (K := K₁ * (2 * π)) (by positivity)
  have hℓ0 : ∀ᶠ x : ℕ in atTop, 1 ≤ 1 + 2 * Real.log (K₁ * (2 * π) * x) := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have : 1 ≤ K₁ * (2 * π) * x := by
      have := Real.pi_gt_three
      nlinarith [mul_le_mul hK₁1 hx1 zero_le_one (by linarith)]
    linarith [Real.log_nonneg this]
  have hQ : SubPoly fun x => Ĉ * (1 + 2 * Real.log (K₁ * (2 * π) * x)) ^ 5 :=
    Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul (subPoly_const Ĉ) (subPoly_pow hℓ (hℓ0.mono fun _ h => by linarith) 5)
      (Eventually.of_forall fun _ => by positivity) (hℓ0.mono fun _ h => pow_nonneg (by linarith) 5)
  -- the decay of the ground term
  set κ := η * π / 6 with hκ
  have hκ0 : 0 < κ := by positivity
  have hdecay : ∀ᶠ x : ℕ in atTop,
      (2 * π * x) ^ 7 * Real.exp (-(κ * (2 * π * x))) ≤ 1 / (16 * C₀ * K₁ + 1) := by
    have h1 : Tendsto (fun x : ℕ => κ * (2 * π * x)) atTop atTop :=
      Tendsto.const_mul_atTop hκ0 (Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop)
    have h2 := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 7).comp h1).div_const (κ ^ 7)
    rw [zero_div] at h2
    have hpos : (0 : ℝ) < 1 / (16 * C₀ * K₁ + 1) := by positivity
    filter_upwards [h2.eventually (ge_mem_nhds hpos)] with x hx
    have e : (κ * (2 * π * x)) ^ 7 * Real.exp (-(κ * (2 * π * x))) / κ ^ 7
        = (2 * π * x) ^ 7 * Real.exp (-(κ * (2 * π * x))) := by
      rw [mul_pow]; field_simp
    simp only [Function.comp] at hx
    rwa [e] at hx
  filter_upwards [eventually_ge_atTop 13, hQ ε hε, hdecay, hℓ0] with x hx13 hQx hdx hℓx j hj
  have hx : 80 ≤ 2 * π * (x : ℝ) := by
    have : (13 : ℝ) ≤ x := by exact_mod_cast hx13
    nlinarith [Real.pi_gt_d2]
  have htwo := extInt_profile_le_two x hx hj hσ
  obtain ⟨hex, hσj⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  have hlam := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hrung := rung_term_le hx hex hη0 hlam hσj
  have hground := ground_term_le (C := C₀) hx hη0 hη1.le hC₀0
  -- abstract the remaining arithmetic
  set c := 2 * π * (x : ℝ) with hcdef
  set a := 1 / (x : ℝ) with hadef
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by positivity
  have hca : c * a = 2 * π := by rw [hcdef, hadef]; field_simp
  set ω := 1 - lamR c (2 * j) with hωdef
  set ω₀ := 1 - lamR c 0 with hω₀def
  have hω : 0 ≤ ω := by rw [hωdef]; linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex]
  have hω0 : 0 ≤ ω₀ := by rw [hω₀def]; linarith [Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0]
  have hω0ω : ω₀ ≤ ω := by
    have := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc0 hex (Nat.zero_le (2 * j))
    rw [hωdef, hω₀def]; linarith
  have hsplit : ω = ω ^ (1 - η) * ω ^ η := by
    rw [← Real.rpow_add' hω (by norm_num), sub_add_cancel, Real.rpow_one]
  have hsplit0 : ω₀ = ω₀ ^ (1 - η) * ω₀ ^ η := by
    rw [← Real.rpow_add' hω0 (by norm_num), sub_add_cancel, Real.rpow_one]
  have hωr0 : 0 ≤ ω ^ (1 - η) := Real.rpow_nonneg hω _
  set ℓ := 1 + 2 * Real.log (K₁ * (2 * π) * x) with hℓdef
  have hℓc : Real.log (33 / 20 * Real.exp 5 * c) = Real.log (K₁ * (2 * π) * x) := by
    rw [hcdef, hK₁]; ring_nf
  rw [hℓc, ← hℓdef] at hrung
  set L := Real.log c with hL
  have hLℓ : 1 + L ≤ ℓ := by
    have h1 : L ≤ Real.log (K₁ * (2 * π) * x) := by
      rw [hL, hcdef]
      exact Real.log_le_log hc0 (by nlinarith [mul_le_mul_of_nonneg_right hK₁1 hc0.le])
    have h2 : 0 ≤ L := Real.log_nonneg (by linarith)
    rw [hℓdef]; linarith
  set dd := ((c ^ 2 - lev c (2 * j)) / c + 1) ^ 4 with hdd
  -- rung part: `aω C₁(1 + L)dd ≤ aω^{1−η}(Ĉℓ⁵ − 1)`
  have hp1 : a * ω * (C₁ * (1 + L) * dd) ≤ a * ω ^ (1 - η) * (C₁ * ℓ * (16 * (ℓ ^ 4 + B) + 1296)) := by
    have hdd0 : 0 ≤ dd := by positivity
    have h1 : ω * dd = ω ^ (1 - η) * (ω ^ η * dd) := by rw [← mul_assoc, ← hsplit]
    have h2 : ω ^ η * dd ≤ 16 * (ℓ ^ 4 + B) + 1296 := hrung
    have hL0 : 0 ≤ 1 + L := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ c); linarith
    calc a * ω * (C₁ * (1 + L) * dd) = a * C₁ * (1 + L) * (ω * dd) := by ring
      _ = a * C₁ * (1 + L) * (ω ^ (1 - η) * (ω ^ η * dd)) := by rw [h1]
      _ ≤ a * C₁ * ℓ * (ω ^ (1 - η) * (16 * (ℓ ^ 4 + B) + 1296)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hLℓ (by positivity))
            (mul_le_mul_of_nonneg_left h2 hωr0) (by positivity) (by positivity)
      _ = a * ω ^ (1 - η) * (C₁ * ℓ * (16 * (ℓ ^ 4 + B) + 1296)) := by ring
  -- ground part: `ω₀C₀(1 + L)(c + 1)⁴ ≤ aω^{1−η}`
  have hp0 : ω₀ * (C₀ * (1 + L) * (c + 1) ^ 4) ≤ a * ω ^ (1 - η) := by
    have h1 : 16 * C₀ * K₁ * (c ^ 6 * Real.exp (-(κ * c))) ≤ a :=
      arith_ground hc0 hca (by positivity) hdx
    have h2 : ω₀ ^ η * (C₀ * (1 + L) * (c + 1) ^ 4) ≤ a := hground.trans h1
    calc ω₀ * (C₀ * (1 + L) * (c + 1) ^ 4) = ω₀ ^ (1 - η) * (ω₀ ^ η * (C₀ * (1 + L) * (c + 1) ^ 4)) := by
          conv_lhs => rw [hsplit0]
          ring
      _ ≤ ω ^ (1 - η) * a := by
          have hL0 : 0 ≤ 1 + L := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ c); linarith
          exact mul_le_mul (Real.rpow_le_rpow hω0 hω0ω (by linarith)) h2
            (mul_nonneg (Real.rpow_nonneg hω0 _) (by positivity)) hωr0
      _ = a * ω ^ (1 - η) := by ring
  -- assemble
  have hfin : Cvs.Route.Visibility.ExteriorTransformPointBound.extInt a
      (fun s => rung c (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s) σ
      ≤ a * ω ^ (1 - η) * Ĉ * ℓ ^ 5 := by
    refine htwo.trans ?_
    have hℓ1 : 1 ≤ ℓ := hℓx
    have hpoly : C₁ * ℓ * (16 * (ℓ ^ 4 + B) + 1296) + 1 ≤ Ĉ * ℓ ^ 5 := arith_poly hℓ1 hC₁0 hB0
    have haω : 0 ≤ a * ω ^ (1 - η) := by positivity
    calc a * ω * (C₁ * (1 + L) * dd) + ω₀ * (C₀ * (1 + L) * (c + 1) ^ 4)
        ≤ a * ω ^ (1 - η) * (C₁ * ℓ * (16 * (ℓ ^ 4 + B) + 1296)) + a * ω ^ (1 - η) := add_le_add hp1 hp0
      _ = a * ω ^ (1 - η) * (C₁ * ℓ * (16 * (ℓ ^ 4 + B) + 1296) + 1) := by ring
      _ ≤ a * ω ^ (1 - η) * (Ĉ * ℓ ^ 5) := mul_le_mul_of_nonneg_left hpoly haω
      _ = a * ω ^ (1 - η) * Ĉ * ℓ ^ 5 := by ring
  refine hfin.trans ?_
  have haω : 0 ≤ a * ω ^ (1 - η) := by positivity
  calc a * ω ^ (1 - η) * Ĉ * ℓ ^ 5 = a * ω ^ (1 - η) * (Ĉ * ℓ ^ 5) := by ring
    _ ≤ a * ω ^ (1 - η) * (x : ℝ) ^ ε := mul_le_mul_of_nonneg_left hQx haω
    _ = (x : ℝ) ^ ε * a * ω ^ (1 - η) := by ring

/-- **PR_σ in the route-SEP form**: for `σ < 1` and `0 < η < ½`, for every `ε > 0`, eventually in `x`, every `j < x`
has `Ext_{G_j}(σ) ≤ x^ε·a·(1 − λ_{4j})^{1/2+η}`. -/
theorem extInt_profile_le_half {σ η : ℝ} (hσ : σ < 1) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j < x,
      Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x)
          (fun s => rung (2 * π * x) (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 s) σ
        ≤ (x : ℝ) ^ ε * (1 / x) * (1 - lamR (2 * π * x) (2 * j)) ^ (1 / 2 + η) := by
  intro ε hε
  have h := extInt_profile_le_rpow hσ (η := 1 / 2 - η) (by linarith) (by linarith) ε hε
  rw [show (1 : ℝ) - (1 / 2 - η) = 1 / 2 + η by ring] at h
  exact h

end Cvs.Prolate.Envelope.RungDuhamelRemainder
