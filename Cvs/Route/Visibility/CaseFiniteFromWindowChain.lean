import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Case F's cell floor from the window chain, and the `Ext` floor sum from PR_σ

The window chain (WF′) ∧ (EF′) ∧ AL-R of Cvs.Route.Visibility.WindowChainCellFloors gives `CaseFiniteCellFloorRates`'s eventual cell floor `δ_j = cellFloor x η₀ j`, and
`δ_j ≥ ((1 − η₀)²/4)·σ'_j/x` with `σ'_j = 1/(C⁻¹)_jj` of the cell Gram. Floor sum rates against `σ'_j/x` pass to
`δ`. With `RungDuhamelRemainder`'s PR_σ, `Ext_{e_j}(σ) ≤ x^ε·x⁻¹·(1 − λ_{4j})^{1/2+η}`, `CaseFiniteCellFloorRates`'s `Ext` floor sum at every `σ < 1`
reduces to the tunnelling floor sum `Σ_j √((1 − λ_{4j})^{1/2+η})/√σ'_j ≤ C_ε x^ε`.
-/

noncomputable section

open Real Set Filter Finset
open Cvs.Prolate.EvenRungsByIndex (rung lamR)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram cellGram_posDef)
open Cvs.Route.Visibility.WindowChainCellFloors (cellFloor finOfSF)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (IsCellFloor FloorSumRate ExtFloorSum)

namespace Cvs.Route.Visibility.CaseFiniteFromWindowChain
open Cvs.ZeroCounting

/-! ### The cell floor of the window chain -/

/-- The scaled Schur floor `σ'_j/x`, `σ'_j = 1/(C⁻¹)_jj` of the cell Gram. -/
def sigmaFloor (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / x

theorem sigmaFloor_pos {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) : 0 < sigmaFloor x j :=
  div_pos (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (cellGram_posDef hx) _) (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)

/-- `δ_j ≥ ((1 − η₀)²/4)·σ'_j/x`. -/
theorem mul_sigmaFloor_le_cellFloor {x : ℕ} (hx : 80 ≤ 2 * π * x) (η₀ : ℝ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    (1 - η₀) ^ 2 / 4 * sigmaFloor x j ≤ cellFloor x η₀ j := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hs := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (cellGram_posDef hx) (finOfSF j)
  have h1 : 1 ≤ (1 + √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam x j)) ^ 2 := by nlinarith [sqrt_nonneg (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam x j)]
  have hq : 0 ≤ (1 - η₀) ^ 2 := sq_nonneg _
  unfold cellFloor sigmaFloor
  have h2 : Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / 2
      ≤ (1 + √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam x j)) ^ 2 * Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / 2 := by nlinarith
  calc (1 - η₀) ^ 2 / 4 * (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / x)
      = 1 / (x : ℝ) / 2 * ((1 - η₀) ^ 2 * (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / 2)) := by
        field_simp; ring
    _ ≤ _ := by gcongr

/-! ### Floor sum rates -/

/-- **A floor sum rate passes to a larger floor**: if `δ ≥ kδ' > 0`, `k > 0`, and `ν ≥ 0`, a floor sum rate against
`δ'` is one against `δ`. -/
theorem floorSumRate_of_le {δ δ' ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} {e k : ℝ} (hk : 0 < k)
    (hν : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) (hδ : ∀ᶠ x : ℕ in atTop, ∀ j, 0 < δ' x j ∧ k * δ' x j ≤ δ x j)
    (h : FloorSumRate δ' ν e) : FloorSumRate δ ν e := fun ε hε => by
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C / √k, ?_⟩
  filter_upwards [hC, hν, hδ] with x h1 h2 h3
  have hk' : 0 < √k := sqrt_pos.mpr hk
  have hterm : ∀ j, ν x j / √(δ x j) ≤ (1 / √k) * (ν x j / √(δ' x j)) := fun j => by
    have hd : 0 < √(δ' x j) := sqrt_pos.mpr (h3 j).1
    calc ν x j / √(δ x j) ≤ ν x j / √(k * δ' x j) :=
          div_le_div_of_nonneg_left (h2 j) (sqrt_pos.mpr (mul_pos hk (h3 j).1)) (sqrt_le_sqrt (h3 j).2)
      _ = (1 / √k) * (ν x j / √(δ' x j)) := by rw [sqrt_mul hk.le]; field_simp
  calc ∑ j, ν x j / √(δ x j) ≤ ∑ j, (1 / √k) * (ν x j / √(δ' x j)) := Finset.sum_le_sum fun j _ => hterm j
    _ = (1 / √k) * ∑ j, ν x j / √(δ' x j) := by rw [Finset.mul_sum]
    _ ≤ (1 / √k) * (C * (x : ℝ) ^ (e + ε)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C / √k * (x : ℝ) ^ (e + ε) := by ring

/-- A floor sum rate against `σ'/x` is one against the cell floor `cellFloor η₀`, `η₀ < 1`. -/
theorem floorSumRate_cellFloor {ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} {e η₀ : ℝ} (hη : η₀ < 1)
    (hν : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) (h : FloorSumRate sigmaFloor ν e) :
    FloorSumRate (fun x => cellFloor x η₀) ν e := by
  have hk : 0 < (1 - η₀) ^ 2 / 4 := by have : 0 < 1 - η₀ := by linarith
                                       positivity
  refine floorSumRate_of_le hk hν ?_ h
  filter_upwards [Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx j
  exact ⟨sigmaFloor_pos hx j, mul_sigmaFloor_le_cellFloor hx η₀ j⟩

/-- **A floor sum rate scales**: `ν ↦ kν`, `k ≥ 0`. -/
theorem floorSumRate_const_mul {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} {e k : ℝ} (hk : 0 ≤ k)
    (h : FloorSumRate δ ν e) : FloorSumRate δ (fun x j => k * ν x j) e := fun ε hε => by
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨k * C, ?_⟩
  filter_upwards [hC] with x h1
  calc ∑ j, k * ν x j / √(δ x j) = k * ∑ j, ν x j / √(δ x j) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ k * (C * (x : ℝ) ^ (e + ε)) := mul_le_mul_of_nonneg_left h1 hk
    _ = k * C * (x : ℝ) ^ (e + ε) := by ring

/-- **A floor sum rate weakens in the exponent**: `e ≤ e'`. -/
theorem floorSumRate_mono {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ} {e e' : ℝ} (he : e ≤ e')
    (h : FloorSumRate δ ν e) : FloorSumRate δ ν e' := fun ε hε => by
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨max C 0, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with x h1 hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  calc _ ≤ C * (x : ℝ) ^ (e + ε) := h1
    _ ≤ max C 0 * (x : ℝ) ^ (e + ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (x : ℝ) ^ (e' + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (le_max_right _ _)

/-! ### The `Ext` floor sum from PR_σ -/

/-- **The tunnelling floor sum** at exponent `1/2 + η`: `Σ_j √((1 − λ_{4j})^{1/2+η})/√σ'_j ≤ C_ε x^ε` at all large
`x`, for every `ε > 0`. -/
def ExtTunnelSum (η : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
    ∑ j : Cvs.Approximant.SpineSubspace.SF x, √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
      / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)) ≤ C * (x : ℝ) ^ ε

/-- The spine profile of the unit coefficient vector `e_j` is `h_{4j} − α_j h₀`. -/
theorem spineG_single (c : ℝ) {x : ℕ} (j : Cvs.Approximant.SpineSubspace.SF x) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c (Pi.single j 1) = fun s => rung c (2 * (j : ℕ)) s - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s := by
  funext s
  unfold Cvs.Approximant.DeepIndexSpineSpan.spineG
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- `√E/√(σ'/x) ≤ x^{ε/2}·√w/√σ'` whenever `E ≤ x^ε·x⁻¹·w`. -/
theorem sqrt_div_le {x σ E w ε : ℝ} (hx : 0 < x) (hσ : 0 < σ) (hE : E ≤ x ^ ε * (1 / x) * w) :
    √E / √(σ / x) ≤ x ^ (ε / 2) * (√w / √σ) := by
  have h1 : √E ≤ √(x ^ ε) * √(1 / x) * √w := by
    rw [← sqrt_mul (by positivity), ← sqrt_mul (by positivity)]; exact sqrt_le_sqrt hE
  have h2 : √(x ^ ε) = x ^ (ε / 2) := by
    rw [sqrt_eq_rpow, ← Real.rpow_mul hx.le]; ring_nf
  have h3 : √(1 / x) * √x = 1 := by rw [← sqrt_mul (by positivity), one_div, inv_mul_cancel₀ hx.ne', sqrt_one]
  have hσ' : 0 < √σ := sqrt_pos.mpr hσ
  have hx' : 0 < √x := sqrt_pos.mpr hx
  rw [sqrt_div' σ hx.le, div_div_eq_mul_div, div_le_iff₀ hσ']
  calc √E * √x ≤ √(x ^ ε) * √(1 / x) * √w * √x := mul_le_mul_of_nonneg_right h1 hx'.le
    _ = √(x ^ ε) * √w * (√(1 / x) * √x) := by ring
    _ = x ^ (ε / 2) * (√w / √σ) * √σ := by rw [h3, h2]; field_simp
    _ = _ := rfl

/-- **The `Ext` floor sum against `σ'/x` from PR_σ**: for `σ < 1` and `0 < η < ½`, the tunnelling floor sum gives
`Σ_j √Ext_{e_j}(σ)/√(σ'_j/x) ≤ C_ε x^ε`. -/
theorem floorSumRate_sqrt_extInt {σ η : ℝ} (hσ : σ < 1) (hη0 : 0 < η) (hη1 : η < 1 / 2) (hT : ExtTunnelSum η) :
    FloorSumRate sigmaFloor
      (fun x j => √(Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ)) 0 := fun ε hε => by
  obtain ⟨C, hC⟩ := hT (ε / 2) (by linarith)
  refine ⟨C, ?_⟩
  filter_upwards [hC, Cvs.Prolate.Envelope.RungDuhamelRemainder.extInt_profile_le_half hσ hη0 hη1 ε hε, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x h1 h2 hx
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hterm : ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      √(Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ) / √(sigmaFloor x j)
        ≤ (x : ℝ) ^ (ε / 2) * (√((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
          / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j))) := fun j => by
    refine sqrt_div_le hx0 (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (cellGram_posDef hx) _) ?_
    rw [spineG_single]
    exact h2 j (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)
  calc _ ≤ ∑ j : Cvs.Approximant.SpineSubspace.SF x, (x : ℝ) ^ (ε / 2) * (√((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
          / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j))) := Finset.sum_le_sum fun j _ => hterm j
    _ = (x : ℝ) ^ (ε / 2) * ∑ j : Cvs.Approximant.SpineSubspace.SF x, √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
          / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)) := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) ^ (ε / 2) * (C * (x : ℝ) ^ (ε / 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * (x : ℝ) ^ (0 + ε) := by
        rw [zero_add, show ε = ε / 2 + ε / 2 by ring, Real.rpow_add hx0]; ring_nf

/-- **`CaseFiniteCellFloorRates`'s `Ext` floor sum from PR_σ**: for `σ < 1`, `0 < η < ½` and `η₀ < 1`, the tunnelling floor sum gives
`ExtFloorSum (cellFloor η₀) σ`. -/
theorem extFloorSum_of_tunnel {σ η η₀ : ℝ} (hσ : σ < 1) (hη0 : 0 < η) (hη1 : η < 1 / 2) (hη₀ : η₀ < 1)
    (hT : ExtTunnelSum η) : ExtFloorSum (fun x => cellFloor x η₀) σ :=
  ⟨_, Eventually.of_forall fun _ _ => le_rfl, Eventually.of_forall fun _ _ => sqrt_nonneg _,
    floorSumRate_cellFloor hη₀ (Eventually.of_forall fun _ _ => sqrt_nonneg _)
      (floorSumRate_sqrt_extInt hσ hη0 hη1 hT)⟩

end Cvs.Route.Visibility.CaseFiniteFromWindowChain

end
