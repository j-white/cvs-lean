import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.EvenFirstCellPoisson
import Cvs.Route.Visibility.EvenFirstCellProfile
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.Upstream.PencilLayerBound
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window chain: (WF′) ∧ (EF′) ⟹ (B) ⟹ AL ⟹ the cell floors `δ_j`, given AL-R

With `AL-R`, `x∫cellRem² ≤ C₀(x)E(b)`, (B) gives AL, `x∫cellRem² ≤ η₀²∫cellMain²` with `η₀ < 1`, and AL gives
`δ_j = (1/(2x))(1 − η₀)²(1 + √λ_j)²σ'_j/2 ≤ cellEnergy x b` on `b_j = 1`, `σ'_j = 1/(C⁻¹)_jj`.
-/

noncomputable section

open Real Set Filter Matrix Finset MeasureTheory Topology

namespace Cvs.Route.Visibility.WindowChainCellFloors
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram cellGram_posDef lam lamTop energyE coefH coefW)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0 C0inf cE CondB WFprime EFprime eventually_scale)

/-! ### AL-R and AL -/

/-- **AL-R**: eventually `‖R b‖² = x∫_{(1/2,1]} cellRem² ≤ C₀(x)·E(b)` for every spine
class `b`, with `C₀ = (½ + √(W̃/2 + C₁/(2c)) + (πcλ_t)^{−1/2})²`. -/
def ALR (Wt C₁ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ b : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2 ≤ C0 Wt C₁ x * energyE x b

/-- **AL** with constant `η₀`: eventually `‖R b‖² = x∫cellRem² ≤ η₀²‖M b‖² = η₀²∫cellMain²` on `(1/2, 1]`. -/
def AL (η₀ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ b : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2
      ≤ η₀ ^ 2 * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2

/-- **(B) ∧ AL-R ⟹ AL**: through I1, `E(b) ≤ (1 − λ_t)c_E^C‖M b‖²`, and `1 − λ_t ≤ ½`. -/
theorem al_of_condB {Wt C₁ : ℝ} (hB : CondB Wt C₁) (hR : ALR Wt C₁) : ∃ η₀, 0 < η₀ ∧ η₀ < 1 ∧ AL η₀ := by
  obtain ⟨κ, hκ, hev⟩ := hB
  set κ' := max κ 1
  have hκ' : κ' < 2 := max_lt hκ (by norm_num)
  have hκ1 : 1 ≤ κ' := le_max_right _ _
  refine ⟨√(κ' / 2), Real.sqrt_pos.2 (by linarith), ?_, ?_⟩
  · rw [Real.sqrt_lt' one_pos]; linarith
  filter_upwards [hev, hR, eventually_scale] with x hb hr hx b
  rw [Real.sq_sqrt (by linarith)]
  have hE := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.energyE_le hx b
  have hc0 := Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0_nonneg Wt C₁ x
  have hcE : 0 ≤ cE x := Cvs.Upstream.PencilLayerBound.pencilTop_nonneg (cellGram_posDef hx) (fun n => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_nonneg hx n.2) _
  have hM : 0 ≤ ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have ht := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have ht1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  set A := ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2
  have hκb : C0 Wt C₁ x * cE x ≤ κ' := hb.trans (le_max_left _ _)
  calc (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2 ≤ C0 Wt C₁ x * energyE x b := hr b
    _ ≤ C0 Wt C₁ x * ((1 - lamTop x) * cE x * A) := mul_le_mul_of_nonneg_left hE hc0
    _ = (1 - lamTop x) * (C0 Wt C₁ x * cE x) * A := by ring
    _ ≤ (1 / 2) * κ' * A := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact mul_le_mul (by linarith) hκb (mul_nonneg hc0 hcE) (by norm_num)
    _ = κ' / 2 * A := by ring

/-! ### AL gives the cell floors -/

/-- The spine index `j ∈ SF x` as a rung of the cell Gram. -/
def finOfSF {x : ℕ} (j : Cvs.Approximant.SpineSubspace.SF x) : Fin x := ⟨j, Cvs.Approximant.SpineSubspace.SF_lt x j j.2⟩

/-- **The cell floor** `δ_j = (1/(2x))·(1 − η₀)²·(1 + √λ_j)²σ'_j/2`, with `σ'_j = 1/(C⁻¹)_jj`. -/
def cellFloor (x : ℕ) (η₀ : ℝ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ :=
  1 / (x : ℝ) / 2 * ((1 - η₀) ^ 2 * ((1 + √(lam x j)) ^ 2 * Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / 2))

/-- `δ_j > 0` for `η₀ < 1`. -/
theorem cellFloor_pos {x : ℕ} (hx : 80 ≤ 2 * π * x) {η₀ : ℝ} (hη : η₀ < 1) (j : Cvs.Approximant.SpineSubspace.SF x) :
    0 < cellFloor x η₀ j := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hs := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (cellGram_posDef hx) (finOfSF j)
  have h1 : 0 < 1 - η₀ := by linarith
  unfold cellFloor
  positivity

/-- The main cell profile is continuous on `[−1, 1]`. -/
theorem continuousOn_cellMain {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ContinuousOn (Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b) (Icc (-1) 1) := by
  rw [show Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b = fun s => ∑ n, coefW x b n * Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (n : ℕ)) s from
    funext (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellMain_eq_sum hx b)]
  exact continuousOn_finsetSum _ fun n _ => (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _).const_smul (coefW x b n)

/-- The main cell profile is square integrable on `(1/2, 1]`. -/
theorem memLp_cellMain {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have hsub : Ioc (1 / 2 : ℝ) 1 ⊆ Icc (-1) 1 := fun u hu => ⟨by linarith [hu.1], hu.2⟩
  have hc := continuousOn_cellMain hx b
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine MemLp.of_bound ((hc.mono hsub).aestronglyMeasurable measurableSet_Ioc) M ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun u hu => hM u (hsub hu)

/-- The even cell profile is square integrable on `(1/2, 1]`. -/
theorem memLp_cellProfile {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hs : (0 : ℝ) < √(1 / (x : ℝ) / 2) := Real.sqrt_pos.2 (by positivity)
  have hsum : MemLp (fun u => ∑ j, b j * Cvs.Prolate.Gram.EvenFirstCellEnergyGram.rungCell x j u) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) :=
    memLp_finsetSum _ fun j _ => (Cvs.Prolate.Gram.EvenFirstCellEnergyGram.memLp_rungCell x j).const_mul (b j)
  have e : Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)
      = fun u => (√(1 / (x : ℝ) / 2))⁻¹ * ∑ j, b j * Cvs.Prolate.Gram.EvenFirstCellEnergyGram.rungCell x j u := by
    funext u
    rw [← Cvs.Prolate.Gram.EvenFirstCellEnergyGram.cellProfile_eq_sum, Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  rw [e]
  exact hsum.const_mul _

/-- The scaled remainder `√x·cellRem` is square integrable on `(1/2, 1]`. -/
theorem memLp_cellRem {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (fun θ => √(x : ℝ) * Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  refine ((memLp_cellProfile hx b).sub (memLp_cellMain hx1 b)).ae_eq ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [Cvs.Route.Visibility.EvenFirstCellPoisson.cellProfile_ae_eq hx b] with θ h hθ
  rw [Pi.sub_apply, h hθ]
  ring

/-- **A relative `L²` perturbation keeps the energy**: `∫g² ≤ η²∫f²` with `0 < η ≤ 1` gives
`(1 − η)²∫f² ≤ ∫(f + g)²`. -/
theorem integral_add_sq_ge {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (h : ∫ u, g u ^ 2 ∂μ ≤ η ^ 2 * ∫ u, f u ^ 2 ∂μ) :
    (1 - η) ^ 2 * ∫ u, f u ^ 2 ∂μ ≤ ∫ u, (f u + g u) ^ 2 ∂μ := by
  have hf2 := hf.integrable_sq
  have hg2 := hg.integrable_sq
  have hfg2 := (hf.add hg).integrable_sq
  have hpt : ∀ u, (1 - η) * f u ^ 2 + (1 - 1 / η) * g u ^ 2 ≤ (f u + g u) ^ 2 := by
    intro u
    have : (f u + g u) ^ 2 - ((1 - η) * f u ^ 2 + (1 - 1 / η) * g u ^ 2) = (η * f u + g u) ^ 2 / η := by
      field_simp; ring
    have : 0 ≤ (η * f u + g u) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    linarith
  have hint : ∫ u, ((1 - η) * f u ^ 2 + (1 - 1 / η) * g u ^ 2) ∂μ ≤ ∫ u, (f u + g u) ^ 2 ∂μ :=
    integral_mono ((hf2.const_mul (1 - η)).add (hg2.const_mul (1 - 1 / η))) hfg2 hpt
  rw [integral_add (hf2.const_mul _) (hg2.const_mul _), integral_const_mul, integral_const_mul] at hint
  have hc : 1 - 1 / η ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hη]; linarith
  have hA : 0 ≤ ∫ u, f u ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have := mul_le_mul_of_nonpos_left h hc
  have e : (1 - 1 / η) * (η ^ 2 * ∫ u, f u ^ 2 ∂μ) = (η ^ 2 - η) * ∫ u, f u ^ 2 ∂μ := by
    field_simp
  rw [e] at this
  nlinarith

/-- `∫(√x·cellRem)² = x∫cellRem²`. -/
theorem integral_sqrt_mul_sq (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, (√(x : ℝ) * Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ) ^ 2
      = (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2 := by
  simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg x)]
  exact integral_const_mul _ _

/-- The main cell energy on a unit coefficient: `(1 + √λ_j)²σ'_j/2 ≤ ∫cellMain²` when `b_j = 1`. -/
theorem le_integral_cellMain_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    (hb : b j = 1) :
    (1 + √(lam x j)) ^ 2 * Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j) / 2
      ≤ ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2 := by
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.integral_cellMain_sq hx1]
  have h := Cvs.Upstream.CellFloorSandwichPosDef.coef_sq_mul_le (cellGram_posDef hx) (coefW x b) (finOfSF j)
  have hw : coefW x b (finOfSF j) = 1 + √(lam x j) := by
    have hj : ((finOfSF j : Fin x) : ℕ) ∈ Cvs.Approximant.SpineSubspace.SF x := j.2
    simp only [coefW, coefH, dif_pos hj]
    simp [finOfSF, hb]
  rw [hw] at h
  linarith

/-- **AL ⟹ the cell floors**: eventually `δ_j ≤ cellEnergy x b` whenever `b_j = 1`. -/
theorem cellFloor_le_of_al {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ < 1) (hAL : AL η₀) :
    ∀ᶠ x : ℕ in atTop, ∀ (j : Cvs.Approximant.SpineSubspace.SF x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ), b j = 1 →
      cellFloor x η₀ j ≤ Cvs.Upstream.CoefficientFloorLinearBound.cellEnergy x b := by
  filter_upwards [hAL, eventually_scale] with x hal hx j b hb
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  have hR : ∫ θ in Ioc (1 / 2 : ℝ) 1, (√(x : ℝ) * Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ) ^ 2
      ≤ η₀ ^ 2 * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b θ ^ 2 := by
    rw [integral_sqrt_mul_sq]; exact hal b
  have hE := integral_add_sq_ge (memLp_cellMain hx1 b) (memLp_cellRem hx b) h0 h1.le hR
  have hM := le_integral_cellMain_sq hx j b hb
  rw [Cvs.Route.Visibility.EvenFirstCellPoisson.cellEnergy_eq hx b, cellFloor]
  have hc : (0 : ℝ) ≤ 1 / (x : ℝ) / 2 := by positivity
  refine mul_le_mul_of_nonneg_left (le_trans ?_ hE) hc
  exact mul_le_mul_of_nonneg_left hM (sq_nonneg _)

/-! ### The chain -/

end Cvs.Route.Visibility.WindowChainCellFloors
