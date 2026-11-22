import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.WindowTransformExterior

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The log-tail rate from a cell floor and a per-rung log-tail law

For `Re s < 1`, `X_b(s) = Σ_j b_j X_{e_j}(s)` (Cvs.Route.Visibility.PerRungBoxBound), so `b ↦ X_b(σ + i·)·√(log⁺(|·|/T₀))` is linear into
`L²(ℝ; ℂ)` with squared norm the log tail, and a cell floor `δ` bounds it by `(Σ_j ν_j/√δ_j)·‖r_b‖` (Cvs.Upstream.CoefficientFloorLinearBound). Per-rung
bounds `√(log tail_{e_j}) ≤ ν_j` on `[σ₁, σ₂]` with floor sum `x^{o(1)}` give `Cvs.Route.Visibility.CaseFiniteCellFloorRates.LogTailRate σ₁ σ₂`; a per-rung
law `log tail_{e_j}(σ) ≤ P(x)·x⁻¹·(1 − λ_{4j})^{1/2+η}` feeds the tunnelling floor sum of the `Ext` law (Cvs.Route.Visibility.CaseFiniteFromWindowChain).
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Route.Visibility.ExteriorFactorMTwo (rNorm)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (IsCellFloor FloorSumRate LogTailRate logTail)
open Cvs.Route.Visibility.CaseFiniteFromWindowChain (sigmaFloor)

namespace Cvs.Route.Visibility.LogTailRateCellFloor
open Cvs.ZeroCounting

/-! ### Sums of `L²` classes -/

/-- The coefficient function of a real combination of `L²` classes is a.e. the combination of the functions. -/
theorem coeFn_sum_smul_toLp {ι α E : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : ι → α → E) (hv : ∀ i, MemLp (v i) 2 μ) (a : ι → ℝ) :
    ⇑(∑ i, a i • (hv i).toLp (v i)) =ᵐ[μ] fun x => ∑ i, a i • v i x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (a j • (hv j).toLp (v j)) (∑ i ∈ s, a i • (hv i).toLp (v i)),
      Lp.coeFn_smul (a j) ((hv j).toLp (v j)), (hv j).coeFn_toLp, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert hj]

/-! ### The log-tail map -/

/-- The weighted line function `g ↦ X_b(σ + ig)·√(log⁺(|g|/T₀))`. -/
def tailFun (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (g : ℝ) : ℂ :=
  mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I) * (√(max (Real.log (|g| / T₀)) 0) : ℂ)

theorem norm_sq_tailFun (x : ℕ) (σ T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (g : ℝ) :
    ‖tailFun x σ T₀ b g‖ ^ 2
      = ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T₀)) 0 := by
  rw [tailFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), mul_pow,
    sq_sqrt (le_max_right _ _)]

/-- For `σ < 1` the weighted line function is the coefficient combination of the unit ones. -/
theorem tailFun_eq_sum {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    (g : ℝ) : tailFun x σ T₀ b g = ∑ j, b j • tailFun x σ T₀ (Pi.single j 1) g := by
  have hs : ((σ : ℂ) + g * I).re < 1 := by simpa using hσ
  unfold tailFun
  rw [Cvs.Route.Visibility.PerRungBoxBound.mellinR_ext_eq_sum hx hs b, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [Complex.real_smul]; ring

/-- The weighted line function is a.e. strongly measurable for `σ < 1`. -/
theorem aestronglyMeasurable_tailFun {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (T₀ : ℝ)
    (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : AEStronglyMeasurable (tailFun x σ T₀ b) volume := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx b
  have hX := (Cvs.Route.Visibility.ExteriorTransformHolomorphy.mellinR_ext_holo (by positivity : (0 : ℝ) < 1 / x) hG hG₁ hGi).1
  have hc : Continuous fun g : ℝ => mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I) :=
    hX.continuousOn.comp_continuous (by fun_prop) fun g => by simpa using hσ
  have hm : Measurable fun g : ℝ => ((√(max (Real.log (|g| / T₀)) 0) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      ((Real.measurable_log.comp (measurable_abs.div_const T₀)).max measurable_const).sqrt
  exact hc.aestronglyMeasurable.mul hm.aestronglyMeasurable

/-- An integrable log tail makes the weighted line function square integrable. -/
theorem memLp_tailFun {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (T₀ : ℝ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    (hb : Integrable fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0) :
    MemLp (tailFun x σ T₀ b) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_tailFun hx hσ T₀ b)]
  simpa only [norm_sq_tailFun] using hb

/-- The log-tail map of the coefficients into `L²(ℝ; ℂ)`, from integrable unit log tails. -/
def tailMap {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (T₀ : ℝ)
    (h : ∀ j : Cvs.Approximant.SpineSubspace.SF x, Integrable fun g : ℝ =>
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0) :
    (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  Fintype.linearCombination ℝ fun j => (memLp_tailFun hx hσ T₀ _ (h j)).toLp (tailFun x σ T₀ (Pi.single j 1))

/-- **The log-tail map is the weighted line function**: its value at `b` is a.e. `tailFun b`; so the log tail of
`b` is integrable and equals `‖tailMap b‖²`. -/
theorem tailMap_spec {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (T₀ : ℝ)
    (h : ∀ j : Cvs.Approximant.SpineSubspace.SF x, Integrable fun g : ℝ =>
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    (Integrable fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0)
      ∧ ‖tailMap hx hσ T₀ h b‖ ^ 2 = logTail x σ T₀ b := by
  have hae : ⇑(tailMap hx hσ T₀ h b) =ᵐ[volume] tailFun x σ T₀ b := by
    rw [tailMap, Fintype.linearCombination_apply]
    filter_upwards [coeFn_sum_smul_toLp _ (fun j => memLp_tailFun hx hσ T₀ _ (h j)) b] with g hg
    rw [hg, tailFun_eq_sum hx hσ]
  have hL : MemLp (tailFun x σ T₀ b) 2 volume :=
    (Lp.memLp (tailMap hx hσ T₀ h b)).ae_eq hae
  refine ⟨?_, ?_⟩
  · have := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).1 hL
    simpa only [norm_sq_tailFun] using this
  · rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral, logTail]
    refine integral_congr_ae ?_
    filter_upwards [hae] with g hg
    rw [hg, norm_sq_tailFun]

/-! ### The log-tail rate from a cell floor -/

/-- **The log tail under a cell floor**: for `σ < 1`, integrable unit log tails with `√(log tail_{e_j}) ≤ ν_j` give
`log tail_b ≤ (Σ_j ν_j/√δ_j)²·‖r_b‖²`, the log tail of `b` being integrable. -/
theorem logTail_le_floorSum {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ : σ < 1) (T₀ : ℝ)
    {δ ν : Cvs.Approximant.SpineSubspace.SF x → ℝ} (hδ : IsCellFloor x δ)
    (h : ∀ j : Cvs.Approximant.SpineSubspace.SF x, Integrable fun g : ℝ =>
      ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0)
    (hν : ∀ j, √(logTail x σ T₀ (Pi.single j 1)) ≤ ν j) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    (Integrable fun g : ℝ => ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) (σ + g * I)‖ ^ 2
        * max (Real.log (|g| / T₀)) 0)
      ∧ logTail x σ T₀ b ≤ (∑ j, ν j / √(δ j)) ^ 2 * rNorm x b ^ 2 := by
  obtain ⟨hI, hn⟩ := tailMap_spec hx hσ T₀ h b
  refine ⟨hI, ?_⟩
  have h1 := Cvs.Upstream.CoefficientFloorLinearBound.norm_le_of_cell_floor hx (tailMap hx hσ T₀ h) δ hδ.1 hδ.2 b
  have hj : ∀ j, ‖tailMap hx hσ T₀ h (Pi.single j 1)‖ ≤ ν j := fun j => by
    rw [← Real.sqrt_sq (norm_nonneg _), (tailMap_spec hx hσ T₀ h _).2]; exact hν j
  have h2 : ‖tailMap hx hσ T₀ h b‖ ≤ (∑ j, ν j / √(δ j)) * rNorm x b :=
    h1.trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ =>
      div_le_div_of_nonneg_right (hj j) (sqrt_nonneg _)) (norm_nonneg _))
  rw [← hn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- **The log-tail rate from a cell floor**: for `σ₂ < 1`, an eventual cell floor `δ`, per-rung bounds
`√(log tail_{e_j}(σ)) ≤ ν_j` at `T₀ = 8πx` with integrable unit log tails, uniform on `[σ₁, σ₂]`, `ν ≥ 0`, and the
floor sum rate `x^{o(1)}` give `LogTailRate σ₁ σ₂`. -/
theorem logTailRate_of_floorSum {σ₁ σ₂ : ℝ} (hσ₂ : σ₂ < 1) {δ ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (δ x))
    (hν : ∀ᶠ x : ℕ in atTop, ∀ σ ∈ Icc σ₁ σ₂, ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      (Integrable fun g : ℝ =>
        ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) (σ + g * I)‖ ^ 2
          * max (Real.log (|g| / (8 * π * x))) 0)
      ∧ √(logTail x σ (8 * π * x) (Pi.single j 1)) ≤ ν x j)
    (hν0 : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j) (hs : FloorSumRate δ ν 0) : LogTailRate σ₁ σ₂ := by
  have h0 : ∀ᶠ x : ℕ in atTop, 0 ≤ ∑ j, ν x j / √(δ x j) := by
    filter_upwards [hν0] with x h
    exact Finset.sum_nonneg fun j _ => div_nonneg (h j) (sqrt_nonneg _)
  refine ⟨_, Cvs.Route.Visibility.CaseFiniteCellFloorRates.subPoly_sq_of_floorSumRate hs h0, ?_⟩
  filter_upwards [hδ, hν, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hδx hνx hsc σ hσ a
  have hσ1 : σ < 1 := lt_of_le_of_lt hσ.2 hσ₂
  have h := logTail_le_floorSum hsc hσ1 (8 * π * x) hδx (fun j => (hνx σ hσ j).1) (fun j => (hνx σ hσ j).2) a
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [mul_zero, neg_zero, Real.rpow_zero, mul_one]

/-! ### The per-rung log-tail law -/

/-- **The per-rung log-tail law at exponent `½ + η`**: for `0 < σ₁ ≤ σ ≤ σ₂ < 1`, some subpolynomial `P` has, at all
large `x` and on every rung, an integrable log tail at `T₀ = 8πx` with
`log tail_{e_j}(σ) ≤ P(x)·x⁻¹·(1 − λ_{4j})^{1/2+η}`. -/
def LogTailProfile (η : ℝ) : Prop :=
  ∀ σ₁ σ₂ : ℝ, 0 < σ₁ → σ₂ < 1 → ∃ P : ℕ → ℝ, SubPoly P ∧ ∀ᶠ x : ℕ in atTop, ∀ σ ∈ Icc σ₁ σ₂,
    ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      (Integrable fun g : ℝ =>
        ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) (σ + g * I)‖ ^ 2
          * max (Real.log (|g| / (8 * π * x))) 0)
      ∧ logTail x σ (8 * π * x) (Pi.single j 1)
          ≤ P x * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η)

/-- **The tunnelling floor sum with a subpolynomial factor**: `Σ_j √(P⁺(x)·x⁻¹·(1 − λ_{4j})^{1/2+η})/√(σ'_j/x)` has
rate `x^{o(1)}` under `CaseFiniteFromWindowChain`'s tunnelling floor sum. -/
theorem floorSumRate_profile {η : ℝ} (hT : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η) {P : ℕ → ℝ} (hP : SubPoly P) :
    FloorSumRate sigmaFloor (fun x j => √(max (P x) 0 * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η)))
      0 := fun ε hε => by
  obtain ⟨C, hC⟩ := hT (ε / 2) (by linarith)
  refine ⟨max C 0, ?_⟩
  filter_upwards [hC, Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hP ε hε, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x h1 h2 hx
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  set p := max (P x) 0
  have hp : 0 ≤ p := le_max_right _ _
  have hterm : ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      √(p * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η)) / √(sigmaFloor x j)
        = √p * (√((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
          / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j))) := fun j => by
    have hs := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx) (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j)
    unfold sigmaFloor
    rw [sqrt_mul (by positivity), sqrt_mul hp, Real.sqrt_div' 1 hx0.le, Real.sqrt_div' _ hx0.le, Real.sqrt_one]
    have : 0 < √(x : ℝ) := sqrt_pos.2 hx0
    have : 0 < √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j)) := sqrt_pos.2 hs
    field_simp
  have hS0 : 0 ≤ ∑ j : Cvs.Approximant.SpineSubspace.SF x, √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
      / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j)) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hsp : √p ≤ (x : ℝ) ^ (ε / 2) := by
    rw [show (x : ℝ) ^ (ε / 2) = √((x : ℝ) ^ ε) by
      rw [sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; ring_nf]
    exact sqrt_le_sqrt h2
  simp only [hterm, ← Finset.mul_sum]
  calc √p * _ ≤ (x : ℝ) ^ (ε / 2) * (max C 0 * (x : ℝ) ^ (ε / 2)) :=
        mul_le_mul hsp (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) hS0
          (by positivity)
    _ = max C 0 * (x : ℝ) ^ (0 + ε) := by
        rw [zero_add, show ε = ε / 2 + ε / 2 by ring, Real.rpow_add hx0]; ring_nf

/-- **The log-tail rate from the window chain's cell floor, the tunnelling floor sum and the per-rung law**: for
`η₀ < 1`, an eventual cell floor `cellFloor η₀`, `ExtTunnelSum η` and `LogTailProfile η` give `LogTailRate σ₁ σ₂`
for every `0 < σ₁`, `σ₂ < 1`. -/
theorem logTailRate_of_profile {η η₀ : ℝ} (hη₀ : η₀ < 1)
    (hδ : ∀ᶠ x : ℕ in atTop, IsCellFloor x (Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀)) (hT : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η)
    (hP : LogTailProfile η) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : σ₂ < 1) : LogTailRate σ₁ σ₂ := by
  obtain ⟨P, hP, hb⟩ := hP σ₁ σ₂ hσ₁ hσ₂
  set ν : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ :=
    fun x j => √(max (P x) 0 * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
  have hν0 : ∀ᶠ x : ℕ in atTop, ∀ j, 0 ≤ ν x j := Eventually.of_forall fun _ _ => sqrt_nonneg _
  refine logTailRate_of_floorSum hσ₂ hδ ?_ hν0
    (Cvs.Route.Visibility.CaseFiniteFromWindowChain.floorSumRate_cellFloor hη₀ hν0 (floorSumRate_profile hT hP))
  filter_upwards [hb, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx hsc σ hσ j
  obtain ⟨hI, hle⟩ := hx σ hσ j
  refine ⟨hI, sqrt_le_sqrt (hle.trans ?_)⟩
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have hlam := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 (Cvs.L2a.FullSpanIndexFloor.full_index x hsc (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)).1
  have hω : 0 ≤ (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η) := Real.rpow_nonneg (by linarith) _
  have hx1 : (0 : ℝ) ≤ 1 / x := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx1) hω

end Cvs.Route.Visibility.LogTailRateCellFloor

end
