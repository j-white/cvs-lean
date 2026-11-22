import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FiniteSpanRateHighMass
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.L1ConnesFactorPolynomial
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.LowRungFullTail
import Cvs.L2a.LowRungHighSpectralMass
import Cvs.L2a.LowRungTruncationRate
import Cvs.L2a.PositionTailEdgeRow
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.QSideConnesRelative
import Cvs.L2a.QSideRungConstants
import Cvs.L2a.RungSpanProfilePowers
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowThresholdExplicit
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.GroundRungEndpoint
import Cvs.Prolate.LowLevelsTwoFifths
import Cvs.Prolate.LowRungRadialTailEdge
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Route.JointGapConnesFromL1
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The q-side at Connes' vector in `h₄(1)²` units

At `c = 2πx`, `c₀^W ≤ c`: `M ≤ (2πc/C₀)h₄(1)²` (Cvs.Prolate.GroundRungEndpoint, `Σ|bᵢ| ≤ c`), `N ≤ (4 + Kfr)M` (Minkowski, Cvs.L2a.LowRungFullTail, Cvs.Prolate.LowRungRadialTailEdge),
`|2Π₊∫F/θ| ≤ 2C_π√P√N` with `P ≤ 4M` (Cvs.Prolate.RungTailIntegralMass, Cvs.L2a.FullTailBilinearChannels), and the constants of Cvs.L2a.QSideRungConstants give
`connesLrel x ≤ 2·10⁶(1 + log c)(2πc/C₀)h₄(1)²`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.QSideConnesEndpointUnits
open Cvs.ZeroCounting

open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)
open Cvs.Route.JointGapConnesFromL1 (one₁)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.Prolate.GroundRungEndpoint (groundC)

/-- The q-side factor `2·10⁶(1 + log c)(2πc/C₀)` at `c = 2πx`. -/
def qFactor (x : ℕ) : ℝ :=
  2 * 10 ^ 6 * (1 + Real.log (2 * π * x)) * (2 * π * (2 * π * x) / groundC)

/-- `c₀^W ≤ 2πx` gives `160 ≤ 2πx`. -/
theorem le_scale {x : ℕ} (hx : c0W ≤ 2 * π * x) : 160 ≤ 2 * π * (x : ℝ) := by
  have h := (Cvs.L2a.BandInputsFromCutMultipliers.scale_ge (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx)).1
  have := Real.add_one_le_exp (1360 : ℝ)
  linarith

/-- The full tail of a finite span of rungs is the span of their full tails, on `θ > 1`. -/
theorem fullTail_span {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} (b : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc0 : 0 < c) {θ : ℝ} (hθ : 1 < θ) :
    fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ = ∑ i, b i * fullTail (psi c (g i)) θ := by
  rw [Cvs.L2a.FullTailFloorLimit.span_eq b hg c]
  have h1 := Cvs.L2a.FullTailConvergence.tendsto_partial (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b hg)
    (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b hg₁) (Cvs.L2a.FullTailFloorLimit.continuousOn_span b hg₂c) hc0 hθ
  have h2 : Tendsto (fun M : ℕ => ∑ i, b i * ∑ m ∈ Finset.Icc 1 M, psi c (g i) (m * θ)) atTop
      (𝓝 (∑ i, b i * fullTail (psi c (g i)) θ)) :=
    tendsto_finsetSum _ fun i _ =>
      (Cvs.L2a.FullTailConvergence.tendsto_partial (hg i) (hg₁ i) (hg₂c i) hc0 hθ).const_mul (b i)
  refine tendsto_nhds_unique h1 (h2.congr fun M => ?_)
  rw [← Cvs.L2a.FullTailFloorLimit.span_eq b hg c]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **The full-tail norm of a span of low rungs**: `N ≤ (4 + Kfr(c))(Σ|bᵢ||ψᵢ(1)|)²` for `c ≥ 100`,
`0 ≤ χᵢ ≤ (2/5)c²`. -/
theorem tailN_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (b : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 100 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i ≤ 2 / 5 * c ^ 2) :
    Cvs.L2a.L1WindowFromFloor.tailN c b g
      ≤ (4 + Cvs.L2a.LowRungFullTail.Kfr c) * (∑ i, |b i| * |psi c (g i) 1|) ^ 2 := by
  have hc0 : 0 < c := by linarith
  set x : ι → ℝ → ℝ := fun i θ => fullTail (psi c (g i)) θ with hxd
  have hpt : ∀ θ ∈ Ioi (1 : ℝ), fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2 = (∑ i, b i * x i θ) ^ 2 :=
    fun θ hθ => by rw [fullTail_span b hg hg₁ hg₂c hc0 hθ]
  unfold Cvs.L2a.L1WindowFromFloor.tailN
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hmeas : ∀ i, Measurable (x i) := fun i =>
    Cvs.L2a.FullTailConvergence.measurable_fullTail (hg i) (hg₁ i) (hg₂c i) hc0
  have hbd := fun i θ (hθ : 0 < θ) => Cvs.L2a.FullTailConvergence.abs_fullTail_le (hg i) (hg₁ i) (hg₂c i) hc0 hθ
  have hx : ∀ i, IntegrableOn (fun θ => x i θ ^ 2) (Ioi 1) := fun i =>
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le (hmeas i) (hbd i)
  have hxy : ∀ i j, IntegrableOn (fun θ => x i θ * x j θ) (Ioi 1) := fun i j =>
    Cvs.L2a.FullTailConvergence.integrableOn_mul_of_le (hmeas i) (hmeas j) (hbd i) (hbd j)
  refine (Cvs.L2a.FiniteSpanRateHighMass.integral_sum_sq_le b hx hxy).trans ?_
  have hK0 : 0 ≤ 4 + Cvs.L2a.LowRungFullTail.Kfr c := by
    have : 0 ≤ Cvs.L2a.LowRungFullTail.Kfr c := by
      unfold Cvs.L2a.LowRungFullTail.Kfr Cvs.L2a.PositionTailEdgeRow.rowC; positivity
    linarith
  have hi : ∀ i, √(∫ θ in Ioi 1, x i θ ^ 2) ≤ √(4 + Cvs.L2a.LowRungFullTail.Kfr c) * |psi c (g i) 1| := fun i => by
    have h1 := (Cvs.L2a.LowRungFullTail.integral_fullTail_rung_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i)
      (hχ i)).2
    have h2 := Cvs.Prolate.LowRungRadialTailEdge.tail_le_edge (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ i)
    have h3 : ∫ θ in Ioi 1, x i θ ^ 2 ≤ (4 + Cvs.L2a.LowRungFullTail.Kfr c) * psi c (g i) 1 ^ 2 := by
      simp only [hxd]; linarith
    calc √(∫ θ in Ioi 1, x i θ ^ 2) ≤ √((4 + Cvs.L2a.LowRungFullTail.Kfr c) * psi c (g i) 1 ^ 2) :=
          Real.sqrt_le_sqrt h3
      _ = _ := by rw [Real.sqrt_mul hK0, Real.sqrt_sq_eq_abs]
  have hsum : ∑ i, |b i| * √(∫ θ in Ioi 1, x i θ ^ 2)
      ≤ √(4 + Cvs.L2a.LowRungFullTail.Kfr c) * ∑ i, |b i| * |psi c (g i) 1| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |b i| * √(∫ θ in Ioi 1, x i θ ^ 2) ≤ |b i| * (√(4 + Cvs.L2a.LowRungFullTail.Kfr c) * |psi c (g i) 1|) :=
          mul_le_mul_of_nonneg_left (hi i) (abs_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ i, |b i| * √(∫ θ in Ioi 1, x i θ ^ 2) := Finset.sum_nonneg fun i _ => by positivity
  calc (∑ i, |b i| * √(∫ θ in Ioi 1, x i θ ^ 2)) ^ 2
      ≤ (√(4 + Cvs.L2a.LowRungFullTail.Kfr c) * ∑ i, |b i| * |psi c (g i) 1|) ^ 2 := pow_le_pow_left₀ h0 hsum 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hK0]

/-- **The tail mass of a span of low rungs**: `Σ bᵢ²∫_{ξ>1}ψᵢ² ≤ 4(Σ|bᵢ||ψᵢ(1)|)²`. -/
theorem tailMass_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (b : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 100 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i ≤ 2 / 5 * c ^ 2) :
    ∑ i, b i ^ 2 * (∫ t in Ioi 1, psi c (g i) t ^ 2) ≤ 4 * (∑ i, |b i| * |psi c (g i) 1|) ^ 2 := by
  have h1 : ∑ i, b i ^ 2 * (∫ t in Ioi 1, psi c (g i) t ^ 2) ≤ 4 * ∑ i, (|b i| * |psi c (g i) 1|) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := Cvs.Prolate.LowRungRadialTailEdge.tail_le_edge (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ i)
    rw [mul_pow, sq_abs, sq_abs]
    nlinarith [sq_nonneg (b i)]
  have h2 : ∑ i, (|b i| * |psi c (g i) 1|) ^ 2 ≤ (∑ i, |b i| * |psi c (g i) 1|) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => by positivity
  linarith

/-- The Connes levels lie in `[0, (2/5)c²]`, and the Connes rungs exist. -/
theorem connes_levels {x : ℕ} (hx : c0W ≤ 2 * π * x) (i : Option ({1} : Finset ℕ)) :
    (∃ χ, IsLevelIdx (2 * π * x) (kOf i) χ) ∧ lev (2 * π * x) (kOf i) ≤ 2 / 5 * (2 * π * x) ^ 2 := by
  set c : ℝ := 2 * π * x with hcdef
  have hc80 : 80 ≤ c := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hc100 : 100 ≤ c := Cvs.L2a.QSideConnesRelative.hundred_le hx
  have hx1 : 1 < x := by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hc80
  rcases i with _ | j
  · refine ⟨exists_isLevelIdx_zero c, ?_⟩
    show lev c 0 ≤ 2 / 5 * c ^ 2
    rw [lev_zero]
    have := groundLevel_le c
    nlinarith
  · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
    have hk : kOf (some j) = 2 := by simp only [kOf, Option.elim, hj]
    rw [hk]
    have h := Cvs.Prolate.LowLevelsTwoFifths.lev_two_lt (c := c) (by nlinarith [Real.pi_lt_four])
    exact ⟨h.2, h.1.le⟩

/-- **Connes' edge scale in `h₄(1)²` units**: `M ≤ (2πc/C₀) h₄(1)²`. -/
theorem connesM_le {x : ℕ} (hx : c0W ≤ 2 * π * x) :
    Cvs.L2a.QSideConnesRelative.connesM x ≤ 2 * π * (2 * π * x) / groundC * rung (2 * π * x) 2 1 ^ 2 := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hc160 : 160 ≤ c := le_scale hx
  have hc0 : 0 < c := by linarith
  have hC := Cvs.Prolate.GroundRungEndpoint.groundC_pos
  have hC1 := Cvs.Prolate.GroundRungEndpoint.groundC_le_one
  set r := √(2 * π / (c * groundC)) * |rung c 2 1| with hrd
  have hr0 : 0 ≤ r := by positivity
  have hpt : ∀ i : Option ({1} : Finset ℕ), |psi c (rung c (kOf i)) 1| ≤ r := by
    intro i
    have hsq : psi c (rung c (kOf i)) 1 ^ 2 ≤ 2 * π / (c * groundC) * rung c 2 1 ^ 2 := by
      have h1 := Cvs.Prolate.GroundRungEndpoint.psi_one_sq_le hc0 (connes_levels hx i).1
      have hk : rung c (kOf i) 1 ^ 2 ≤ rung c 2 1 ^ 2 / groundC := by
        rw [le_div_iff₀ hC]
        rcases i with _ | j
        · have := Cvs.Prolate.GroundRungEndpoint.ground_ladder hc160
          simp only [kOf, Option.elim]; linarith
        · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
          have hk : kOf (some j) = 2 := by simp only [kOf, Option.elim, hj]
          rw [hk]
          nlinarith [sq_nonneg (rung c 2 1)]
      calc psi c (rung c (kOf i)) 1 ^ 2 ≤ 2 * π / c * rung c (kOf i) 1 ^ 2 := h1
        _ ≤ 2 * π / c * (rung c 2 1 ^ 2 / groundC) := mul_le_mul_of_nonneg_left hk (by positivity)
        _ = _ := by field_simp
    calc |psi c (rung c (kOf i)) 1| = √(psi c (rung c (kOf i)) 1 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √(2 * π / (c * groundC) * rung c 2 1 ^ 2) := Real.sqrt_le_sqrt hsq
      _ = r := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  have hsum : ∑ i, |bOf c one₁ i| * |psi c (rung c (kOf i)) 1| ≤ c * r := by
    calc ∑ i, |bOf c one₁ i| * |psi c (rung c (kOf i)) 1| ≤ ∑ i, |bOf c one₁ i| * r :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (abs_nonneg _)
      _ = (∑ i, |bOf c one₁ i|) * r := by rw [Finset.sum_mul]
      _ ≤ c * r := mul_le_mul_of_nonneg_right H.hS hr0
  unfold Cvs.L2a.QSideConnesRelative.connesM
  calc (∑ i, |bOf c one₁ i| * |psi c (rung c (kOf i)) 1|) ^ 2 ≤ (c * r) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => by positivity) hsum 2
    _ = c ^ 2 * (2 * π / (c * groundC)) * rung c 2 1 ^ 2 := by
        have hr2 : r ^ 2 = 2 * π / (c * groundC) * rung c 2 1 ^ 2 := by
          rw [hrd, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
        rw [mul_pow, hr2]; ring
    _ = _ := by field_simp

/-- **Connes' full-tail norm against its edge scale**: `N ≤ (4 + Kfr(c))M`. -/
theorem connesN_le {x : ℕ} (hx : c0W ≤ 2 * π * x) :
    Cvs.L2a.QSideConnesRelative.connesN x ≤ (4 + Cvs.L2a.LowRungFullTail.Kfr (2 * π * x)) * Cvs.L2a.QSideConnesRelative.connesM x := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  exact tailN_le _ H.hg H.hg₁ H.hg₂c H.hang (Cvs.L2a.QSideConnesRelative.hundred_le hx) H.hχ0 fun i => (connes_levels hx i).2

set_option maxHeartbeats 1000000 in
/-- **The q-side at Connes' vector against its edge scale**: `connesLrel x ≤ 2·10⁶(1 + log c)M`. -/
theorem connesLrel_le_M {x : ℕ} (hx : c0W ≤ 2 * π * x) :
    Cvs.L2a.QSideConnesRelative.connesLrel x ≤ 2 * 10 ^ 6 * (1 + Real.log (2 * π * x)) * Cvs.L2a.QSideConnesRelative.connesM x := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hc100 : 100 ≤ c := Cvs.L2a.QSideConnesRelative.hundred_le hx
  have hc0 : 0 < c := by linarith
  have hlog : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hχ := fun i => (connes_levels hx i).2
  set M := Cvs.L2a.QSideConnesRelative.connesM x with hMd
  set N := Cvs.L2a.QSideConnesRelative.connesN x with hNd
  set P := ∑ i, bOf c one₁ i ^ 2 * (∫ t in Ioi 1, psi c (rung c (kOf i)) t ^ 2) with hPd
  have hM0 : 0 ≤ M := by rw [hMd]; unfold Cvs.L2a.QSideConnesRelative.connesM; positivity
  have hN0 : 0 ≤ N := by
    rw [hNd]; unfold Cvs.L2a.QSideConnesRelative.connesN Cvs.L2a.L1WindowFromFloor.tailN
    exact setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hNM : N ≤ 104 * M := by
    have h1 := connesN_le hx
    have h2 := Cvs.L2a.QSideRungConstants.Kfr_le hc100
    rw [← hcdef, ← hNd, ← hMd] at h1
    nlinarith
  have hPM : P ≤ 4 * M := tailMass_le _ H.hg H.hg₁ H.hg₂c H.hang hc100 H.hχ0 hχ
  -- the pole term
  have hdist : Function.Injective fun i : Option ({1} : Finset ℕ) => lev c (kOf i) := by
    intro i i' he
    simp only at he
    rcases i with _ | j <;> rcases i' with _ | j'
    · rfl
    · have hj : (j' : ℕ) = 1 := Finset.mem_singleton.mp j'.2
      have hk : kOf (some j') = 2 := by simp only [kOf, Option.elim, hj]
      have := lev_lt (connes_levels hx (some j')).1 (show 0 < kOf (some j') by rw [hk]; norm_num)
      simp only [kOf, Option.elim] at he this ⊢; linarith
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      have hk : kOf (some j) = 2 := by simp only [kOf, Option.elim, hj]
      have := lev_lt (connes_levels hx (some j)).1 (show 0 < kOf (some j) by rw [hk]; norm_num)
      simp only [kOf, Option.elim] at he this ⊢; linarith
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      have hj' : (j' : ℕ) = 1 := Finset.mem_singleton.mp j'.2
      exact congrArg some (Subtype.ext (by rw [hj, hj']))
  have hPi := Cvs.Prolate.RungTailIntegralMass.abs_piPlus_span_le (bOf c one₁) H.hg H.hg₁ H.hg₂c H.hang H.hc H.hχ0 H.hχc hdist
  have hcard : (Fintype.card (Option ({1} : Finset ℕ)) : ℝ) = 2 := by simp [Fintype.card_option]
  rw [hcard] at hPi
  have hπC := Cvs.L2a.QSideRungConstants.piConst_two_le hc100
  have hspan := Cvs.L2a.FullTailFloorLimit.span_eq (bOf c one₁) H.hg c
  have hF : |∫ θ in Ioi 1, fullTail (Cvs.L2a.QSideConnesRelative.connesPhi x) θ / θ| ≤ √N := by
    have h := Cvs.L2a.FullTailBilinearChannels.abs_integral_fullTail_div_le
      (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span (bOf c one₁) H.hg)
      (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span (bOf c one₁) H.hg₁)
      (Cvs.L2a.FullTailFloorLimit.continuousOn_span (bOf c one₁) H.hg₂c) hc0
    rw [← hspan] at h
    exact h
  have hpole : 2 * Cvs.L2a.FullTailPoleChannel.piPlus (Cvs.L2a.QSideConnesRelative.connesPhi x) * (∫ θ in Ioi 1, fullTail (Cvs.L2a.QSideConnesRelative.connesPhi x) θ / θ)
      ≤ 2 * (P + N) := by
    set A := Cvs.L2a.FullTailPoleChannel.piPlus (Cvs.L2a.QSideConnesRelative.connesPhi x)
    set B := ∫ θ in Ioi 1, fullTail (Cvs.L2a.QSideConnesRelative.connesPhi x) θ / θ
    have hA : |A| ≤ 2 * √P := hPi.trans (mul_le_mul_of_nonneg_right hπC (Real.sqrt_nonneg _))
    have hAB : 2 * A * B ≤ 2 * (|A| * |B|) := by
      have := le_abs_self (A * B); rw [abs_mul] at this; linarith
    have h2 : |A| * |B| ≤ 2 * √P * √N := mul_le_mul hA hF (abs_nonneg _) (by positivity)
    have h3 : 2 * √P * √N ≤ P + N := by
      nlinarith [sq_nonneg (√P - √N), Real.sq_sqrt hP0, Real.sq_sqrt hN0]
    linarith
  -- the constants
  have ha : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c) + 114 / (2 * c) ≤ 7 + Real.log c := by
    have h1 := Cvs.L2a.QSideRungConstants.archSymbol_two_mul_le (c := c) (by linarith)
    have : 114 / (2 * c) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hKh := Cvs.L2a.QSideRungConstants.Khigh_le hc100
  have hKr := Cvs.L2a.QSideRungConstants.Krate_le hc100
  have hKr0 := Cvs.L2a.FiniteSpanRateHighMass.Krate_nonneg hc0
  have hsKr : √(Cvs.L2a.LowRungTruncationRate.Krate c) ≤ 270 :=
    Cvs.L2a.QSideRungConstants.sqrt_le_of_le_sq (by norm_num) (by linarith)
  have hκ := (Cvs.L2a.WindowChainInputsProlate.floor_full_span x (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx)
    fun _ => 0).1
  have hKp : Cvs.L2a.WindowChainFromInputs.KpolL (1 / 2) (kapFX x) ≤ 6650 :=
    (Cvs.L2a.WindowChainFromInputs.KpolL_anti (by norm_num) (by norm_num) hκ).trans Cvs.L2a.WindowThresholdExplicit.KpolL_half_le
  have hKp0 := Cvs.L2a.WindowChainFromInputs.KpolL_nonneg (1 / 2) (kapFX x)
  unfold Cvs.L2a.QSideConnesRelative.connesLrel
  rw [← hcdef, ← hNd, ← hMd]
  have t1 : (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c) + 114 / (2 * c)) * N ≤ (7 + Real.log c) * N :=
    mul_le_mul_of_nonneg_right ha hN0
  have t2 : 2 * Cvs.L2a.LowRungHighSpectralMass.Khigh c * M ≤ 2 * 80000 * M := by nlinarith
  have t3 : 4 * √(Cvs.L2a.LowRungTruncationRate.Krate c) * (M + N) ≤ 4 * 270 * (M + N) := by nlinarith
  have t4 : 4 * Cvs.L2a.LowRungTruncationRate.Krate c * M ≤ 4 * 72000 * M := by nlinarith
  have t5 : Cvs.L2a.WindowChainFromInputs.KpolL (1 / 2) (kapFX x) * N ≤ 6650 * N := by nlinarith
  have t6 : Real.log c * N ≤ Real.log c * (104 * M) := mul_le_mul_of_nonneg_left hNM hlog
  nlinarith

/-- **The q-side at Connes' vector in `h₄(1)²` units**: `connesLrel x ≤ qFactor x · h₄(1)²`. -/
theorem connesLrel_le {x : ℕ} (hx : c0W ≤ 2 * π * x) :
    Cvs.L2a.QSideConnesRelative.connesLrel x ≤ qFactor x * rung (2 * π * x) 2 1 ^ 2 := by
  have hc100 := Cvs.L2a.QSideConnesRelative.hundred_le hx
  have hlog : 0 ≤ Real.log (2 * π * x) := Real.log_nonneg (by linarith)
  have h1 := connesLrel_le_M hx
  have h2 := connesM_le hx
  have hk : 0 ≤ 2 * 10 ^ 6 * (1 + Real.log (2 * π * x)) := by positivity
  calc Cvs.L2a.QSideConnesRelative.connesLrel x ≤ 2 * 10 ^ 6 * (1 + Real.log (2 * π * x)) * Cvs.L2a.QSideConnesRelative.connesM x := h1
    _ ≤ 2 * 10 ^ 6 * (1 + Real.log (2 * π * x))
        * (2 * π * (2 * π * x) / groundC * rung (2 * π * x) 2 1 ^ 2) := mul_le_mul_of_nonneg_left h2 hk
    _ = _ := by unfold qFactor; ring

end Cvs.L2a.QSideConnesEndpointUnits
