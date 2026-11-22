import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungCentreBound
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.WindowTransformExterior

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `RungBox 1` from one rung at a time: the exterior box bound and the tunnelling sum

`PerRungBoxBound`'s `RungBox 1` asks for per-rung box data whose bounds `ν_j` have floor sum `x^{−1/2+o(1)}` against `σ'_j/x`.
Here `ν_j = (Q(x) + 4/π)x⁻¹√((1 − λ_j)^{½+η})`: the `g0` part is `RungCentreBound`'s `|g0_j| ≤ (4/π)x⁻¹√(1 − λ_j)`, the
exterior part is the per-rung statement `RungXBox η` (one rung, one box, no Gram), conjugate symmetry follows from the
identity theorem on the convex box, and the floor sum is `CaseFiniteFromWindowChain`'s `ExtTunnelSum η` times `x^{−1/2}Q(x)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open scoped ComplexConjugate
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.StepA.Edge.TransplantAngleHighZeros (sbox g0)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (FloorSumRate)
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)

namespace Cvs.Route.Visibility.RungBoxTunnellingSum
open Cvs.ZeroCounting

/-! ### Schwarz reflection on the box -/

/-- The data box is convex. -/
theorem convex_sbox (Y : ℝ) : Convex ℝ (sbox Y) := by
  have e : sbox Y = Complex.reLm ⁻¹' Ioo (-2) 3 ∩ Complex.imLm ⁻¹' Ioo (-Y) Y := by
    ext s; simp [sbox, abs_lt, and_assoc]
  rw [e]
  exact ((convex_Ioo _ _).linear_preimage _).inter ((convex_Ioo _ _).linear_preimage _)

/-- The data box is closed under conjugation. -/
theorem conj_mem_sbox {Y : ℝ} {s : ℂ} (hs : s ∈ sbox Y) : conj s ∈ sbox Y := by
  obtain ⟨h1, h2, h3⟩ := hs
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- **Schwarz reflection**: a function holomorphic on a connected conjugation-invariant open set that commutes with
conjugation near one point commutes with it everywhere on the set. -/
theorem conj_eqOn {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hpc : IsPreconnected U)
    (hcU : ∀ s ∈ U, conj s ∈ U) (hF : DifferentiableOn ℂ F U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (h : ∀ᶠ s in 𝓝 z₀, F (conj s) = conj (F s)) : ∀ s ∈ U, F (conj s) = conj (F s) := by
  have hG : DifferentiableOn ℂ (conj ∘ F ∘ conj) U := fun s hs => by
    have hd : DifferentiableAt ℂ F (conj s) := hF.differentiableAt (hU.mem_nhds (hcU s hs))
    have := hd.hasDerivAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableAt.differentiableWithinAt
  have heq := (hF.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hU) hpc hz₀
    (h.mono fun s hs => by simp only [Function.comp_apply, hs, Complex.conj_conj])
  intro s hs
  have := heq (hcU s hs)
  simp only [Function.comp_apply, Complex.conj_conj] at this
  exact this

/-- A continuation of `X_{e_j} + g0_j/(2(1 − s))` to the box commutes with conjugation there. -/
theorem conj_of_agree {x : ℕ} (hx0 : (0 : ℝ) < x) {j : Cvs.Approximant.SpineSubspace.SF x} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (sbox x))
    (hagree : ∀ s ∈ sbox x, s.re < 1 → F s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
        + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))) :
    ∀ s ∈ sbox x, F (conj s) = conj (F s) := by
  have h0 : (0 : ℂ) ∈ sbox x := ⟨by simp, by simp, by simpa using hx0⟩
  have hV : IsOpen (sbox x ∩ {s : ℂ | s.re < 1}) :=
    (Cvs.StepA.Edge.TransplantAngleHighZeros.isOpen_sbox x).inter (isOpen_lt Complex.continuous_re continuous_const)
  refine conj_eqOn (Cvs.StepA.Edge.TransplantAngleHighZeros.isOpen_sbox x) (convex_sbox x).isPreconnected (fun s hs => conj_mem_sbox hs) hF h0 ?_
  filter_upwards [hV.mem_nhds ⟨h0, by simp⟩] with s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hc1 : (conj s).re < 1 := by simpa using hs2
  rw [hagree s hs1 hs2, hagree (conj s) (conj_mem_sbox hs1) hc1, map_add, Cvs.WeilForm.ThetaSpaceParseval.mellinR_conj, map_div₀,
    map_mul, map_sub, map_one, Complex.conj_ofReal, map_ofNat]

/-! ### The per-rung exterior statement -/

/-- **The per-rung exterior box bound with exponent `η`** (caseinf-W Lemma 2_j): eventually every rung's
`X_{e_j} + g0_j/(2(1 − s))` continues holomorphically to the box of height `x` with sup at most
`Q(x)x⁻¹√((1 − λ_j)^{½+η})`, `Q` subpolynomial. -/
def RungXBox (η : ℝ) : Prop :=
  ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∃ F : ℂ → ℂ,
    DifferentiableOn ℂ F (sbox x)
      ∧ (∀ s ∈ sbox x, s.re < 1 → F s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
          + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)))
      ∧ ∀ s ∈ sbox x, ‖F s‖ ≤ Q x / x * √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))

/-- A larger exponent gives a smaller bound: `RungXBox η₁ → RungXBox η₀` for `0 ≤ ½ + η₀ ≤ ½ + η₁`. -/
theorem rungXBox_mono {η₀ η₁ : ℝ} (h0 : 0 ≤ 1 / 2 + η₀) (h01 : η₀ ≤ η₁) (h : RungXBox η₁) : RungXBox η₀ := by
  obtain ⟨Q, hQ, hev⟩ := h
  refine ⟨fun x => max (Q x) 0, Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ, ?_⟩
  filter_upwards [hev, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx hsc j
  obtain ⟨F, hF, ha, hb⟩ := hx j
  refine ⟨F, hF, ha, fun s hs => (hb s hs).trans ?_⟩
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc
  have hjx := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc hjx
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one (by linarith) (Cvs.Prolate.RungFamilyRangePartners.exists_main hsc ⟨j, Finset.mem_range.2 hjx⟩)
  have hw : (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η₁)
      ≤ (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η₀) :=
    Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) h0 (by linarith)
  exact mul_le_mul (div_le_div_of_nonneg_right (le_max_left _ _) hx0.le) (Real.sqrt_le_sqrt hw)
    (sqrt_nonneg _) (div_nonneg (le_max_right _ _) hx0.le)

/-! ### Assembly -/

/-- The per-rung bound `ν_j = (Q + 4/π)x⁻¹√((1 − λ_j)^{½+η})`. -/
def nu (Q : ℕ → ℝ) (η : ℝ) (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ :=
  (max (Q x) 0 + 4 / π) / x * √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))

/-- `(A/r²)W/√(σ/r²) = A(r²)^{−1/2}(W/√σ)`. -/
theorem arith_term {A W σ r : ℝ} (hr : 0 < r) (hσ : 0 < σ) :
    A / r ^ 2 * W / √(σ / r ^ 2) = A * (r ^ 2) ^ (-(1 / 2 : ℝ)) * (W / √σ) := by
  rw [Real.sqrt_div hσ.le, Real.sqrt_sq hr.le, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hr.le]
  have : 0 < √σ := Real.sqrt_pos.2 hσ
  field_simp

/-- **The floor sum of `ν`**: with `CaseFiniteFromWindowChain`'s `ExtTunnelSum η` and `Q` subpolynomial, `Σ_j ν_j/√(σ'_j/x) ≤
C_ε x^{−1/2+ε}`. -/
theorem floorSumRate_nu {Q : ℕ → ℝ} {η : ℝ} (hQ : SubPoly Q) (hT : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η) :
    FloorSumRate Cvs.Route.Visibility.CaseFiniteFromWindowChain.sigmaFloor (nu Q η) (-1 / 2) := fun ε hε => by
  obtain ⟨C, hC⟩ := hT (ε / 2) (by linarith)
  refine ⟨(1 + 4 / π) * max C 0, ?_⟩
  filter_upwards [hC, hQ (ε / 2) (by linarith), Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x h1 h2 hsc
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hsc
  set A := max (Q x) 0 + 4 / π
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ j : Cvs.Approximant.SpineSubspace.SF x, nu Q η x j / √(Cvs.Route.Visibility.CaseFiniteFromWindowChain.sigmaFloor x j)
      = A * (x : ℝ) ^ (-(1 / 2 : ℝ)) * (√((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
          / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j))) := fun j => by
    have hσ := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hsc) (finOfSF j)
    unfold nu Cvs.Route.Visibility.CaseFiniteFromWindowChain.sigmaFloor
    have := arith_term (A := A) (W := √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η)))
      (Real.sqrt_pos.2 hx0) hσ
    rwa [Real.sq_sqrt hx0.le] at this
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum]
  have hAx : A ≤ (1 + 4 / π) * (x : ℝ) ^ (ε / 2) := by
    have hp : 1 ≤ (x : ℝ) ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
    have : max (Q x) 0 ≤ (x : ℝ) ^ (ε / 2) := max_le h2 (by positivity)
    have h4 : 4 / π * 1 ≤ 4 / π * (x : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left hp (by positivity)
    simp only [A]; linarith
  have hS : ∑ j : Cvs.Approximant.SpineSubspace.SF x, √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
      / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)) ≤ max C 0 * (x : ℝ) ^ (ε / 2) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hS0 : 0 ≤ ∑ j : Cvs.Approximant.SpineSubspace.SF x, √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η))
      / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)) := Finset.sum_nonneg fun _ _ => by positivity
  have hxe : (x : ℝ) ^ (-(1 / 2 : ℝ)) * (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) = (x : ℝ) ^ (-1 / 2 + ε) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  calc A * (x : ℝ) ^ (-(1 / 2 : ℝ)) * _
      ≤ ((1 + 4 / π) * (x : ℝ) ^ (ε / 2)) * (x : ℝ) ^ (-(1 / 2 : ℝ)) * (max C 0 * (x : ℝ) ^ (ε / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hAx (by positivity)) hS hS0 (by positivity)
    _ = (1 + 4 / π) * max C 0 * ((x : ℝ) ^ (-(1 / 2 : ℝ)) * (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2)) := by ring
    _ = (1 + 4 / π) * max C 0 * (x : ℝ) ^ (-1 / 2 + ε) := by rw [hxe]

/-- **`RungBox 1` from the per-rung exterior bound and the tunnelling sum**: `RungXBox η₁`, `CaseFiniteFromWindowChain`'s `ExtTunnelSum η₀`,
`0 < η₀ ≤ η₁`, `η₀ ≤ ½`. -/
theorem rungBox_one {η₀ η₁ : ℝ} (h0 : 0 < η₀) (h01 : η₀ ≤ η₁) (h12 : η₀ ≤ 1 / 2) (hX : RungXBox η₁)
    (hT : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η₀) : Cvs.Route.Visibility.PerRungBoxBound.RungBox 1 := by
  obtain ⟨Q, hQ, hev⟩ := rungXBox_mono (by linarith) h01 hX
  have hev' : ∀ᶠ x : ℕ in atTop, (0 : ℝ) < x ∧ (80 : ℝ) ≤ 2 * π * x ∧ ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (sbox x)
      ∧ (∀ s ∈ sbox x, s.re < 1 → F s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
          + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)))
      ∧ ∀ s ∈ sbox x, ‖F s‖ ≤ Q x / x * √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η₀)) := by
    filter_upwards [hev, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx hsc
    exact ⟨Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc, hsc, hx⟩
  classical
  let F : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℂ → ℂ := fun x j =>
    if h : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (sbox x)
      ∧ (∀ s ∈ sbox x, s.re < 1 → F s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
          + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)))
      ∧ ∀ s ∈ sbox x, ‖F s‖ ≤ Q x / x * √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η₀))
    then h.choose else 0
  refine ⟨F, nu Q η₀, ?_, by simpa using floorSumRate_nu hQ hT⟩
  filter_upwards [hev'] with x ⟨hx0, hsc, hx⟩ j
  have hex := hx j
  have hFj : F x j = hex.choose := dif_pos hex
  obtain ⟨hd, ha, hb⟩ := hex.choose_spec
  rw [← hFj] at hd ha hb
  have hjx := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc hjx
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one (by linarith) (Cvs.Prolate.RungFamilyRangePartners.exists_main hsc ⟨j, Finset.mem_range.2 hjx⟩)
  set w := 1 - lamR (2 * π * x) (2 * (j : ℕ))
  have hw0 : 0 ≤ w := by simp only [w]; linarith
  have hw1 : w ≤ 1 := by simp only [w]; linarith
  have hsq0 : 0 ≤ √(w ^ (1 / 2 + η₀)) := sqrt_nonneg _
  refine ⟨hd, conj_of_agree hx0 hd ha, ha, fun s hs => (hb s hs).trans ?_, ?_⟩
  · unfold nu
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (by have := le_max_left (Q x) 0; have : 0 < 4 / π := by positivity
          linarith) hx0.le) hsq0
  · have hg := Cvs.Prolate.Envelope.RungCentreBound.abs_g0_single_le hsc j
    have hww : √w ≤ √(w ^ (1 / 2 + η₀)) := by
      refine Real.sqrt_le_sqrt ?_
      have := Real.rpow_le_rpow_of_exponent_ge' hw0 hw1 (by linarith : (0 : ℝ) ≤ 1 / 2 + η₀)
        (by linarith : 1 / 2 + η₀ ≤ 1)
      rwa [Real.rpow_one] at this
    refine hg.trans ?_
    unfold nu
    calc 4 / π / x * √w ≤ 4 / π / x * √(w ^ (1 / 2 + η₀)) := mul_le_mul_of_nonneg_left hww (by positivity)
      _ ≤ (max (Q x) 0 + 4 / π) / x * √(w ^ (1 / 2 + η₀)) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith [le_max_right (Q x) 0]) hx0.le) hsq0

/-- **`RungBox 1` in the route's form**: the tunnelling sum for some `η ∈ (0, ½)` and the per-rung exterior bound
for every `η ∈ (0, ½)`. -/
theorem rungBox_one_of_tunnel (hT : ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η)
    (hX : ∀ η : ℝ, 0 < η → η < 1 / 2 → RungXBox η) : Cvs.Route.Visibility.PerRungBoxBound.RungBox 1 := by
  obtain ⟨η, h0, h1, hη⟩ := hT
  exact rungBox_one h0 le_rfl h1.le (hX η h0 h1) hη

end Cvs.Route.Visibility.RungBoxTunnellingSum

end
