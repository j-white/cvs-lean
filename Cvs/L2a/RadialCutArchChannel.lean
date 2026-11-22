import Mathlib
import Cvs.L2a.WeightedArcsineDiagonal
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The arch channel of a radial cut is its local-frequency term plus a resolvent series

For a radial cut `F = 1_{(M,∞)}ψ` (`|ψ| ≤ B/w`, `|ψ'| ≤ B'`, `c ≥ 1`), with `ν = c w²/√(w² − 1)` and `b_n = 2n + ½`:
`archSpec F = ∫_M^∞ ψ² a(ν) + Σ_n (X_n + J_n − 2R_n)` whenever the series converges, where
`X_n = ∫_M^∞ ψ² 2c²w⁴(2 − w²)/D_n²`, `J_n = M(M² − 1)ψ(M)²/D_n(M)`, `R_n = ∫ f K_{b_n} E_{b_n}`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open Cvs.Zeta.Explicit.Weil (selfConvolution)
open Cvs.L2a.TailLogScaleTest (logScale)

namespace Cvs.L2a.RadialCutArchChannel
open Cvs.ZeroCounting

section Radial

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)

/-- `|ψ| ≤ B/w` gives `ψ² ≤ B² rr`. -/
theorem sq_le_rr {ψ : ℝ → ℝ} {B : ℝ} (hB : ∀ w, 1 ≤ w → |ψ w| ≤ B / w) {w : ℝ} (hw : 1 < w) :
    ψ w ^ 2 ≤ B ^ 2 * Cvs.L2a.WeightedArcsineDiagonal.rr w := by
  have hw0 : 0 < w := by linarith
  have hp : 0 < w ^ 2 - 1 := by nlinarith
  have h1 : ψ w ^ 2 ≤ B ^ 2 / w ^ 2 := by
    rw [← sq_abs, ← div_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB w hw.le) 2
  refine h1.trans ?_
  unfold Cvs.L2a.WeightedArcsineDiagonal.rr
  rw [div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  apply one_div_le_one_div_of_le (by positivity)
  have : √(w ^ 2 - 1) ≤ w := by rw [sqrt_le_left hw0.le]; linarith
  nlinarith [sqrt_nonneg (w ^ 2 - 1)]

omit hv hode in
include hψ in
theorem integrableOn_sq {B M : ℝ} (hB : ∀ w, 1 ≤ w → |ψ w| ≤ B / w) (hM : 1 ≤ M) :
    IntegrableOn (fun w => ψ w ^ 2) (Ioi M) :=
  Cvs.L2a.WeightedArcsineDiagonal.integrableOn_of_le_rr (fun w hw => ((hψ w (mem_Ici.mpr (le_of_lt hw))).continuousAt.pow 2).continuousWithinAt)
    (fun _ _ => sq_nonneg _) (fun _ hw => sq_le_rr hB hw) hM

omit hv hode in
include hψ in
/-- `ψ²` against the local symbol increment is integrable past a cut. -/
theorem integrableOn_sq_mul_arch {B M : ℝ} (hc : 1 ≤ c) (hB : ∀ w, 1 ≤ w → |ψ w| ≤ B / w) (hM : 1 ≤ M) :
    IntegrableOn (fun w => ψ w ^ 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) (Ioi M) := by
  have hc0 : 0 < c := by linarith
  have hψc : ContinuousOn (fun w => ψ w ^ 2) (Ioi 1) := fun w hw =>
    ((hψ w (mem_Ici.mpr (le_of_lt hw))).continuousAt.pow 2).continuousWithinAt
  have hrr : ∀ w, 1 < w → ψ w ^ 2 ≤ B ^ 2 * Cvs.L2a.WeightedArcsineDiagonal.rr w := fun w hw => sq_le_rr hB hw
  have hlw := Cvs.L2a.WeightedArcsineDiagonal.integrableOn_mul_lw hψc (fun w _ => sq_nonneg (ψ w)) hrr hM
  have hsq := Cvs.L2a.WeightedArcsineDiagonal.integrableOn_of_le_rr hψc (fun w _ => sq_nonneg (ψ w)) hrr hM
  set K0 := |Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c) with hK0
  refine Integrable.mono' (hsq.mul_const K0 |>.add hlw) ?_ ?_
  · have hac : ContinuousOn (fun w => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)) (Ioi 1) :=
      Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.comp_continuousOn (Cvs.L2a.WeightedArcsineDiagonal.continuousOn_nuLoc c)
    exact ((hψc.mul (hac.sub continuousOn_const)).mono (Ioi_subset_Ioi hM)).aestronglyMeasurable measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun w hw => ?_
    have hw1 : 1 < w := lt_of_le_of_lt hM hw
    have h0 := Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)
    have h1 := Cvs.L2a.WeightedArcsineDiagonal.abs_archSymbol_nuLoc_le hc hw1
    have hl := Cvs.L2a.WeightedArcsineDiagonal.lw_nonneg hw1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg h0]
    have hle : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
        ≤ K0 + Cvs.L2a.WeightedArcsineDiagonal.lw w := by
      rw [hK0]
      have := (abs_le.mp h1).2
      have := le_abs_self (Real.log (c / π))
      have := neg_abs_le (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
      linarith
    calc ψ w ^ 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) ≤ ψ w ^ 2 * (K0 + Cvs.L2a.WeightedArcsineDiagonal.lw w) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = ψ w ^ 2 * K0 + ψ w ^ 2 * Cvs.L2a.WeightedArcsineDiagonal.lw w := by ring

end Radial

end Cvs.L2a.RadialCutArchChannel
