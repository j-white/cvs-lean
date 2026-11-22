import Mathlib
import Cvs.L2a.RadialCutArchChannel
import Cvs.L2a.RadialCutPastEnergyPoint
import Cvs.L2a.WeightedArcsineDiagonal
import Cvs.Prolate.ExteriorMassEdgeLayer
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.RadialCutResolvent
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The local pieces of the edge layer

For a radial solution with `0 ≤ χ < c²`, `c ≥ 1`, `1 ≤ M ≤ ξ₀`, `ξ₀² ≤ 2`, `δ = ξ₀ − 1` and
`K₀ = |log(c/π)| + |a(0)| + 57/(2c)`: `∫_M^{ξ₀} ψ² ≤ δψ(1)²`,
`|∫_M^{ξ₀} ψ² a(ν)| ≤ K₀ ∫_M^{ξ₀} ψ² + ψ(1)²(δ/2)(1 − log δ)`, and past `ξ₀` (with `w(ξ₀) < 2`)
`∫_{ξ₀}^∞ ψ²(a(ν) − a(0)) ≤ K₀ ∫_{ξ₀}^∞ ψ² + (G/√(c² − χ)) ℓ(arcsin(1/ξ₀))`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (wP)

namespace Cvs.L2a.EdgeLayerLocalPieces
open Cvs.ZeroCounting

section Radial

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)

include hψ hv hode in
theorem sq_le_edge (hχ : χ < c ^ 2) {w : ℝ} (hw : 1 ≤ w) : ψ w ^ 2 ≤ ψ 1 ^ 2 :=
  Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge (ξ₁ := w) hχ ⟨hw, le_rfl⟩ (fun r hr => hψ r hr.1) (fun r hr => hv r hr.1)
    (fun r hr => hode r hr.1)

include hψ hv hode in
/-- `∫_M^{ξ₀} ψ² ≤ (ξ₀ − 1)ψ(1)²`. -/
theorem integral_edge_sq_le (hχ : χ < c ^ 2) {M ξ₀ : ℝ} (hM : 1 ≤ M) (hMξ : M ≤ ξ₀) :
    ∫ w in Ioc M ξ₀, ψ w ^ 2 ≤ (ξ₀ - 1) * ψ 1 ^ 2 := by
  calc ∫ w in Ioc M ξ₀, ψ w ^ 2 ≤ ∫ w in Ioc M ξ₀, ψ 1 ^ 2 := by
        refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Ioc fun w hw =>
          sq_le_edge hψ hv hode hχ (le_trans hM hw.1.le)
        have hc : ContinuousOn (fun w => ψ w ^ 2) (Icc M ξ₀) := fun w hw =>
          ((hψ w (le_trans hM hw.1)).continuousAt.pow 2).continuousWithinAt
        exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    _ = (ξ₀ - M) * ψ 1 ^ 2 := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hMξ, smul_eq_mul]
    _ ≤ (ξ₀ - 1) * ψ 1 ^ 2 := by gcongr

omit hψ hv hode in
/-- `|a(ν)| ≤ K₀ + lw` past `1`. -/
theorem abs_arch_le {w : ℝ} (hc : 1 ≤ c) (hw : 1 < w) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)|
      ≤ |Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c) + Cvs.L2a.WeightedArcsineDiagonal.lw w := by
  have h1 := Cvs.L2a.WeightedArcsineDiagonal.abs_archSymbol_nuLoc_le hc hw
  have hl := Cvs.L2a.WeightedArcsineDiagonal.lw_nonneg hw
  have := abs_nonneg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
  rw [abs_le] at h1 ⊢
  constructor
  · have := neg_abs_le (Real.log (c / π)); have : 0 < 57 / (2 * c) := by positivity
    linarith [h1.1]
  · have := le_abs_self (Real.log (c / π)); linarith [h1.2]

include hψ hv hode in
/-- **The local term on the edge layer**:
`|∫_M^{ξ₀} ψ² a(ν)| ≤ K₀ ∫_M^{ξ₀} ψ² + ψ(1)²(δ/2)(1 − log δ)`, `δ = ξ₀ − 1`, for `ξ₀² ≤ 2`. -/
theorem abs_integral_edge_arch_le (hc : 1 ≤ c) (hχ : χ < c ^ 2) {M ξ₀ : ℝ} (hM : 1 ≤ M) (hMξ : M ≤ ξ₀)
    (h1 : 1 < ξ₀) (hξ2 : ξ₀ ^ 2 ≤ 2) :
    |∫ w in Ioc M ξ₀, ψ w ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)|
      ≤ (|Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c)) * (∫ w in Ioc M ξ₀, ψ w ^ 2)
        + ψ 1 ^ 2 * ((ξ₀ - 1) / 2 * (1 - Real.log (ξ₀ - 1))) := by
  set K0 := |Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c) with hK0
  have hψc : ContinuousOn (fun w => ψ w ^ 2) (Icc M ξ₀) := fun w hw =>
    ((hψ w (le_trans hM hw.1)).continuousAt.pow 2).continuousWithinAt
  have hsqi : IntegrableOn (fun w => ψ w ^ 2) (Ioc M ξ₀) :=
    (hψc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hlogI : IntegrableOn (fun w => -(Real.log (w - 1) / 2)) (Ioc 1 ξ₀) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := 1 - 1) (b := ξ₀ - 1)).comp_sub_right 1
    simp only [sub_add_cancel] at h
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1.le).mp ((h.div_const 2).neg))
  have hdom : ∀ w ∈ Ioc M ξ₀, |ψ w ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)|
      ≤ K0 * ψ w ^ 2 + ψ 1 ^ 2 * (-(Real.log (w - 1) / 2)) := by
    intro w hw
    have hw1 : 1 < w := lt_of_le_of_lt hM hw.1
    have hw2 : w ^ 2 ≤ 2 := le_trans (pow_le_pow_left₀ (by linarith) hw.2 2) hξ2
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have ha := abs_arch_le (c := c) hc hw1
    have hl := Cvs.L2a.WeightedArcsineDiagonal.lw_le_edge hw1 hw2
    have hl0 := Cvs.L2a.WeightedArcsineDiagonal.lw_nonneg hw1
    have hs := sq_le_edge hψ hv hode hχ hw1.le
    calc ψ w ^ 2 * |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)|
        ≤ ψ w ^ 2 * (K0 + Cvs.L2a.WeightedArcsineDiagonal.lw w) := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
      _ = K0 * ψ w ^ 2 + ψ w ^ 2 * Cvs.L2a.WeightedArcsineDiagonal.lw w := by ring
      _ ≤ K0 * ψ w ^ 2 + ψ 1 ^ 2 * (-(Real.log (w - 1) / 2)) := by
          have := mul_le_mul hs hl hl0 (sq_nonneg _)
          linarith
  have hmaj : IntegrableOn (fun w => K0 * ψ w ^ 2 + ψ 1 ^ 2 * (-(Real.log (w - 1) / 2))) (Ioc M ξ₀) :=
    (hsqi.const_mul K0).add ((hlogI.mono_set (Ioc_subset_Ioc_left hM)).const_mul _)
  calc |∫ w in Ioc M ξ₀, ψ w ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)|
      ≤ ∫ w in Ioc M ξ₀, |ψ w ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w in Ioc M ξ₀, (K0 * ψ w ^ 2 + ψ 1 ^ 2 * (-(Real.log (w - 1) / 2))) := by
        refine setIntegral_mono_on ?_ hmaj measurableSet_Ioc hdom
        refine Integrable.mono' hmaj ?_ ?_
        · have hac : ContinuousOn (fun w => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w))
              (Ioc M ξ₀) := (Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.comp_continuousOn
                (Cvs.L2a.WeightedArcsineDiagonal.continuousOn_nuLoc c)).mono fun w hw => lt_of_le_of_lt hM hw.1
          exact ((hψc.mono Ioc_subset_Icc_self).mul hac).abs.aestronglyMeasurable measurableSet_Ioc
        · rw [ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall fun w hw => by rw [Real.norm_eq_abs, abs_abs]; exact hdom w hw
    _ = K0 * (∫ w in Ioc M ξ₀, ψ w ^ 2) + ψ 1 ^ 2 * ∫ w in Ioc M ξ₀, -(Real.log (w - 1) / 2) := by
        rw [integral_add (hsqi.const_mul K0) ((hlogI.mono_set (Ioc_subset_Ioc_left hM)).const_mul _),
          integral_const_mul, integral_const_mul]
    _ ≤ K0 * (∫ w in Ioc M ξ₀, ψ w ^ 2) + ψ 1 ^ 2 * ∫ w in Ioc 1 ξ₀, -(Real.log (w - 1) / 2) := by
        gcongr
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun w hw => ?_
        have : Real.log (w - 1) ≤ 0 := Real.log_nonpos (by linarith [hw.1]) (by nlinarith [hw.2])
        simp only [Pi.zero_apply]; linarith
    _ = _ := by
        rw [← intervalIntegral.integral_of_le h1.le, show ξ₀ = 1 + (ξ₀ - 1) by ring,
          Cvs.L2a.WeightedArcsineDiagonal.integral_neg_log_sub]
        ring_nf

include hψ hv hode in
/-- **The local term past `ξ₀`**: `∫_{ξ₀}^∞ ψ²(a(ν) − a(0)) ≤ K₀ ∫_{ξ₀}^∞ ψ² + C ℓ(arcsin(1/ξ₀))`. -/
theorem integral_arch_sub_le {B : ℝ} (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ : ℝ} (h1 : 1 < ξ₀)
    (hW : wP c χ ξ₀ < 2) (hB : ∀ w, 1 ≤ w → |ψ w| ≤ B / w) :
    ∫ w in Ioi ξ₀, ψ w ^ 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
      ≤ (|Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c)) * (∫ w in Ioi ξ₀, ψ w ^ 2)
        + Cvs.L2a.RadialCutPastEnergyPoint.Gen c χ ψ v ξ₀ / √(c ^ 2 - χ) * Cvs.L2a.WeightedArcsineDiagonal.ell (arcsin (1 / ξ₀)) := by
  have hc0 : 0 < c := by linarith
  set K0 := |Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c) with hK0
  set C := Cvs.L2a.RadialCutPastEnergyPoint.Gen c χ ψ v ξ₀ / √(c ^ 2 - χ) with hC
  have hsq := Cvs.L2a.RadialCutArchChannel.integrableOn_sq hψ hB h1.le
  have hgi := Cvs.L2a.RadialCutArchChannel.integrableOn_sq_mul_arch hψ hc hB h1.le
  have hrl := Cvs.L2a.WeightedArcsineDiagonal.integrableOn_rr_lw h1.le
  have hmaj : IntegrableOn (fun w => K0 * ψ w ^ 2 + C * (Cvs.L2a.WeightedArcsineDiagonal.rr w * Cvs.L2a.WeightedArcsineDiagonal.lw w))
      (Ioi ξ₀) := (hsq.const_mul K0).add (hrl.const_mul C)
  calc ∫ w in Ioi ξ₀, ψ w ^ 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w)
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
      ≤ ∫ w in Ioi ξ₀, (K0 * ψ w ^ 2 + C * (Cvs.L2a.WeightedArcsineDiagonal.rr w * Cvs.L2a.WeightedArcsineDiagonal.lw w)) := by
        refine setIntegral_mono_on hgi hmaj measurableSet_Ioi fun w hw => ?_
        have hw1 : 1 < w := lt_trans h1 hw
        have hal := Cvs.L2a.RadialCutPastEnergyPoint.alf_le (c := c) hc hw1
        have hl0 := Cvs.L2a.WeightedArcsineDiagonal.lw_nonneg hw1
        obtain ⟨hP, -, -⟩ := Cvs.L2a.RadialCutPastEnergyPoint.energy_env hψ hv hode hc0 hχ0 hχ h1 hW (le_of_lt hw)
        rw [sq_abs] at hP
        have hP' : ψ w ^ 2 ≤ C * Cvs.L2a.WeightedArcsineDiagonal.rr w := by
          rw [Cvs.L2a.RadialCutPastEnergyPoint.rr_eq, mul_one_div]; exact hP
        have : ψ w ^ 2 * Cvs.L2a.WeightedArcsineDiagonal.lw w ≤ C * Cvs.L2a.WeightedArcsineDiagonal.rr w * Cvs.L2a.WeightedArcsineDiagonal.lw w :=
          mul_le_mul_of_nonneg_right hP' hl0
        unfold Cvs.L2a.RadialCutPastEnergyPoint.alf at hal
        nlinarith [sq_nonneg (ψ w)]
    _ = _ := by
        rw [integral_add (hsq.const_mul K0) (hrl.const_mul C), integral_const_mul, integral_const_mul,
          Cvs.L2a.WeightedArcsineDiagonal.integral_rr_lw h1.le]

end Radial

end Cvs.L2a.EdgeLayerLocalPieces
