import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.GreenTailCancellation
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.StepQuadratureResidual
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Radial Monotonicity of `truncSymbol`, `augShiftedScaleSymbol`, and Three-Band Coercivity

Proves radial monotonicity of `truncSymbol` and `shiftedTruncSymbol`, unconditional high-band floor
discharges, band-free boundary cosine augmentation `augShiftedScaleSymbol`, and three-band coercivity.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Cvs.WeilForm.TruncSymbolMonotone
open Cvs.ZeroCounting

/-! ### 1. Radial Monotonicity of `truncSymbol` and `shiftedTruncSymbol` -/

theorem bIdx_pos (n : ℕ) : 0 < Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx n := by
  unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; positivity

/-- At `t = 0`, each Lévy channel deficit `digammaDeficit 0 n` vanishes. -/
theorem digammaDeficit_zero (n : ℕ) : Cvs.Zeta.digammaDeficit 0 n = 0 := by
  rw [← Cvs.WeilForm.Archimedean.TruncationBelowSymbol.gap_eq_deficit, Cvs.WeilForm.Archimedean.TruncationBelowSymbol.peak_eq, sub_self]

/-- Each Lévy channel deficit `digammaDeficit t n` is radially nondecreasing in `|t|`. -/
theorem digammaDeficit_mono_abs (n : ℕ) {s t : ℝ} (h : |s| ≤ |t|) :
    Cvs.Zeta.digammaDeficit s n ≤ Cvs.Zeta.digammaDeficit t n := by
  rw [← Cvs.WeilForm.Archimedean.TruncationBelowSymbol.gap_eq_deficit, ← Cvs.WeilForm.Archimedean.TruncationBelowSymbol.gap_eq_deficit]
  refine sub_le_sub_left ?_ _
  have hb : 0 < Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx n := bIdx_pos n
  have hsq : s ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs s, ← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg s) h 2
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- `truncSymbol N t = archSymbol 0 + ∑_{n < N} digammaDeficit t n`. -/
theorem truncSymbol_eq_zero_add_sum_deficit (N : ℕ) (t : ℝ) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N t
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + ∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit t n := by
  unfold Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun n _ => Cvs.WeilForm.Archimedean.TruncationBelowSymbol.gap_eq_deficit t n

/-- At `t = 0`, `truncSymbol N 0 = archSymbol 0` for every truncation order `N`. -/
theorem truncSymbol_zero_right (N : ℕ) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N 0 = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 := by
  rw [truncSymbol_eq_zero_add_sum_deficit]
  simp [digammaDeficit_zero]

/-- Increment `truncSymbol N t − archSymbol 0 = ∑_{n < N} digammaDeficit t n`. -/
theorem truncSymbol_sub_archSymbol_zero (N : ℕ) (t : ℝ) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      = ∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit t n := by
  rw [truncSymbol_eq_zero_add_sum_deficit, add_sub_cancel_left]

/-- **Radial Monotonicity of `truncSymbol`**: `|s| ≤ |t|` implies `truncSymbol N s ≤ truncSymbol N t`. -/
theorem truncSymbol_mono_abs (N : ℕ) {s t : ℝ} (h : |s| ≤ |t|) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N s ≤ Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N t := by
  rw [truncSymbol_eq_zero_add_sum_deficit, truncSymbol_eq_zero_add_sum_deficit]
  exact add_le_add_right (Finset.sum_le_sum fun n _ => digammaDeficit_mono_abs n h) _

/-- `archSymbol 0 ≤ truncSymbol N t` for all `N : ℕ` and `t : ℝ`. -/
theorem archSymbol_zero_le_truncSymbol (N : ℕ) (t : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N t := by
  rw [← truncSymbol_zero_right N]
  exact truncSymbol_mono_abs N (by simp only [abs_zero, abs_nonneg])

/-- **Unconditional High-Band Archimedean Lower Bound**: for `0 ≤ T ≤ |t|`,
`truncSymbol N T ≤ archSymbol t` for every `N : ℕ` (with no lower threshold on `T`). -/
theorem truncSymbol_le_archSymbol_of_abs_ge (N : ℕ) {T t : ℝ} (hT : 0 ≤ T) (ht : T ≤ |t|) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N T ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t :=
  (truncSymbol_mono_abs N (by rwa [abs_of_nonneg hT])).trans (Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol_le N t)

/-! ### 2. Unconditional Rational High-Band Discharges for `archTerm`, `BulkFloor`, and Range Positivity -/

/-- **Rational High-Band Lower Bound on `archTerm`** (`0 ≤ L`, `0 ≤ T`):
`truncSymbol N T · ‖φ‖² − (∑_{n < N} digammaDeficit T n) ∫_{|t| < T} ρ_φ ≤ archTerm (rep φ)`. -/
theorem archTerm_rep_ge_truncSymbol {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (N : ℕ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N T * ‖φ‖ ^ 2
        - (∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit T n)
          * (∫ t in {t : ℝ | |t| < T}, Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  have h := Cvs.WeilForm.WindowCircleIsometry.archTerm_rep_ge_floor_sub_lowBand hL
    (fun t ht => truncSymbol_le_archSymbol_of_abs_ge N hT ht) φ
  rwa [truncSymbol_sub_archSymbol_zero] at h

/-! ### 3. Band-Free Boundary Cosine Augmentation (`augShiftedScaleSymbol`) & Three-Band Coercivity -/

/-- **Boundary-Augmented Shifted Abel Scale Symbol**: adds the band-free boundary cosine
`C cos(t log x)` to `shiftedAbelScaleSymbol x t`, shifting the origin value to `archSymbol 0 + 4 + C`. -/
def augShiftedScaleSymbol (x : ℕ) (C : ℝ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.GreenTailCancellation.shiftedAbelScaleSymbol x t + C * Real.cos (t * Real.log x)

/-- `t ↦ C cos(t log x)` lies in `bandFree (log x)`. -/
theorem cos_log_mem_bandFree (x : ℕ) (C : ℝ) :
    (fun t => C * Real.cos (t * Real.log x)) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x) := by
  change C • (fun t => Real.cos (t * Real.log x)) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x)
  exact Submodule.smul_mem _ _ (Cvs.WeilForm.BandFreedomCosine.cos_mem_bandFree (le_abs_self _))

/-- `augShiftedScaleSymbol x C * rho w` is integrable on `Dom x` (`1 ≤ x`). -/
theorem integrable_augShiftedScaleSymbol_mul_rho {x : ℕ} (hx : 1 ≤ x) (C : ℝ)
    (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Integrable fun t => augShiftedScaleSymbol x C t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  refine ((Cvs.WeilForm.GreenTailCancellation.integrable_shiftedAbelScaleSymbol_mul_rho hx w).add
    (Cvs.WeilForm.EvenBulkVisibility.integrable_bandFree_mul_rho (cos_log_mem_bandFree x C) w)).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, augShiftedScaleSymbol]
  ring

/-- **Exact Spectral Identity for `augShiftedScaleSymbol`** (`1 ≤ x`): for every `C : ℝ` and `w : Dom x`,
`Qx x w = ∫ t, augShiftedScaleSymbol x C t * rho w t`. -/
theorem Qx_eq_integral_augShiftedScaleSymbol {x : ℕ} (hx : 1 ≤ x) (C : ℝ)
    (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x w = ∫ t, augShiftedScaleSymbol x C t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  have hsplit : (fun t => augShiftedScaleSymbol x C t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
      = fun t => Cvs.WeilForm.GreenTailCancellation.shiftedAbelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t
          + (C * Real.cos (t * Real.log x)) * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    funext t; unfold augShiftedScaleSymbol; ring
  rw [hsplit, integral_add (Cvs.WeilForm.GreenTailCancellation.integrable_shiftedAbelScaleSymbol_mul_rho hx w)
    (Cvs.WeilForm.EvenBulkVisibility.integrable_bandFree_mul_rho (cos_log_mem_bandFree x C) w),
    Cvs.WeilForm.EvenBulkVisibility.integral_bandFree_mul_rho (cos_log_mem_bandFree x C) w,
    add_zero, ← Cvs.WeilForm.GreenTailCancellation.Qx_eq_integral_shiftedAbelScaleSymbol hx w]

/-- **Origin-Neighborhood Coercivity of `augShiftedScaleSymbol`** (`0 ≤ C`):
`(archSymbol 0 + 4 + C) − (totalMeanFreeSlope (x - 1) + C log x) |t| ≤ augShiftedScaleSymbol x C t`. -/
theorem augShiftedScaleSymbol_ge_origin_sub_slope (x : ℕ) {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4 + C)
        - (Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope (x - 1) + C * Real.log x) * |t|
      ≤ augShiftedScaleSymbol x C t := by
  unfold augShiftedScaleSymbol
  have h1 := Cvs.WeilForm.GreenTailCancellation.shiftedAbelScaleSymbol_ge_origin_sub_slope x t
  have hcos : 1 - Real.log x * |t| ≤ Real.cos (t * Real.log x) := by
    have h2 := (abs_le.mp (Cvs.WeilForm.StepQuadratureResidual.abs_cos_sub_one_le (t * Real.log x))).1
    rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg x), mul_comm] at h2
    linarith
  have hCcos := mul_le_mul_of_nonneg_left hcos hC
  linarith

/-- **Three-Band Spectral Coercivity on `Qx`**: if `c_low ≤ Φ` on `|t| < T₁`, `c_mid ≤ Φ` on
`T₁ ≤ |t| < T₂`, and `c_high ≤ Φ` on `T₂ ≤ |t|`, then
`min c_low c_high · ‖w‖² − (min c_low c_high − c_mid) ∫_{T₁ ≤ |t| < T₂} ρ_w ≤ Qx x w`. -/
theorem Qx_ge_threeBand_of_symbol {x : ℕ} {Φ : ℝ → ℝ} {T₁ T₂ c_low c_mid c_high : ℝ}
    {w : Cvs.Route.L1FloorFromBulkD0.Dom x} (hQ : Cvs.Route.WindowPositivityBulkCoupling.Qx x w = ∫ t, Φ t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
    (hΦi : Integrable fun t => Φ t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
    (hlow : ∀ t, |t| < T₁ → c_low ≤ Φ t)
    (hmid : ∀ t, T₁ ≤ |t| → |t| < T₂ → c_mid ≤ Φ t)
    (hhigh : ∀ t, T₂ ≤ |t| → c_high ≤ Φ t) :
    min c_low c_high * ‖w‖ ^ 2
        - (min c_low c_high - c_mid)
          * (∫ t in {t : ℝ | T₁ ≤ |t| ∧ |t| < T₂}, Cvs.WeilForm.EvenBulkVisibility.rho w t)
      ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w := by
  set S : Set ℝ := {t : ℝ | T₁ ≤ |t| ∧ |t| < T₂} with hS
  have hSm : MeasurableSet S :=
    (isClosed_le continuous_const continuous_abs).measurableSet.inter
      (isOpen_lt continuous_abs continuous_const).measurableSet
  have hi : Integrable (Cvs.WeilForm.EvenBulkVisibility.rho w) := Cvs.WeilForm.EvenBulkVisibility.integrable_rho w
  have hind : Integrable (S.indicator (Cvs.WeilForm.EvenBulkVisibility.rho w)) := hi.indicator hSm
  have hpt : ∀ t,
      min c_low c_high * Cvs.WeilForm.EvenBulkVisibility.rho w t
          - (min c_low c_high - c_mid) * S.indicator (Cvs.WeilForm.EvenBulkVisibility.rho w) t
        ≤ Φ t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    intro t
    have hρ : 0 ≤ Cvs.WeilForm.EvenBulkVisibility.rho w t := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      have h1 : c_mid ≤ Φ t := hmid t ht.1 ht.2
      nlinarith [mul_le_mul_of_nonneg_right h1 hρ]
    · rw [Set.indicator_of_notMem ht]
      have h2 : min c_low c_high ≤ Φ t := by
        rcases lt_or_ge |t| T₁ with hlt | hge
        · exact (min_le_left c_low c_high).trans (hlow t hlt)
        · have hge₂ : T₂ ≤ |t| := by
            by_contra hlt₂
            exact ht ⟨hge, not_le.mp hlt₂⟩
          exact (min_le_right c_low c_high).trans (hhigh t hge₂)
      nlinarith [mul_le_mul_of_nonneg_right h2 hρ]
  have hint : ∫ t, (min c_low c_high * Cvs.WeilForm.EvenBulkVisibility.rho w t
          - (min c_low c_high - c_mid) * S.indicator (Cvs.WeilForm.EvenBulkVisibility.rho w) t)
      = min c_low c_high * ‖w‖ ^ 2
        - (min c_low c_high - c_mid) * (∫ t in S, Cvs.WeilForm.EvenBulkVisibility.rho w t) := by
    rw [integral_sub (hi.const_mul _) (hind.const_mul _),
      integral_const_mul, integral_const_mul, Cvs.WeilForm.EvenBulkVisibility.integral_rho w, integral_indicator hSm]
  rw [hQ, ← hint]
  exact integral_mono ((hi.const_mul _).sub (hind.const_mul _)) hΦi hpt

end Cvs.WeilForm.TruncSymbolMonotone
