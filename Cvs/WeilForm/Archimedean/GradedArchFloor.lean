import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaCriticalAsymptotic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The graded archimedean floor

For `2 ≤ T ≤ |t|`, `archSymbol t ≥ archSymbol T + log(|t|/T) − 114/T` (`DigammaCriticalAsymptotic` at `T` and `|t|`); against
`ρ ≥ 0` this adds `∫ ρ · log⁺(|t|/T)` to the `archSymbol T` floor, less `(114/T) ∫ ρ`.
-/

namespace Cvs.WeilForm.Archimedean.GradedArchFloor

open MeasureTheory Real
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

/-- The symbol is even: `archSymbol |t| = archSymbol t`. -/
theorem archSymbol_abs (t : ℝ) : archSymbol |t| = archSymbol t :=
  le_antisymm (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by rw [sq_abs]))
    (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by rw [sq_abs]))

/-- The symbol never drops below its value at the origin: `0 ≤ archSymbol T − archSymbol 0`. -/
theorem archSymbol_sub_zero_nonneg (T : ℝ) : 0 ≤ archSymbol T - archSymbol 0 :=
  sub_nonneg.mpr (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero T)

/-- For `2 ≤ T ≤ |t|`, `archSymbol T + log(|t|/T) − 114/T ≤ archSymbol t`. -/
theorem archSymbol_ge_add_log {T t : ℝ} (hT : 2 ≤ T) (ht : T ≤ |t|) :
    archSymbol T + Real.log (|t| / T) - 114 / T ≤ archSymbol t := by
  have hT0 : (0:ℝ) < T := by linarith
  have hs : 2 ≤ |t| := hT.trans ht
  have hs0 : (0:ℝ) < |t| := by linarith
  have hlo := (abs_le.mp (DigammaAsym.abs_re_digamma_sub_log_le |t| hs)).1
  have hhi := (abs_le.mp (DigammaAsym.abs_re_digamma_sub_log_le T hT)).2
  have hlog : Real.log (|t| / T) = Real.log (|t| / 2) - Real.log (T / 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have h57 : 57 / |t| ≤ 57 / T := div_le_div_of_nonneg_left (by norm_num) hT0 ht
  rw [← archSymbol_abs t]
  unfold archSymbol
  rw [hlog]
  have : 114 / T = 57 / T + 57 / T := by ring
  linarith

/-- The graded floor: `archSymbol T − (archSymbol T − archSymbol 0)·1_{|t|<T} − 114/T
+ max 0 (log(|t|/T)) ≤ archSymbol t` for `2 ≤ T`. -/
theorem archSymbol_graded {T : ℝ} (hT : 2 ≤ T) (t : ℝ) :
    archSymbol T - (archSymbol T - archSymbol 0) * Set.indicator {t : ℝ | |t| < T} (fun _ => (1 : ℝ)) t
        - 114 / T + max 0 (Real.log (|t| / T)) ≤ archSymbol t := by
  have hT0 : (0:ℝ) < T := by linarith
  have h114 : 0 ≤ 114 / T := by positivity
  by_cases ht : |t| < T
  · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | |t| < T} from ht), mul_one]
    have hmax : max 0 (Real.log (|t| / T)) = 0 := by
      apply max_eq_left
      apply Real.log_nonpos (by positivity)
      rw [div_le_one hT0]; exact ht.le
    rw [hmax]
    have := Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t
    linarith
  · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | |t| < T} from ht), mul_zero]
    have ht' : T ≤ |t| := not_lt.mp ht
    have hmax : max 0 (Real.log (|t| / T)) = Real.log (|t| / T) := by
      apply max_eq_right
      apply Real.log_nonneg
      rw [le_div_iff₀ hT0]; linarith
    rw [hmax]
    have := archSymbol_ge_add_log hT ht'
    linarith

/-- For `ρ ≥ 0` with `ρ` and `archSymbol · ρ` integrable and `2 ≤ T`, the function
`ρ t · max 0 (log(|t|/T))` is integrable. -/
theorem integrable_mul_logPlus (ρ : ℝ → ℝ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ)
    (hA : Integrable (fun t => archSymbol t * ρ t)) {T : ℝ} (hT : 2 ≤ T) :
    Integrable (fun t => ρ t * max 0 (Real.log (|t| / T))) := by
  have hmeas : Measurable (fun t : ℝ => max 0 (Real.log (|t| / T))) :=
    measurable_const.max ((measurable_abs.div_const T).log)
  refine Integrable.mono' (hA.add (hρ.const_mul (114 / T - archSymbol 0)))
    (hρ.aestronglyMeasurable.mul hmeas.aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
  intro t
  have hg := archSymbol_graded hT t
  have hd := archSymbol_sub_zero_nonneg T
  have hind : Set.indicator {t : ℝ | |t| < T} (fun _ => (1 : ℝ)) t ≤ 1 :=
    Set.indicator_le_self' (fun _ _ => zero_le_one) t
  have hm : max 0 (Real.log (|t| / T)) ≤ archSymbol t + (114 / T - archSymbol 0) := by
    nlinarith
  have hnn : 0 ≤ ρ t * max 0 (Real.log (|t| / T)) := mul_nonneg (hρ0 t) (le_max_left _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  simp only [Pi.add_apply]
  nlinarith [hρ0 t]

/-- The graded archimedean floor against a nonnegative density: `archSymbol T ∫ρ
− (archSymbol T − archSymbol 0) ∫_{|t|<T} ρ − (114/T) ∫ρ + ∫ ρ · max 0 (log(|t|/T))
≤ ∫ archSymbol · ρ` for `2 ≤ T`. -/
theorem integral_arch_ge_graded (ρ : ℝ → ℝ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ)
    (hA : Integrable (fun t => archSymbol t * ρ t)) {T : ℝ} (hT : 2 ≤ T) :
    archSymbol T * (∫ t, ρ t) - (archSymbol T - archSymbol 0) * (∫ t in {t : ℝ | |t| < T}, ρ t)
        - 114 / T * (∫ t, ρ t) + ∫ t, ρ t * max 0 (Real.log (|t| / T))
      ≤ ∫ t, archSymbol t * ρ t := by
  set S : Set ℝ := {t : ℝ | |t| < T} with hS
  have hSm : MeasurableSet S := (isOpen_lt continuous_abs continuous_const).measurableSet
  have hind : Integrable (S.indicator ρ) := hρ.indicator hSm
  have hL := integrable_mul_logPlus ρ hρ0 hρ hA hT
  have h1 := hρ.const_mul (archSymbol T)
  have h2 := hind.const_mul (archSymbol T - archSymbol 0)
  have h3 := hρ.const_mul (114 / T)
  have hint : ∫ t, (archSymbol T * ρ t - (archSymbol T - archSymbol 0) * S.indicator ρ t
        - 114 / T * ρ t + ρ t * max 0 (Real.log (|t| / T)))
      = archSymbol T * (∫ t, ρ t) - (archSymbol T - archSymbol 0) * (∫ t in S, ρ t)
        - 114 / T * (∫ t, ρ t) + ∫ t, ρ t * max 0 (Real.log (|t| / T)) := by
    have h12 : Integrable (fun t => archSymbol T * ρ t
        - (archSymbol T - archSymbol 0) * S.indicator ρ t) := h1.sub h2
    have h123 : Integrable (fun t => archSymbol T * ρ t
        - (archSymbol T - archSymbol 0) * S.indicator ρ t - 114 / T * ρ t) := h12.sub h3
    rw [integral_add h123 hL, integral_sub h12 h3, integral_sub h1 h2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_indicator hSm]
  rw [← hint]
  refine integral_mono (((h1.sub h2).sub h3).add hL) hA fun t => ?_
  have hg := archSymbol_graded hT t
  have hρt := hρ0 t
  have hiρ : S.indicator ρ t = ρ t * S.indicator (fun _ => (1 : ℝ)) t := by
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_one]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
  rw [hiρ]
  nlinarith

end Cvs.WeilForm.Archimedean.GradedArchFloor
