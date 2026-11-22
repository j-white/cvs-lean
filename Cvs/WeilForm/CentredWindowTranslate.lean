import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# Moving a window test function to the centred window

    supp f ⊆ (0, L]  ⟹  supp (f (· + L/2)) ⊆ [−L/2, L/2]

and the self-convolution, the energy and `L²` membership are all unchanged, so results stated
for the centred window apply to a function supported in `(0, L]`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.CentredWindowTranslate

/-- **The translate is supported in the centred window.** -/
theorem support_translate {L : ℝ} {f : ℝ → ℝ}
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) :
    ∀ x, x ∉ Set.Icc (-(L / 2)) (L / 2) → f (x + L / 2) = 0 := by
  intro x hx
  refine hsupp _ (fun hmem => hx ?_)
  have h1 : 0 < x + L / 2 := hmem.1
  have h2 : x + L / 2 ≤ L := hmem.2
  exact ⟨by linarith, by linarith⟩

/-- **Translation does not move the self-convolution.** -/
theorem selfConvolution_translate (f : ℝ → ℝ) (c u : ℝ) :
    selfConvolution (fun x => f (x + c)) u = selfConvolution f u := by
  have hstep : (∫ s : ℝ, f (s + c) * f (s + u + c))
      = ∫ s : ℝ, f s * f (s + u) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => f y * f (y + u)) c
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [add_right_comm s u c]
  exact hstep

/-- **Translation does not move the energy.** -/
theorem integral_sq_translate (f : ℝ → ℝ) (c : ℝ) :
    (∫ x : ℝ, f (x + c) ^ 2) = ∫ x : ℝ, f x ^ 2 :=
  integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun x : ℝ => f x ^ 2) c

/-- **Translation preserves `L²` membership.** -/
theorem memLp_translate {f : ℝ → ℝ} (c : ℝ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun x => f (x + c)) 2 (volume : Measure ℝ) :=
  hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) c)

/-- **A window test function is integrable.**  Compact support and finite energy. -/
theorem integrable_of_support {L : ℝ} {f : ℝ → ℝ} (hL : 0 ≤ L)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) :
    Integrable f (volume : Measure ℝ) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) L)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hind : IntegrableOn f (Set.Ioc (0:ℝ) L) (volume : Measure ℝ) :=
    (hf.restrict (Set.Ioc (0:ℝ) L)).integrable (by norm_num)
  have := hind.integrable_indicator measurableSet_Ioc
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hsupp x hx]

end Cvs.WeilForm.CentredWindowTranslate
