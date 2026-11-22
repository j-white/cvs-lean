import Mathlib
import Cvs.WeilForm.Mollify.MollifiedSliceL2
import Cvs.WeilForm.Mollify.MollifyL2Contraction

/-!
# Mollification does not increase the shifted energy

    ∫ ((f⋆ρ)(s) − (f⋆ρ)(s+v))² ds  ≤  ∫ (f s − f (s+v))² ds

because mollification commutes with the shifted difference, so `Cvs.WeilForm.Mollify.MollifyL2Contraction` applies to it directly.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifyShiftedEnergy

variable {f ρ : ℝ → ℝ}

/-- The mollification integral. -/
def conv (f ρ : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t : ℝ, f (s - t) * ρ t

/-- Each slice is integrable. -/
theorem integrable_slice (hf : MemLp f 2 (volume : Measure ℝ)) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (s : ℝ) :
    Integrable (fun t : ℝ => f (s - t) * ρ t) (volume : Measure ℝ) := by
  have hrefl := Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_reflect_translate hf s
  have hρL : MemLp ρ 2 (volume : Measure ℝ) :=
    hρc.memLp_of_hasCompactSupport hρs
  exact hrefl.integrable_mul hρL

/-- **Mollification commutes with the shifted difference.** -/
theorem conv_sub (hf : MemLp f 2 (volume : Measure ℝ)) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (s v : ℝ) :
    conv f ρ s - conv f ρ (s + v) = conv (fun x => f x - f (x + v)) ρ s := by
  have hfv : MemLp (fun x : ℝ => f (x + v)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) v)
  rw [conv, conv, conv, ← integral_sub (integrable_slice hf hρc hρs s)
    (integrable_slice hf hρc hρs (s + v))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [show s + v - t = s - t + v by ring]
  ring

/-- **Mollification does not increase the shifted energy.** -/
theorem lintegral_shift_conv_le (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) (v : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal ((conv f ρ s - conv f ρ (s + v)) ^ 2))
      ≤ ENNReal.ofReal (∫ s : ℝ, (f s - f (s + v)) ^ 2) := by
  have hfv : MemLp (fun x : ℝ => f (x + v)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) v)
  have hh : MemLp (fun x : ℝ => f x - f (x + v)) 2 (volume : Measure ℝ) := hf.sub hfv
  have hhm : Measurable (fun x : ℝ => f x - f (x + v)) :=
    hfm.sub (hfm.comp (measurable_id.add_const v))
  have hrw : ∀ s : ℝ, (conv f ρ s - conv f ρ (s + v)) ^ 2
      = (∫ t : ℝ, (fun x : ℝ => f x - f (x + v)) (s - t) * ρ t) ^ 2 := by
    intro s
    rw [conv_sub hf hρc hρs s v, conv]
  have key := Cvs.WeilForm.Mollify.MollifyL2Contraction.lintegral_conv_sq_le hh hhm hρc hρs
    hρm hρi hρnn hρ1
  refine (le_of_eq (lintegral_congr fun s => by rw [hrw s])).trans ?_
  exact key

end Cvs.WeilForm.Mollify.MollifyShiftedEnergy
