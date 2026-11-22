import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# On the window the constant mode is damped; on the circle it is not

    selfConvolution (indicator (Ioc 0 L) 1) τ = L − τ   for 0 ≤ τ ≤ L

against `Cvs.Finite.ShiftedModePairingTable`'s `L·cos(0·v) = L` at every displacement.  The window tapers every prime
term by `1 − τ/L`; the circle applies no taper at all.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.ConstantModeWindowDamped

/-- **The window's constant mode tapers linearly.** -/
theorem selfConvolution_indicator_one {L τ : ℝ} (hτ0 : 0 ≤ τ) (hτL : τ ≤ L) :
    selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ))) τ = L - τ := by
  have hfun : (fun s : ℝ => Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ)) s
      * Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ)) (s + τ))
      = Set.indicator (Set.Ioc (0:ℝ) (L - τ)) (fun _ => (1:ℝ)) := by
    funext s
    by_cases h1 : s ∈ Set.Ioc (0:ℝ) (L - τ)
    · obtain ⟨ha, hb⟩ := h1
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ha, by linarith⟩),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ha, hb⟩)]
      norm_num
    · rw [Set.indicator_of_notMem h1]
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at h1
      rcases h1 with h | h
      · rw [Set.indicator_of_notMem (fun (hc : s ∈ Set.Ioc (0:ℝ) L) => absurd hc.1 (not_lt.mpr h))]
        ring
      · refine mul_eq_zero.mpr (Or.inr ?_)
        refine Set.indicator_of_notMem (fun (hc : s + τ ∈ Set.Ioc (0:ℝ) L) => ?_) _
        exact absurd hc.2 (not_le.mpr (by linarith [hc.1]))
  unfold selfConvolution
  rw [hfun, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc_of_le (by linarith)]
  ring

end Cvs.Finite.ConstantModeWindowDamped
