import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.PoleChannelL2Continuous

/-!
# The pole channel is L²-continuous on the window

    |pole f − pole h| ≤ 2·‖f−h‖₂·‖w₊‖₂·‖w₋‖₂·(‖f‖₂+‖h‖₂)

The pole term is a product of two linear functionals, so its increment splits as
`A(f)(B(f)−B(h)) + B(h)(A(f)−A(h))`; each weight is in `L²` only after truncation.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.PoleChannelWindowL2

/-- The rising pole weight, truncated to the window. -/
def poleWeightPos (L : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (0:ℝ) L) (fun s => Real.exp (s / 2))

/-- The falling pole weight, truncated to the window. -/
def poleWeightNeg (L : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (0:ℝ) L) (fun s => Real.exp (-(s / 2)))

theorem memLp_poleWeightPos (L : ℝ) : MemLp (poleWeightPos L) 2 (volume : Measure ℝ) :=
  Cvs.WeilForm.PoleChannelL2Continuous.memLp_indicator_of_continuous
    (Real.continuous_exp.comp (continuous_id.div_const 2))

theorem memLp_poleWeightNeg (L : ℝ) : MemLp (poleWeightNeg L) 2 (volume : Measure ℝ) :=
  Cvs.WeilForm.PoleChannelL2Continuous.memLp_indicator_of_continuous
    (Real.continuous_exp.comp (continuous_id.div_const 2).neg)

/-- **A function supported in the window does not see the weight outside it.** -/
theorem integral_eq_window {L : ℝ} {f : ℝ → ℝ}
    (hfs : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) (w : ℝ → ℝ) :
    (∫ s : ℝ, f s * w s) = ∫ s : ℝ, f s * Set.indicator (Set.Ioc (0:ℝ) L) w s := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  by_cases hs : s ∈ Set.Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hs]
  · rw [hfs s hs]; ring

/-- **The pole channel is `L²`-continuous on the window.** -/
theorem abs_poleTerm_sub_le {L : ℝ} {f h : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ))
    (hfs : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) (hhs : ∀ s ∉ Set.Ioc (0:ℝ) L, h s = 0) :
    |2 * (∫ s : ℝ, f s * Real.exp (s / 2)) * (∫ s : ℝ, f s * Real.exp (-(s / 2)))
        - 2 * (∫ s : ℝ, h s * Real.exp (s / 2)) * (∫ s : ℝ, h s * Real.exp (-(s / 2)))|
      ≤ 2 * Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
          * Real.sqrt (∫ x : ℝ, poleWeightPos L x ^ 2)
          * Real.sqrt (∫ x : ℝ, poleWeightNeg L x ^ 2)
          * (Real.sqrt (∫ x : ℝ, f x ^ 2) + Real.sqrt (∫ x : ℝ, h x ^ 2)) := by
  have hwp := memLp_poleWeightPos L
  have hwn := memLp_poleWeightNeg L
  -- rewrite each integral against the truncated weight
  have hfp : (∫ s : ℝ, f s * Real.exp (s / 2)) = ∫ s : ℝ, f s * poleWeightPos L s :=
    integral_eq_window hfs _
  have hfn : (∫ s : ℝ, f s * Real.exp (-(s / 2))) = ∫ s : ℝ, f s * poleWeightNeg L s :=
    integral_eq_window hfs _
  have hhp : (∫ s : ℝ, h s * Real.exp (s / 2)) = ∫ s : ℝ, h s * poleWeightPos L s :=
    integral_eq_window hhs _
  have hhn : (∫ s : ℝ, h s * Real.exp (-(s / 2))) = ∫ s : ℝ, h s * poleWeightNeg L s :=
    integral_eq_window hhs _
  rw [hfp, hfn, hhp, hhn]
  set Wp : ℝ := Real.sqrt (∫ x : ℝ, poleWeightPos L x ^ 2) with hWp
  set Wn : ℝ := Real.sqrt (∫ x : ℝ, poleWeightNeg L x ^ 2) with hWn
  set Ef : ℝ := Real.sqrt (∫ x : ℝ, f x ^ 2) with hEf
  set Eh : ℝ := Real.sqrt (∫ x : ℝ, h x ^ 2) with hEh
  set d : ℝ := Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2) with hd
  set Af : ℝ := ∫ s : ℝ, f s * poleWeightPos L s with hAf
  set Bf : ℝ := ∫ s : ℝ, f s * poleWeightNeg L s with hBf
  set Ah : ℝ := ∫ s : ℝ, h s * poleWeightPos L s with hAh
  set Bh : ℝ := ∫ s : ℝ, h s * poleWeightNeg L s with hBh
  have hAfb : |Af| ≤ Ef * Wp := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hf hwp
  have hBhb : |Bh| ≤ Eh * Wn := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hh hwn
  have hAd : |Af - Ah| ≤ d * Wp := Cvs.WeilForm.PoleChannelL2Continuous.abs_integral_mul_sub_le hf hh hwp
  have hBd : |Bf - Bh| ≤ d * Wn := Cvs.WeilForm.PoleChannelL2Continuous.abs_integral_mul_sub_le hf hh hwn
  have hnn : 0 ≤ Wp ∧ 0 ≤ Wn ∧ 0 ≤ Ef ∧ 0 ≤ Eh ∧ 0 ≤ d :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _,
      Real.sqrt_nonneg _⟩
  have hsplit : 2 * Af * Bf - 2 * Ah * Bh = 2 * (Af * (Bf - Bh) + Bh * (Af - Ah)) := by ring
  rw [hsplit]
  have hstep : |Af * (Bf - Bh) + Bh * (Af - Ah)| ≤ (Ef * Wp) * (d * Wn) + (Eh * Wn) * (d * Wp) := by
    calc |Af * (Bf - Bh) + Bh * (Af - Ah)|
        ≤ |Af * (Bf - Bh)| + |Bh * (Af - Ah)| := abs_add_le _ _
      _ = |Af| * |Bf - Bh| + |Bh| * |Af - Ah| := by rw [abs_mul, abs_mul]
      _ ≤ (Ef * Wp) * (d * Wn) + (Eh * Wn) * (d * Wp) := by
          refine add_le_add (mul_le_mul hAfb hBd (abs_nonneg _) ?_)
            (mul_le_mul hBhb hAd (abs_nonneg _) ?_)
          · exact mul_nonneg hnn.2.2.1 hnn.1
          · exact mul_nonneg hnn.2.2.2.1 hnn.2.1
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [hstep, hnn.1, hnn.2.1, hnn.2.2.1, hnn.2.2.2.1, hnn.2.2.2.2]

end Cvs.WeilForm.PoleChannelWindowL2
