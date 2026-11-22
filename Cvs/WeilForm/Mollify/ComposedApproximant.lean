import Mathlib
import Cvs.Upstream.L2DilationContinuity
import Cvs.WeilForm.Mollify.MollificationStage
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.WeilFormDilationContinuous

/-!
# The composed approximant, and where it lives

    ξ n = (a n)^{−1/2}·η(·/a n) shifted by `c n`, then mollified at radius `c n`

with `a n · L + 2·c n = L`, so the three moves fit the window exactly.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Upstream.L2DilationContinuity

namespace Cvs.WeilForm.Mollify.ComposedApproximant

/-- The dilation ratio. -/
def dila (n : ℕ) : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 2)

/-- The shift, which is also the mollifier's radius. -/
def shift (L : ℝ) (n : ℕ) : ℝ := L / (2 * ((n : ℝ) + 2))

theorem dila_pos (n : ℕ) : 0 < dila n := by
  rw [dila]; positivity

theorem dila_half_le (n : ℕ) : 1 / 2 ≤ dila n := by
  rw [dila, le_div_iff₀ (by positivity)]
  have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem dila_lt_one (n : ℕ) : dila n < 1 := by
  rw [dila, div_lt_one (by positivity)]
  linarith

theorem tendsto_dila : Filter.Tendsto dila Filter.atTop (nhds 1) := by
  have h : ∀ n : ℕ, dila n = 1 - 1 / ((n : ℝ) + 2) := by
    intro n
    rw [dila]
    field_simp
    ring
  rw [funext h]
  have h2 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hbase
    refine one_div_le_one_div_of_le (by positivity) (by linarith)
  have hc : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have h3 := hc.sub h2
  rw [sub_zero] at h3
  exact h3

theorem shift_pos {L : ℝ} (hL : 0 < L) (n : ℕ) : 0 < shift L n := by
  rw [shift]; positivity

theorem tendsto_shift (L : ℝ) : Filter.Tendsto (shift L) Filter.atTop (nhds 0) := by
  have h : ∀ n : ℕ, shift L n = L * (1 / (2 * ((n : ℝ) + 2))) := by
    intro n; rw [shift]; ring
  rw [funext h]
  have h2 : Filter.Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 2))) Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hbase
    refine one_div_le_one_div_of_le (by positivity) (by linarith)
  have hc : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) := tendsto_const_nhds
  have h3 := hc.mul h2
  rw [mul_zero] at h3
  exact h3

/-- **The three moves fit the window exactly.** -/
theorem fit (L : ℝ) (n : ℕ) : dila n * L + 2 * shift L n = L := by
  rw [dila, shift]
  have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The dilate, translated so its support leaves the origin. -/
def shifted (L : ℝ) (η : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => dilate (dila n) η (x + -(shift L n))

/-- **The composed approximant, before renormalising.** -/
def pre {L : ℝ} (hL : 0 < L) (η : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv (shifted L η n)
    (Cvs.WeilForm.Mollify.MollifierKernel.kernel (shift_pos hL n))

theorem memLp_shifted {η : ℝ → ℝ} (hη : MemLp η 2 (volume : Measure ℝ)) (L : ℝ) (n : ℕ) :
    MemLp (shifted L η n) 2 (volume : Measure ℝ) :=
  (memLp_dilate (dila_pos n) hη).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) (-(shift L n)))

theorem measurable_shifted {η : ℝ → ℝ} (hηm : Measurable η) (L : ℝ) (n : ℕ) :
    Measurable (shifted L η n) := by
  refine ((measurable_const.mul (hηm.comp (measurable_id.div_const (dila n)))).comp
    (measurable_id.add_const (-(shift L n))))

/-- **The dilate-and-translate has left the origin.** -/
theorem support_shifted {L : ℝ} {η : ℝ → ℝ}
    (hηs : ∀ s ∉ Set.Ioc (0:ℝ) L, η s = 0) (n : ℕ) :
    ∀ s ∉ Set.Ioc (shift L n) (dila n * L + shift L n), shifted L η n s = 0 := by
  intro s hs
  have hdil : ∀ t ∉ Set.Ioc (0:ℝ) (dila n * L), dilate (dila n) η t = 0 := by
    intro t ht
    rw [dilate]
    have := Cvs.WeilForm.WeilFormDilationContinuous.support_dilate (dila_pos n) hηs t ht
    rw [this, mul_zero]
  refine hdil _ ?_
  intro hmem
  simp only [Set.mem_Ioc] at hmem
  exact hs (Set.mem_Ioc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)

/-- **The approximant lives in the window.** -/
theorem support_pre {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ}
    (hηs : ∀ s ∉ Set.Ioc (0:ℝ) L, η s = 0) (n : ℕ) :
    ∀ s ∉ Set.Ioc (0:ℝ) L, pre hL η n s = 0 := by
  refine Cvs.WeilForm.Mollify.MollificationStage.support_conv_window (by linarith) ?_
    (support_shifted hηs n) (fun t ht => Cvs.WeilForm.Mollify.MollifierKernel.kernel_eq_zero _ ht)
  have := fit L n
  linarith

end Cvs.WeilForm.Mollify.ComposedApproximant
