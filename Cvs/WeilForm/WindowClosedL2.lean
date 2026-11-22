import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# The window is closed in `L²`

    `φₙ ∈ window L`, `φₙ → y` in `L²`   ⟹   `y ∈ window L`

along an almost-everywhere convergent subsequence, vanishing off the window passes to the limit.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Cvs.WeilForm.WindowClosedL2

/-- **A limit of window classes is a window class.** -/
theorem mem_window_of_tendsto {L : ℝ} {f : ℕ → Lp ℝ 2 (volume : Measure ℝ)}
    {y : Lp ℝ 2 (volume : Measure ℝ)} (hf : ∀ n, f n ∈ Cvs.WeilForm.WeilFormOnWindowL2.window L)
    (hy : Tendsto f atTop (𝓝 y)) : y ∈ Cvs.WeilForm.WeilFormOnWindowL2.window L := by
  have hm := tendstoInMeasure_of_tendsto_Lp hy
  obtain ⟨ns, _, hae⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ i, x ∉ Set.Ioc (0:ℝ) L → (f (ns i) : ℝ → ℝ) x = 0 :=
    ae_all_iff.mpr fun i => (hf (ns i) : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Set.Ioc (0:ℝ) L → (f (ns i) : ℝ → ℝ) x = 0)
  change ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (0:ℝ) L → (y : ℝ → ℝ) x = 0
  filter_upwards [hae, hall] with x hx hz hxL
  have h0 : Tendsto (fun i => (f (ns i) : ℝ → ℝ) x) atTop (𝓝 0) := by
    simp only [hz _ hxL]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hx h0

/-- **In the window's own topology.** -/
theorem tendsto_window {L : ℝ} {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Lp ℝ 2 (volume : Measure ℝ)}
    (hy : Tendsto (fun n => ((x n : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 y)) :
    ∃ hyw : y ∈ Cvs.WeilForm.WeilFormOnWindowL2.window L, Tendsto x atTop (𝓝 ⟨y, hyw⟩) :=
  ⟨mem_window_of_tendsto (fun n => (x n).2) hy, tendsto_subtype_rng.mpr hy⟩

end Cvs.WeilForm.WindowClosedL2
