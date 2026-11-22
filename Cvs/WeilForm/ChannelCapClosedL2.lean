import Mathlib
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.ChannelFunctionalLipschitz
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-!
# The channel cap is closed under `L²` limits

    `φ_k → φ`, `chanInt b (rep φ_k) ≤ lam·‖φ_k‖²`   ⟹   `chanInt b (rep φ) ≤ lam·‖φ‖²`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Cvs.WeilForm.ChannelCapClosedL2

/-- **`chanInt b (rep ·)` is continuous along `L²` convergence.** -/
theorem tendsto_chanInt {L : ℝ} {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L} {b : ℝ} (hb : 0 < b)
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) :
    Tendsto (fun k => Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (x k))) atTop
      (𝓝 (Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep y))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : Tendsto (fun k => ‖((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
      Lp ℝ 2 (volume : Measure ℝ)) - (y : Lp ℝ 2 (volume : Measure ℝ))‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hbdd : Tendsto (fun k => (2 / b) * ‖((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
      Lp ℝ 2 (volume : Measure ℝ)) - (y : Lp ℝ 2 (volume : Measure ℝ))‖
      * (‖x k‖ + ‖y‖)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (2 / b) * ‖((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
        Lp ℝ 2 (volume : Measure ℝ)) - (y : Lp ℝ 2 (volume : Measure ℝ))‖) atTop (𝓝 0) := by
      simpa using hnorm.const_mul (2 / b)
    have h2 : Tendsto (fun k => ‖x k‖ + ‖y‖) atTop (𝓝 (‖y‖ + ‖y‖)) := hx.norm.add tendsto_const_nhds
    simpa using h1.mul h2
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hbdd
  rw [Real.norm_eq_abs]
  exact Cvs.WeilForm.ChannelFunctionalLipschitz.abs_chanInt_sub_le (x k) y hb

/-- **The channel cap is closed under limits.** -/
theorem cap_closed {L : ℝ} {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L} {b lam : ℝ} (hb : 0 < b)
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ))))
    (hcap : ∀ k, Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (x k))
      ≤ lam * ‖x k‖ ^ 2) :
    Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep y) ≤ lam * ‖y‖ ^ 2 := by
  have hL := tendsto_chanInt hb hx
  have hR : Tendsto (fun k => lam * ‖x k‖ ^ 2) atTop (𝓝 (lam * ‖y‖ ^ 2)) :=
    (hx.norm.pow 2).const_mul lam
  exact le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall hcap)

end Cvs.WeilForm.ChannelCapClosedL2
