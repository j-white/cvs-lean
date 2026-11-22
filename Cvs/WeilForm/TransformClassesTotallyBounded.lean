import Mathlib
import Cvs.Upstream.ToLpNormSqIntegral
import Cvs.WeilForm.TransformFamilyL2Net

/-!
# The family of classes is totally bounded, hence has compact closure

Uniform tightness upgrades `Cvs.WeilForm.TransformFamilyL2Net`'s net for one `ε` to a net for every `ε`, and `Cvs.Upstream.ToLpNormSqIntegral`
carries it into `Lp ℂ 2`, where the space is complete and total boundedness is
precompactness.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Metric

namespace Cvs.WeilForm.TransformClassesTotallyBounded

/-- **The classes are totally bounded.** -/
theorem totallyBounded_toLp {ι : Type*} {F : ι → ℝ → ℂ} {M : ℝ}
    (hcont : ∀ i, Continuous (F i)) (hbd : ∀ (i : ι) (x : ℝ), ‖F i x‖ ≤ M)
    (heq : Equicontinuous F)
    (hsq : ∀ i, Integrable fun t => ‖F i t‖ ^ 2)
    (hdiff : ∀ i j, Integrable fun t => ‖F i t - F j t‖ ^ 2)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
      ∀ i, (∫ t in (Icc (-T) T)ᶜ, ‖F i t‖ ^ 2) ≤ ε)
    (hmem : ∀ i, MemLp (F i) 2 (volume : Measure ℝ)) :
    TotallyBounded (Set.range fun i => (hmem i).toLp (F i)) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro d hd
  -- `5 * ε` must land strictly below `d ^ 2`
  set ε : ℝ := d ^ 2 / 6 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨T, hT, htail⟩ := htight ε hε
  obtain ⟨S, hSfin, hSnet⟩ :=
    Cvs.WeilForm.TransformFamilyL2Net.exists_L2_net hcont hbd heq hT hε hsq hdiff htail
  refine ⟨(fun i => (hmem i).toLp (F i)) '' S, hSfin.image _, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hjS, hij⟩ := hSnet i
  have hdist : dist ((hmem i).toLp (F i)) ((hmem j).toLp (F j)) ≤ Real.sqrt (5 * ε) :=
    Cvs.Upstream.ToLpNormSqIntegral.dist_toLp_le (hmem i) (hmem j) hij
  have hlt : Real.sqrt (5 * ε) < d := by
    have hbound : 5 * ε < d ^ 2 := by rw [hεdef]; nlinarith [hd]
    have := Real.sqrt_lt_sqrt (by positivity) hbound
    rwa [Real.sqrt_sq hd.le] at this
  refine Set.mem_iUnion₂.mpr ⟨(hmem j).toLp (F j), ⟨j, hjS, rfl⟩, ?_⟩
  exact Metric.mem_ball.mpr (lt_of_le_of_lt hdist hlt)

end Cvs.WeilForm.TransformClassesTotallyBounded
