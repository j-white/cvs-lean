import Mathlib
import Cvs.Upstream.ComplexificationIsometryL2
import Cvs.Upstream.FrequencyTruncationL2
import Cvs.Upstream.TotallyBoundedOfApprox
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SpectralTailMassByForm
import Cvs.WeilForm.SublevelTruncationsTotallyBounded
import Cvs.WeilForm.TruncationDistanceByForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative

/-!
# The sublevel set of the form is totally bounded

    `{φ ∈ formDomain | ‖φ‖ ≤ 1, weilQW φ ≤ c}` is totally bounded

by the approximation criterion: its truncations are totally bounded and the truncation error is
uniformly small.  Every sequence in it has a subsequence converging in `L²`.
-/

noncomputable section

open MeasureTheory FourierTransform Real Filter Topology

namespace Cvs.WeilForm.SublevelSetTotallyBounded

/-- The sublevel set of the form, at norm at most one. -/
def sublevel {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ) : Set (Cvs.WeilForm.FormDomain.formDomain hL) :=
  {φ | ‖φ‖ ≤ 1 ∧ Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ≤ c}

/-- The form domain, complexified. -/
abbrev Φ {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  Cvs.Upstream.ComplexificationIsometryL2.emb ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))

/-- **The complexified sublevel set is totally bounded.** -/
theorem totallyBounded_image {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ) :
    TotallyBounded (Φ hL '' sublevel hL P R c) := by
  refine Cvs.Upstream.TotallyBoundedOfApprox.totallyBounded_of_approx fun ε hε => ?_
  obtain ⟨T, hT2, hTM⟩ := Cvs.WeilForm.SpectralTailMassByForm.exists_tailConst_ge
    (max 1 ((c + |Cvs.WeilForm.WindowFormNormFloor.floorConst L P R|) / ε ^ 2))
  have hpos : 0 < Cvs.WeilForm.SpectralTailMassByForm.tailConst T :=
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans hTM)
  have hTnn : 0 ≤ T / (2 * π) := div_nonneg (by linarith) (by positivity)
  refine ⟨(fun φ : Cvs.WeilForm.FormDomain.formDomain hL =>
      Cvs.Upstream.FrequencyTruncationL2.cut (T / (2 * π)) (Φ hL φ)) '' sublevel hL P R c,
    Cvs.WeilForm.SublevelTruncationsTotallyBounded.totallyBounded_cut hL P R c hTnn, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  refine ⟨_, ⟨φ, hφ, rfl⟩, ?_⟩
  have hsq := Cvs.WeilForm.TruncationDistanceByForm.norm_sub_cut_sq_le_of_le hL P R φ hφ.1 hφ.2 hT2 hpos
  have hbound : (c + |Cvs.WeilForm.WindowFormNormFloor.floorConst L P R|) / Cvs.WeilForm.SpectralTailMassByForm.tailConst T
      ≤ ε ^ 2 := by
    rw [div_le_iff₀ hpos]
    have hM := (le_max_right _ _).trans hTM
    have hε2 : 0 < ε ^ 2 := by positivity
    calc c + |Cvs.WeilForm.WindowFormNormFloor.floorConst L P R|
        = ε ^ 2 * ((c + |Cvs.WeilForm.WindowFormNormFloor.floorConst L P R|) / ε ^ 2) := by
          field_simp
      _ ≤ ε ^ 2 * Cvs.WeilForm.SpectralTailMassByForm.tailConst T := mul_le_mul_of_nonneg_left hM hε2.le
  have h := hsq.trans hbound
  calc ‖Φ hL φ - Cvs.Upstream.FrequencyTruncationL2.cut (T / (2 * π)) (Φ hL φ)‖
      = Real.sqrt (‖Φ hL φ - Cvs.Upstream.FrequencyTruncationL2.cut (T / (2 * π)) (Φ hL φ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h
    _ = ε := Real.sqrt_sq hε.le

/-- **Every sequence in the sublevel set converges in `L²` along a subsequence.** -/
theorem exists_subseq_tendsto {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ)
    (x : ℕ → Cvs.WeilForm.FormDomain.formDomain hL) (hx : ∀ n, x n ∈ sublevel hL P R c) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ y : Lp ℝ 2 (volume : Measure ℝ),
      Tendsto (fun k => (((x (σ k)) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
        atTop (𝓝 y) := by
  have hcpt : IsCompact (closure (Φ hL '' sublevel hL P R c)) :=
    isCompact_iff_totallyBounded_isComplete.mpr
      ⟨(totallyBounded_image hL P R c).closure, isClosed_closure.isComplete⟩
  obtain ⟨a, _, σ, hσ, hlim⟩ := hcpt.tendsto_subseq (x := fun n => Φ hL (x n))
    (fun n => subset_closure ⟨x n, hx n, rfl⟩)
  refine ⟨σ, hσ, ?_⟩
  have hc : CauchySeq (fun k => Φ hL (x (σ k))) := hlim.cauchySeq
  have hc' : CauchySeq (fun k =>
      (((x (σ k)) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) := by
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hN m hm n hn
    rwa [Cvs.Upstream.ComplexificationIsometryL2.isometry_emb.dist_eq] at this
  exact cauchySeq_tendsto_of_complete hc'

end Cvs.WeilForm.SublevelSetTotallyBounded
