/-
The explicit bump, and the hypothesis-free theorem (campaign finale).

Mathlib's `ContDiffBump` centered at `ℓ/2` with radii `ℓ/4 < ℓ/3`
is smooth, valued in `[0,1]`, supported in `(ℓ/6, 5ℓ/6) ⊆ (0, ℓ)`,
and nonvanishing on an interval of the position-zero slice — which has
positive measure. Feeding it to
`superalgebraic_sections_atomCLMC_of_bump` yields the unconditional
theorem: for every atom,

  `pathLawNorm q c − ‖P_N T P_N‖ = o(N^{-p})` for every `p`,

where `T = atomCLMC q c` is the unfolded atom on `ℓ²(ℤ)` and `P_N` projects
onto `span {e_k : |k| ≤ N}`. The odd sector is not treated here.
-/
import Cvs.PathLaw.SuperAlgebraicC
import Mathlib.Analysis.Calculus.BumpFunction.Basic

open MeasureTheory Real Submodule
open scoped ContDiff

namespace Cvs.PathLaw

/-- Any function nonvanishing on the middle of the long-base interval
survives on a positive-measure part of the position-zero slice. -/
lemma volume_slice_pos_of_nonvanishing (β : ℝ) (hβ : 0 < β)
    (b : ℝ → ℝ)
    (hne : ∀ y, y ∈ Set.Ioo ((1 - ((capacity 1 β : ℝ) - 1) * β) / 6)
      (5 * (1 - ((capacity 1 β : ℝ) - 1) * β) / 6) → b y ≠ 0)
    (hbm : Measurable b) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ b (chainBase β (rep z)) ≠ 0} := by
  have hℓpos : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  have hℓ1 : (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 := by
    have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
    have h1 : (1 : ℝ) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hm1
    nlinarith
  have hsub : Set.Ioo ((1 - ((capacity 1 β : ℝ) - 1) * β) / 6)
      (5 * (1 - ((capacity 1 β : ℝ) - 1) * β) / 6)
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
            ∧ b (chainBase β (rep z)) ≠ 0})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hy0 : 0 < y := lt_trans (by positivity) hy.1
    have hyℓ : y < 1 - ((capacity 1 β : ℝ) - 1) * β := by
      have := hy.2
      linarith
    have hy1 : y < 1 := lt_of_lt_of_le hyℓ hℓ1
    have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y :=
      rep_coe y hy0.le hy1
    have hwin : y ∈ Set.Ico (((0 : ℕ) : ℝ) * β)
        (((0 : ℕ) : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β)) := by
      constructor
      · simpa using hy0.le
      · simpa using hyℓ
    obtain ⟨hpos, hbase, hlen⟩ := chain_coords_window β hβ hwin
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ {z : AddCircle (1 : ℝ) | _}
      refine ⟨?_, ?_, ?_⟩
      · show chainLength β (chainBase β (rep _)) = capacity 1 β
        rw [hrep]
        exact hlen
      · rw [hrep]
        exact hpos
      · rw [hrep, hbase]
        have : y - ((0 : ℕ) : ℝ) * β = y := by simp
        rw [this]
        exact hne y hy
    · exact Set.mem_Ioc.mpr ⟨hy0, by linarith⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ b (chainBase β (rep z)) ≠ 0} := by
    change MeasurableSet (chainSet β (capacity 1 β) ∩ ((chainPos β ∘ rep) ⁻¹' {0}
      ∩ ((b ∘ chainBase β ∘ rep) ⁻¹' {0}ᶜ)))
    refine (measurableSet_chainSet β _).inter
      ((((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0)).inter ?_)
    exact (hbm.comp ((measurable_chainBase β).comp measurable_rep))
      (measurableSet_singleton 0).compl
  have hproj := AddCircle.add_projection_respects_measure
    (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  refine ENNReal.ofReal_pos.mpr ?_
  linarith

/-- **Unconditional super-algebraic Galerkin truncation convergence for
the canonical atom**: for every prime power `q` and window `c`,

  `pathLawNorm q c − ‖P_N T P_N‖ = o(N^{-p})` for every `p`,

where `T = atomCLMC q c` is the unfolded atom on `ℓ²(ℤ)` and `P_N` projects
onto `span {e_k : |k| ≤ N}`. The odd sector is not treated here.

The witnessing eigenvector is the smooth-bump modulation of the top
chain envelope, transported through the DTFT; the bump is Mathlib's
`ContDiffBump` on the long-base interval. -/
theorem superalgebraic_sections_atomCLMC (q c : ℕ) (hq : 2 ≤ q)
    (hc : q < c) :
    SuperAlgebraicDecay fun N =>
      pathLawNorm q c - ‖compress (sectionSpaceC N) (atomCLMC q c)‖ := by
  obtain ⟨hβ, hβ1⟩ := beta_mem q c hq hc
  have hℓpos : 0 < 1 - ((capacity 1 (Real.log q / Real.log c) : ℝ) - 1)
      * (Real.log q / Real.log c) := by
    have := capacity_sub_one_mul_lt (Real.log q / Real.log c) hβ
    linarith
  set ℓ : ℝ := 1 - ((capacity 1 (Real.log q / Real.log c) : ℝ) - 1)
    * (Real.log q / Real.log c) with hℓdef
  set φ : ContDiffBump (ℓ / 2) :=
    ⟨ℓ / 4, ℓ / 3, by positivity, by linarith⟩ with hφdef
  refine superalgebraic_sections_atomCLMC_of_bump q c hq hc φ φ.contDiff
    ?_ φ.continuous.measurable 1 zero_le_one
    (fun r _ _ => by
      rw [abs_of_nonneg φ.nonneg]
      exact φ.le_one)
    ?_
  · rw [φ.tsupport_eq]
    show Metric.closedBall (ℓ / 2) (ℓ / 3) ⊆ Set.Ioo (0 : ℝ) ℓ
    rw [Real.closedBall_eq_Icc]
    intro y hy
    constructor
    · have := hy.1
      linarith
    · have := hy.2
      linarith
  · refine volume_slice_pos_of_nonvanishing _ hβ _ (fun y hy => ?_)
      φ.continuous.measurable
    have hmem : y ∈ Function.support (φ : ℝ → ℝ) := by
      rw [φ.support_eq, Real.ball_eq_Ioo]
      have hr : φ.rOut = ℓ / 3 := rfl
      constructor
      · rw [hr]
        have h2 := hy.1
        rw [← hℓdef] at h2
        linarith
      · rw [hr]
        have h2 := hy.2
        rw [← hℓdef] at h2
        linarith
    exact hmem

end Cvs.PathLaw
