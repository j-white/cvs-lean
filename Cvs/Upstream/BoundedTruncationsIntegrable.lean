import Mathlib

/-!
# Bounded truncations of a nonnegative integrand give integrability

    F ≥ 0,  ∫_{u > δ} F ≤ C for every δ > 0   ⟹   F is integrable on (0, ∞)

The half-lines exhaust `(0, ∞)` upward, so the integral over `(0, ∞)` is the supremum of the
truncated ones, and a bounded supremum is finite.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set

namespace Cvs.Upstream.BoundedTruncationsIntegrable

/-- The half-lines exhaust the positive axis. -/
theorem iUnion_Ioi_eq : (⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 1))) = Set.Ioi (0:ℝ) := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hu
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hu
    exact ⟨n, hn⟩

/-- **Bounded truncations give integrability.** -/
theorem integrableOn_of_bounded_truncations {F : ℝ → ℝ} {C : ℝ}
    (hmeas : AEStronglyMeasurable F ((volume : Measure ℝ).restrict (Set.Ioi 0)))
    (hnn : ∀ u ∈ Set.Ioi (0:ℝ), 0 ≤ F u)
    (hint : ∀ δ : ℝ, 0 < δ → IntegrableOn F (Set.Ioi δ) (volume : Measure ℝ))
    (hbd : ∀ δ : ℝ, 0 < δ → (∫ u in Set.Ioi δ, F u) ≤ C) :
    IntegrableOn F (Set.Ioi 0) (volume : Measure ℝ) := by
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  -- the enorm agrees with `ofReal` on the half-line
  have heq : ∫⁻ x, ‖F x‖ₑ ∂((volume : Measure ℝ).restrict (Set.Ioi 0))
      = ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (F x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Real.enorm_eq_ofReal (hnn x hx)]
  rw [heq, ← iUnion_Ioi_eq]
  -- the half-lines form a chain
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Ioi (1 / ((n : ℝ) + 1))) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩ <;> intro u hu <;> simp only [Set.mem_Ioi] at hu ⊢ <;>
      refine lt_of_le_of_lt ?_ hu <;>
      · apply one_div_le_one_div_of_le
        · positivity
        · have : (min i j : ℝ) ≤ (max i j : ℝ) := by
            exact_mod_cast Nat.cast_le.mpr (min_le_max)
          push_cast
          first
            | (have h := le_max_left i j; exact_mod_cast Nat.succ_le_succ h)
            | (have h := le_max_right i j; exact_mod_cast Nat.succ_le_succ h)
  rw [setLIntegral_iUnion_of_directed _ hdir]
  refine lt_of_le_of_lt (iSup_le fun n => ?_) (by simp : ENNReal.ofReal C < ⊤)
  have hδ : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hI := hint _ hδ
  have hnn' : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi (1 / ((n : ℝ) + 1)))] F := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact hnn u (Set.mem_Ioi.mpr (lt_trans hδ hu))
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn']
  exact ENNReal.ofReal_le_ofReal (hbd _ hδ)

end Cvs.Upstream.BoundedTruncationsIntegrable
