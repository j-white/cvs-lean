import Mathlib
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# The mollification's support, and how much energy it keeps

    supp f ⊆ (a,b],  supp ρ ⊆ [−δ,δ]   ⟹   supp (f⋆ρ) ⊆ (a−δ, b+δ]
    ∫ (f−f⋆ρ)² ≤ ε,  ∫ f² = 1          ⟹   1 − √ε ≤ √(∫ (f⋆ρ)²)

the two facts a mollification has to supply before it can be renormalised inside a window.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real

namespace Cvs.WeilForm.Mollify.MollifySupport

variable {f ρ : ℝ → ℝ}

/-- **The mollification spreads the support by the kernel's radius.** -/
theorem conv_eq_zero_of_support {a b δ : ℝ}
    (hfs : ∀ s ∉ Set.Ioc a b, f s = 0) (hρs : ∀ t : ℝ, δ < |t| → ρ t = 0)
    {s : ℝ} (hs : s ∉ Set.Ioc (a - δ) (b + δ)) :
    Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s = 0 := by
  rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv]
  have hzero : ∀ t : ℝ, f (s - t) * ρ t = 0 := by
    intro t
    by_cases hδt : δ < |t|
    · rw [hρs t hδt, mul_zero]
    · push_neg at hδt
      have habs := abs_le.mp hδt
      have hout : s - t ∉ Set.Ioc a b := by
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs ⊢
        rcases hs with hl | hr
        · exact Or.inl (by linarith [habs.1, habs.2])
        · exact Or.inr (by linarith [habs.1, habs.2])
      rw [hfs _ hout, zero_mul]
  simp only [hzero]
  exact integral_zero ℝ ℝ

end Cvs.WeilForm.Mollify.MollifySupport
