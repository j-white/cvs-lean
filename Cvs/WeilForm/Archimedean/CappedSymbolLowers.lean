import Mathlib

/-!
# Capping the symbol only lowers the form

    `∫ min(archSymbol − archSymbol 0, λ*) · specDensity ≤ ∫ (archSymbol − archSymbol 0) · specDensity`

a pointwise comparison against a nonnegative density.
-/

noncomputable section

open MeasureTheory

namespace Cvs.WeilForm.Archimedean.CappedSymbolLowers

/-- **The capped form, written through the multiplier.**  `min(σ, λ*) = λ*(1 − m)` with
`m = max(0, 1 − σ/λ*)`, which is the form `Cvs.WeilForm.PlaneHyperplaneTraceCap.even_plane_bound` consumes. -/
theorem min_eq_lam_sub {σ lamstar : ℝ} (hlam : 0 < lamstar) :
    min σ lamstar = lamstar * (1 - max 0 (1 - σ / lamstar)) := by
  rcases le_total σ lamstar with h | h
  · have hge : (0:ℝ) ≤ 1 - σ / lamstar := by
      rw [sub_nonneg, div_le_one hlam]; exact h
    rw [min_eq_left h, max_eq_right hge]
    field_simp
    ring
  · have hle : 1 - σ / lamstar ≤ 0 := by
      rw [sub_nonpos, one_le_div hlam]; exact h
    rw [min_eq_right h, max_eq_left hle]
    ring

end Cvs.WeilForm.Archimedean.CappedSymbolLowers
