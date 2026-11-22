import Mathlib.NumberTheory.LSeries.Dirichlet

/-
Growth of `ζ` in a strip — the right edge.

`MATHLIB.md` §7 records this as the wall for rung 6: the test-function form of
Guinand–Weil needs `|ζ(σ+it)| = O(|t|^A)` on a strip, which Mathlib does not
have.  The interpolation route is

  * **right edge** (`σ ≥ 1+δ`): bounded, from the Dirichlet series — *this file*;
  * **left edge** (`σ ≤ −δ`): polynomial, from the functional equation plus
    Stirling for `Γ` on vertical lines — Mathlib's `Γ` asymptotics are
    Bohr–Mollerup, not this, so the ingredient is missing;
  * **interpolate**: Phragmén–Lindelöf, which Mathlib does have
    (`Analysis/Complex/PhragmenLindelof.lean`).

Only the first is here.  The bound is uniform in `Im s`, which is the point — it
is a constant, not a function of the height.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- **`ζ` is bounded on every right half-plane `Re s ≥ σ₀ > 1`.** The Dirichlet-series half of the
growth bound, and the input Phragmén–Lindelöf needs on the right edge. -/
theorem norm_riemannZeta_le_of_re_le {σ₀ : ℝ} (hσ : 1 < σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ‖LSeries.term 1 (σ₀ : ℂ) n‖ := by
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have hsum₀ : LSeriesSummable 1 (σ₀ : ℂ) := by
    refine LSeriesSummable_one_iff.mpr ?_
    simpa using hσ
  have hre : (σ₀ : ℂ).re ≤ s.re := by simpa using hs
  -- termwise comparison against the real point
  have hle : ∀ n : ℕ, ‖LSeries.term 1 s n‖ ≤ ‖LSeries.term 1 (σ₀ : ℂ) n‖ :=
    fun n => LSeries.norm_term_le_of_re_le_re 1 hre n
  have hsummable : Summable fun n : ℕ => ‖LSeries.term 1 s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum₀.norm
  rw [← LSeries_one_eq_riemannZeta hs1, LSeries]
  refine (norm_tsum_le_tsum_norm hsummable).trans ?_
  exact hsummable.tsum_le_tsum hle hsum₀.norm

end Cvs.Zeta
