/-
The rapid-decay tail theorem on the circle (campaign stage 5).

Assembly: on the unit circle, Lebesgue measure *is* the normalized Haar
measure, so Mathlib's `fourierBasis` (whose `repr` is `fourierCoeff`)
applies to the complexified rung function. Combining the coefficient
product formula (stage 3) with the abstract tail bound (stage 4):

  **the bump-modulated top eigenfunction has super-algebraically
  decaying Fourier-window projection tails.**

This is the tail hypothesis of `Cvs.PathLaw.SuperAlgebraic`, machine-checked
on the circle side.
What separates it from the `ℓ²(ℤ)` statement consumed by
`superalgebraic_sections` is only unitary bookkeeping: the DTFT and the
real/complex splitting, both isometries that carry window spans to
window spans.
-/
import Cvs.PathLaw.TailBound

open MeasureTheory Real AddCircle
open scoped ContDiff

namespace Cvs.PathLaw

local notation "𝕋₁" => AddCircle (1 : ℝ)

instance : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

/-- On the unit circle, Lebesgue measure is the normalized Haar
measure. -/
theorem volume_eq_haarAddCircle :
    (volume : Measure 𝕋₁) = (haarAddCircle : Measure 𝕋₁) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- The complexified rung function is square-integrable for Haar. -/
lemma memLp_rungFunC (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) :
    MemLp (fun z : 𝕋₁ => ((rungFun β L j c z : ℝ) : ℂ)) 2
      (haarAddCircle : Measure 𝕋₁) := by
  rw [← volume_eq_haarAddCircle]
  exact (memLp_rungFun β hβ L j c hcm B hB hbd).ofReal

/-- The complexified rung function as an element of the Haar `L²`. -/
noncomputable def rungFunC (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) :
    Lp ℂ 2 (haarAddCircle : Measure 𝕋₁) :=
  MemLp.toLp (fun z : 𝕋₁ => ((rungFun β L j c z : ℝ) : ℂ))
    (memLp_rungFunC β hβ L j c hcm B hB hbd)

/-- The Hilbert-basis coefficients of the packaged rung function are its
Fourier coefficients. -/
lemma fourierBasis_repr_rungFunC (β : ℝ) (hβ : 0 < β) (L : ℕ)
    (j : Fin L) (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) (k : ℤ) :
    (fourierBasis (T := (1 : ℝ))).repr (rungFunC β hβ L j c hcm B hB hbd) k
      = fourierCoeff (fun z : 𝕋₁ => ((rungFun β L j c z : ℝ) : ℂ)) k := by
  rw [fourierBasis_repr]
  exact congrFun (fourierCoeff_congr_ae
    ((memLp_rungFunC β hβ L j c hcm B hB hbd).coeFn_toLp)) k

/-- **The rapid-decay tail theorem on the circle.** For a smooth bump
supported inside the long-base interval, the bump-modulated capacity
rung function has super-algebraically decaying Fourier-window
projection tails. -/
theorem superAlgebraic_fourier_window_tail (β : ℝ) (hβ : 0 < β)
    (j : Fin (capacity 1 β)) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hsupp : tsupport b ⊆ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β))
    (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |b r| ≤ B) :
    SuperAlgebraicDecay fun N =>
      ‖rungFunC β hβ (capacity 1 β) j b hbm B hB hbd
        - (basisWindow (fourierBasis (T := (1 : ℝ))) N).starProjection
            (rungFunC β hβ (capacity 1 β) j b hbm B hB hbd)‖ := by
  apply superAlgebraicDecay_basisWindow_tail
  have hfun : (fun k : ℤ =>
      (fourierBasis (T := (1 : ℝ))).repr
        (rungFunC β hβ (capacity 1 β) j b hbm B hB hbd) k)
      = fourierCoeff (fun z : 𝕋₁ =>
          ((rungFun β (capacity 1 β) j b z : ℝ) : ℂ)) :=
    funext fun k =>
      fourierBasis_repr_rungFunC β hβ (capacity 1 β) j b hbm B hB hbd k
  rw [hfun]
  exact rapidFourierDecay_rungFun β hβ j b hb hsupp

end Cvs.PathLaw
