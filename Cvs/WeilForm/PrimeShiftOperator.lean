import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# The prime shift inside the operator

The truncated form's prime side is the quadratic form of a shift operator, so the shift can be
carried inside the operator whose norm bounds a sector rather than beside it as a slack.
-/

noncomputable section

open MeasureTheory Measure Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimeShiftOperator

variable {L : ℝ}

/-! ### Translation and cutting on the window -/

/-- **Translation of an `L²` class.** -/
def transLp (τ : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (fun s => s - τ) (measurePreserving_sub_right volume τ) φ

/-- Translation acts by shifting the argument. -/
theorem transLp_ae (τ : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    ((transLp τ φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
      =ᵐ[volume] fun s => (φ : ℝ → ℝ) (s - τ) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Translation preserves the norm. -/
theorem norm_transLp (τ : ℝ) (φ : Lp ℝ 2 (volume : Measure ℝ)) : ‖transLp τ φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- Translation is additive. -/
theorem transLp_add (τ : ℝ) (φ ψ : Lp ℝ 2 (volume : Measure ℝ)) :
    transLp τ (φ + ψ) = transLp τ φ + transLp τ ψ := map_add _ _ _

/-- The unshifted class, cut to the window. -/
def cutLp (L : ℝ) (ψ : Lp ℝ 2 (volume : Measure ℝ)) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨((Lp.memLp ψ).indicator measurableSet_Ioc.nullMeasurableSet).toLp _, by
    filter_upwards [((Lp.memLp ψ).indicator (s := Ioc (0:ℝ) L) measurableSet_Ioc.nullMeasurableSet).coeFn_toLp]
      with x hx hxne
    rw [hx]
    exact Set.indicator_of_notMem hxne _⟩

/-- Cutting acts by the indicator. -/
theorem cutLp_ae (L : ℝ) (ψ : Lp ℝ 2 (volume : Measure ℝ)) :
    ⇑((cutLp L ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] Set.indicator (Ioc (0:ℝ) L) (⇑ψ) :=
  ((Lp.memLp ψ).indicator (s := Ioc (0:ℝ) L) measurableSet_Ioc.nullMeasurableSet).coeFn_toLp

/-! ### The shift as a bounded operator on the window -/

/-- Almost everywhere equality survives a translation. -/
theorem ae_eq_sub (τ : ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun s => f (s - τ)) =ᵐ[volume] fun s => g (s - τ) :=
  (measurePreserving_sub_right volume τ).quasiMeasurePreserving.ae_eq_comp h

/-! ### The kernel operator with the shift inside -/

/-! ### The sectors, without a prime slack -/

/-! ### Step (a) at a scale, without prime slacks -/

end Cvs.WeilForm.PrimeShiftOperator
