import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The problem: the pole term against the archimedean and prime terms on every window class

The window Weil form is `pole + arch − prime`, `pole f = 2·M₊(f)·M₋(f)` of rank two (`weilForm_split`). `Problem`:
on every window `(0, log x)` and every class of the form domain, `prime − arch ≤ pole`; `problem_iff_rh` (Cvs.WeilForm.WindowWeilCriterion),
`rh_of_approx_problem` with a loss `ε‖φ‖²` (Cvs.WeilForm.ApproxWindowPositivityRH); `flat_instance`: at the box it is `0 ≤ G L`.
-/

noncomputable section

open MeasureTheory Real Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PoleArchPrimeProblem
open Cvs.ZeroCounting

open Cvs.WeilForm.SelfConvolutionFunctional (weilForm)

/-! ### The three pieces -/

/-- The exponential moment `M₊(f) = ∫ f(s) e^{s/2} ds`. -/
def Mplus (f : ℝ → ℝ) : ℝ := ∫ s : ℝ, f s * Real.exp (s / 2)

/-- The exponential moment `M₋(f) = ∫ f(s) e^{−s/2} ds`. -/
def Mminus (f : ℝ → ℝ) : ℝ := ∫ s : ℝ, f s * Real.exp (-(s / 2))

/-- **The pole term**, of rank two: `2·M₊(f)·M₋(f)`. -/
def poleTerm (f : ℝ → ℝ) : ℝ := 2 * Mplus f * Mminus f

/-- **The archimedean term**: the constant `A₀ = Re ψ(¼) − log π` on the energy plus the Lévy deficit. -/
def archTerm (f : ℝ → ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
    + ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2))

/-- **The prime term**: the autocorrelation sampled at `±log n` with weights `Λ(n) n^{−1/2}`, truncated. -/
def primeTerm (P R : ℕ) (f : ℝ → ℝ) : ℝ := primePowerSideTruncated P R (selfConvolution f)

/-- **The split.** -/
theorem weilForm_split (P R : ℕ) (f : ℝ → ℝ) :
    weilForm P R f = poleTerm f + archTerm f - primeTerm P R f := rfl

/-- The form on a class is the split form of its representative. -/
theorem Q_eq_split (x : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ
      = poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - primeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) := by
  show Cvs.WeilForm.WindowRepresentative.weilQW x (Nat.clog 2 x) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) = _
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep x (Nat.clog 2 x) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))).1, weilForm_split]

/-! ### The problem -/

/-- **The problem.** On every window `(0, log x)`, `x ≥ 2`, and every class `φ` of the form domain, the prime
term less the archimedean term of the representative is at most the pole term, with the truncation
`(P, R) = (x, ⌈log₂ x⌉)` of Cvs.WeilForm.WindowWeilCriterion. -/
def Problem : Prop :=
  ∀ x : ℕ, 2 ≤ x → ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
    primeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      - archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      ≤ poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))

/-- **The problem is RH.** -/
theorem problem_iff_rh : Problem ↔ RiemannHypothesis := by
  rw [Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos 2 le_rfl]
  constructor
  · intro h x hx φ
    rw [Q_eq_split]
    linarith [h x hx φ]
  · intro h x hx φ
    have := h x hx φ
    rw [Q_eq_split] at this
    linarith

/-! ### The first instance: the box -/

end Cvs.WeilForm.PoleArchPrimeProblem
