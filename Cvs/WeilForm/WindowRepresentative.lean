import Mathlib
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's form, and a representative that vanishes off the window

    φ ∈ window L  ⟹  ∃ f, (∀ x ∉ (0, L], f x = 0)  ∧  φ =ᵐ f

so results stated with an everywhere-support hypothesis apply to a class in `window L`.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowRepresentative

variable {L : ℝ}

/-- The underlying function of a class in the window. -/
def fn (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ → ℝ :=
  ((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)

/-- **The window's Weil form**, on the subspace the simplicity criteria consume. -/
def weilQW (P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  Cvs.WeilForm.WeilFormOnWindowL2.weilQ P R (φ : Lp ℝ 2 (volume : Measure ℝ))

/-- **The subspace norm is the ambient one**, so `g 0` is the square of either. -/
theorem selfConvolution_zero (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    selfConvolution (fn φ) 0 = ‖φ‖ ^ 2 := by
  rw [fn, Cvs.WeilForm.WeilFormOnWindowL2.selfConvolution_zero]
  rfl

/-! ### The representative, named

`exists_rep` produces a representative but not its integrability, which every window result
also demands.  Naming it lets both travel together. -/

/-- **The canonical representative**: the class, cut to the window. -/
def rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (0:ℝ) L) (fn φ)

/-- It vanishes off the window, everywhere. -/
theorem rep_supp (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ∀ x, x ∉ Set.Ioc (0:ℝ) L → rep φ x = 0 :=
  fun x hx => Set.indicator_of_notMem hx _

/-- It represents the class. -/
theorem ae_eq_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : fn φ =ᵐ[volume] rep φ := by
  filter_upwards [φ.2] with x hx
  by_cases h : x ∈ Set.Ioc (0:ℝ) L
  · rw [rep, Set.indicator_of_mem h]
  · rw [rep, Set.indicator_of_notMem h]
    exact hx h

/-- It is square integrable, being a.e. equal to a class of `L²`. -/
theorem memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    MemLp (rep φ) 2 (volume : Measure ℝ) :=
  MemLp.ae_eq (ae_eq_rep φ) (Lp.memLp (φ : Lp ℝ 2 (volume : Measure ℝ)))

/-- Its square is integrable. -/
theorem integrable_sq_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (fun s : ℝ => (rep φ s) ^ 2) (volume : Measure ℝ) :=
  (memLp_rep φ).integrable_sq

/-- Its shifted products are integrable, which is what the self-convolution asks for. -/
theorem integrable_cross_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (u : ℝ) :
    Integrable (fun s : ℝ => rep φ s * rep φ (s + u)) (volume : Measure ℝ) := by
  have h := (memLp_rep φ).integrable_mul
    (Cvs.WeilForm.CentredWindowTranslate.memLp_translate u (memLp_rep φ))
  exact h

/-- The form and the norm, both on the named representative. -/
theorem weilQW_rep (P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    weilQW P R φ = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (rep φ) ∧
      selfConvolution (rep φ) 0 = ‖φ‖ ^ 2 := by
  refine ⟨Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (ae_eq_rep φ), ?_⟩
  rw [← Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae (ae_eq_rep φ) 0, selfConvolution_zero]

end Cvs.WeilForm.WindowRepresentative
