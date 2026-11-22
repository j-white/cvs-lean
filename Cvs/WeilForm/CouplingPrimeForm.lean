import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The form coupling in prime form

For `τ` vanishing on `(−∞, 1]` and `u` tame on `[α, 1]`, `α > 0`, every dilate `⟨τ, u(n·)⟩` vanishes, so
`−weilθ(τ, u) = Σ_n Λ(n)⟨u, τ(n·)⟩ − arch(τ, u) − pole(τ, u)`. With `τ_a` the regularised tail of the spine
profile at `80 ≤ 2πx`: `Q(spineMap x a, w_u) = Σ_n Λ(n) ∫_{θ>0} u(θ)τ_a(nθ) dθ − arch(τ_a, u) − pole(τ_a, u)`,
and the tame form coupling is `(prime − arch − pole)² ≤ (1−δ)Q(r)Q(w)`.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.CouplingPrimeForm

open Cvs.WeilForm.ThetaSpaceParseval (weilθ dil poleP poleM)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.WindowFormTailLimit (Tame regProfile)

/-- **A tail and a window test have no common dilate**: for `τ = 0` on `(−∞, 1]` and `u` tame on `[α, 1]`,
`⟨τ, u(n·)⟩ = 0` for every `n`. -/
theorem dil_eq_zero {τ u : ℝ → ℝ} {α : ℝ} (hτ : ∀ θ ≤ 1, τ θ = 0) (hu : Tame u α 1) (n : ℕ) :
    dil τ u n = 0 := by
  unfold dil
  refine setIntegral_eq_zero_of_forall_eq_zero fun θ hθ => ?_
  rcases le_or_gt θ 1 with h1 | h1
  · rw [hτ θ h1, zero_mul]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hu.supp _ fun h => by have := h.1; simp at this; linarith [hu.pos], mul_zero]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [hu.supp _ fun h => by nlinarith [h.2], mul_zero]

/-- **The Weil pairing of a tail with a window test in channels**: for `τ = 0` on `(−∞, 1]` and `u` tame on
`[α, 1]`, `−weilθ(τ, u) = Σ_n Λ(n)⟨u, τ(n·)⟩ − arch(τ, u) − pole(τ, u)`. -/
theorem neg_weilθ_eq_channels {τ u : ℝ → ℝ} {α : ℝ} (hτ : ∀ θ ≤ 1, τ θ = 0) (hu : Tame u α 1) :
    -weilθ τ u
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u τ n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale τ) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP τ * poleM u + poleM τ * poleP u) := by
  have h : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (dil τ u n + dil u τ n)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * dil u τ n := fun n => by
    rw [dil_eq_zero hτ hu n, zero_add]
  unfold weilθ
  rw [tsum_congr h]
  ring

/-- The regularised tail `τ_a` of the spine profile of `a` at scale `x`. -/
abbrev tail (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ → ℝ :=
  fullTail (Cvs.L2a.AngularProlateTailPositive.psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)))

theorem tail_of_le_one (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) {θ : ℝ} (hθ : θ ≤ 1) : tail x a θ = 0 :=
  Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ

/-- **The coupling of a spine vector with a tame class in prime form**: at `80 ≤ 2πx` and `u` tame on
`[1/x, 1]`, `Q(spineMap x a, w_u) = Σ_n Λ(n) ∫_{θ>0} u(θ)τ_a(nθ) dθ − arch(τ_a, u) − pole(τ_a, u)`. -/
theorem QWbil_spineMap_wv_eq_channels {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) {u : ℝ → ℝ}
    (hu : Tame u (1 / x) 1) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a)
        (Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hu)
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u (tail x a) n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (tail x a)) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP (tail x a) * poleM u + poleM (tail x a) * poleP u) := by
  rw [Cvs.Approximant.SpineCouplingTailPairing.QWbil_spineMap_eq_neg_tail hx a hu]
  exact neg_weilθ_eq_channels (fun θ hθ => tail_of_le_one x a hθ) hu

end Cvs.WeilForm.CouplingPrimeForm
