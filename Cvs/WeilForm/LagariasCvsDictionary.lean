import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.CoreSchurForm
import Cvs.Route.DilationLatticeCriterion
import Cvs.Route.NestedBoxDilationAmplify
import Cvs.Route.NestedBoxFrequenciesReal
import Cvs.Route.NestedBoxInduction
import Cvs.Route.OneCellChebyshevInequality
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellExplicitFormula
import Cvs.Route.OneCellLaplaceTransform
import Cvs.Route.WindowPositivityAsCore
import Cvs.Upstream.LandauLaplaceNonneg
import Cvs.WeilForm.ApproxWindowPositivityRH
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MatrixPSDCriterion
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.Zeta.Hadamard
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiLogDerivRhCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One positivity, many coordinates: the map from Lagarias to the CvS matrix

`dictionary`: with no hypothesis, `ξ'/ξ` is the Cauchy transform of the zeros, it is `(s²/2)` times the Laplace
transform of the one-cell function `G`, `G` is the zeros tested against the Fejér kernel `4 sin²(zL/2)/z²`, and `G(L)`
is `L` times the constant-mode corner of the CvS matrix. `rh_tfae`: each object's positivity is RH.
-/

noncomputable section

open Real Filter Cvs.Zeta

namespace Cvs.WeilForm.LagariasCvsDictionary
open Cvs.ZeroCounting

/-- **The dictionary**, unconditionally: Hadamard (`ξ'/ξ` over the zeros), Laplace (`ξ'/ξ` from `G`), the
explicit formula (`G` over the zeros), and the CvS corner (`G` from the window matrix). -/
theorem dictionary :
    (∀ z : ℂ, riemannXi z ≠ 0 → logDeriv riemannXi z
      = ∑' n : zeroIndex riemannXi,
          (1 / (z - zeroSeq riemannXi n) - 1 / (1 / 2 - zeroSeq riemannXi n)))
    ∧ (∀ s : ℝ, 1 / 2 < s →
      Cvs.Upstream.LandauLaplaceNonneg.lap Cvs.Route.OneCellLaplaceTransform.G s = 2 / (s : ℂ) ^ 2 * logDeriv riemannXi (1 / 2 + s))
    ∧ Cvs.Route.NestedBoxFrequenciesReal.ZeroSideG
    ∧ (∀ L : ℝ, 0 < L → ∀ N : ℕ,
      L * Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (Cvs.Finite.SymmetricModeSet.mode N) none none = Cvs.Route.OneCellLaplaceTransform.G L) :=
  ⟨fun _ hz => Cvs.Zeta.XiLogDerivRhCriterion.logDeriv_eq_tsum hz, fun _ hs => Cvs.Route.OneCellCriterion.lap_G_real hs,
    Cvs.Route.OneCellExplicitFormula.zeroSideG, fun L hL N => Cvs.WeilForm.MatrixPSDCriterion.corner_eq hL (Cvs.WeilForm.MatrixPSDCriterion.complete L).1 (Cvs.WeilForm.MatrixPSDCriterion.complete L).2
      (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) rfl⟩

/-- **The map**: RH, Lagarias's positivity of `ξ'/ξ`, real frequencies, `G ≥ 0`, the Chebyshev form, window
positivity (exact, approximate, CORE, the pole problem), the lattice, the box induction, amplification, and the
CvS matrix and its corner are equivalent. -/
theorem rh_tfae : List.TFAE
    [ RiemannHypothesis,
      ∀ z : ℂ, 1 / 2 < z.re → riemannXi z ≠ 0 → 0 ≤ (logDeriv riemannXi z).re,
      Cvs.Route.NestedBoxFrequenciesReal.FrequenciesReal,
      ∀ L : ℝ, 0 < L → 0 ≤ Cvs.Route.OneCellLaplaceTransform.G L,
      ∀ x : ℝ, 1 < x → Cvs.Route.OneCellChebyshevInequality.Psihalf x ≤ Cvs.Route.OneCellChebyshevInequality.M x,
      ∀ x : ℕ, 2 ≤ x → ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q _ x (Nat.clog 2 x) φ,
      ∀ ε > 0, ∀ x₀ : ℕ, ∃ x : ℕ, x₀ ≤ x ∧ ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        -ε * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ,
      ∀ x : ℕ, 2 ≤ x → Cvs.Route.CoreSchurForm.Core x,
      Cvs.WeilForm.PoleArchPrimeProblem.Problem,
      ∀ N : ℕ, ∀ hN : 2 ≤ N, (Cvs.Route.DilationLatticeCriterion.latticeGram N hN).PosSemidef,
      ∀ N, 1 ≤ N → Cvs.Route.NestedBoxInduction.Step N,
      ∃ r : ℕ → ℝ, Tendsto (fun N : ℕ => r N / N) atTop (nhds 0) ∧
        ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ, -(r N) * ∑ n ∈ Finset.Icc 2 N, c n ^ 2 ≤ Cvs.Route.NestedBoxInduction.qf N c,
      ∀ L : ℝ, 0 < L → ∀ N : ℕ,
        (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (Cvs.Finite.SymmetricModeSet.mode N)).PosSemidef,
      ∀ L : ℝ, 0 < L →
        0 ≤ Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (Cvs.Finite.SymmetricModeSet.mode 0) none none ] := by
  tfae_have 1 ↔ 2 := Cvs.Zeta.XiLogDerivRhCriterion.riemannHypothesis_iff_re_logDeriv_nonneg
  tfae_have 1 ↔ 3 := Cvs.Route.OneCellExplicitFormula.rh_iff_frequenciesReal
  tfae_have 1 ↔ 4 := Cvs.Route.OneCellCriterion.riemannHypothesis_iff_G_nonneg
  tfae_have 1 ↔ 5 := Cvs.Route.OneCellChebyshevInequality.cheb_iff_rh.symm
  tfae_have 1 ↔ 6 := Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos 2 le_rfl
  tfae_have 1 ↔ 7 := Cvs.WeilForm.ApproxWindowPositivityRH.rh_iff_approx_windowPos
  tfae_have 1 ↔ 8 := Cvs.Route.WindowPositivityAsCore.rh_iff_core 2 le_rfl
  tfae_have 1 ↔ 9 := Cvs.WeilForm.PoleArchPrimeProblem.problem_iff_rh.symm
  tfae_have 1 ↔ 10 := Cvs.Route.DilationLatticeCriterion.rh_iff_latticeGram_posSemidef
  tfae_have 1 ↔ 11 := Cvs.Route.NestedBoxInduction.rh_iff_forall_step
  tfae_have 1 ↔ 12 := Cvs.Route.NestedBoxDilationAmplify.rh_iff_frequently_sublinear
  tfae_have 1 ↔ 13 := Cvs.WeilForm.MatrixPSDCriterion.rh_iff_posSemidef
  tfae_have 1 ↔ 14 := Cvs.WeilForm.MatrixPSDCriterion.rh_iff_corner_nonneg
  tfae_finish

end Cvs.WeilForm.LagariasCvsDictionary
