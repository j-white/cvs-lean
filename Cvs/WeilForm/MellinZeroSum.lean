import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.WeilForm.ZeroSideSampleMellin
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form of a tame test is its Mellin zero sum, free of `x`

For `2 ≤ x` and `v` tame on `[1/x, 1]`, at `P = x`, `R = ⌈log₂ x⌉`:
`Q(w_v) = Σ_ρ m_ρ Re(M[v](1 − ρ) M[v](ρ))`, summable, with no pole or archimedean term and no dependence on
`x`, so `Q_x(w_v) = Q_{x'}(w_v)` for `x ≤ x'`. Per zero the term is `(m_ρ/4)(|α_ρ|² − |β_ρ|²)` with
`α_ρ, β_ρ = M[v](ρ) ± conj M[v](1 − ρ)`; on the line it is `m_ρ|M[v](ρ)|² = m_ρ‖W_L f(γ)‖²`.
-/

noncomputable section

open MeasureTheory Real Set Complex ComplexConjugate

namespace Cvs.WeilForm.MellinZeroSum
open Cvs.ZeroCounting

open Cvs.WeilForm.SelfConvolutionTransform (cf)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.WeilForm.ZeroSideSampleMellin (logWin)

/-- The nontrivial zeros. -/
abbrev Z := Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet

/-! ### Tame tests across scales -/

theorem supp_exp {v : ℝ → ℝ} {x : ℕ} (hx0 : (0 : ℝ) < x) (hv : Tame v (1 / x) 1) :
    ∀ θ ∉ Icc (Real.exp (-Real.log x)) 1, v θ = 0 := by
  rw [Real.exp_neg, Real.exp_log hx0, ← one_div]; exact hv.supp

/-! ### The zero sum in Mellin coordinates -/

/-- The zero-side term `m_ρ Re(M[v](1 − ρ) M[v](ρ))`. -/
def zeroTerm (v : ℝ → ℝ) (rho : Z) : ℝ :=
  (Cvs.Criterion.divisorWeight rho : ℝ) * (mellinR v (1 - rho) * mellinR v rho).re

/-- The zero-side term is the multiplicity times the square transform at the zero point. -/
theorem zeroTerm_eq_sqTransform {v : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ θ ∉ Icc (Real.exp (-L)) 1, v θ = 0) (rho : Z) :
    zeroTerm v rho = (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Cvs.Detection.sqTransform L (cf (logWin L v)) (zPoint rho)).re := by
  rw [zeroTerm, zPoint, Cvs.WeilForm.ZeroSideSampleMellin.sqTransform_logWin_zPoint hL hv]

/-- **The window form of a tame test is its Mellin zero sum**: for `2 ≤ x` and `v` tame on `[1/x, 1]`,
`Q(w_v) = Σ_ρ m_ρ Re(M[v](1 − ρ) M[v](ρ))`, the family summable. -/
theorem Q_wv_eq_zeroSum {x : ℕ} (hx : 2 ≤ x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.Approximant.SpineCouplingTailPairing.wv (Nat.cast_pos.mpr (by omega)) hv) = ∑' rho : Z, zeroTerm v rho
    ∧ Summable (zeroTerm v) := by
  have hx0 : (0 : ℝ) < x := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ rho : Z, zeroTerm v rho = (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Cvs.Detection.sqTransform (Real.log x) (cf (Cvs.Approximant.SpineCouplingTailPairing.fv x v)) (zPoint rho)).re := fun rho => by
    rw [Cvs.WeilForm.ZeroSideSampleMellin.fv_eq_logWin]
    exact zeroTerm_eq_sqTransform (Real.log_natCast_nonneg x) (supp_exp hx0 hv) rho
  obtain ⟨h1, h2⟩ := Cvs.WeilForm.TameWindowZeroSum.Q_wv_eq_kernelZeroSide hx hv 0 0
  constructor
  · rw [h1, kernelZeroSide]; exact tsum_congr fun rho => (hterm rho).symm
  · convert h2 using 1; funext rho; exact hterm rho

/-! ### The per-zero split -/

/-! ### The on-line measure norm and the off-line remainder -/

end Cvs.WeilForm.MellinZeroSum
