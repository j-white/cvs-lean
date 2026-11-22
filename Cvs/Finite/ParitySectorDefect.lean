import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.DivisionVector
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.CompactTestModulusSquared
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide
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
# Both parity sectors over the zeros through the division vector, and the exact defect

For odd `o` and `x = xdiv o`: `L·oᵀMo = ∑ m_ρ Re[z_ρ²·sq_x(z_ρ)]` and `L·xᵀMx = ∑ m_ρ Re sq_x(z_ρ)`,
so for every real level `a`, `L·(a·xᵀMx − oᵀMo) = ∑ m_ρ Re[(a − z_ρ²)·sq_x(z_ρ)]`, with no hypothesis
on the zeros. On the critical line the term is `m_ρ (a − γ²)‖Ŵ_x(γ)‖²`.
-/

noncomputable section

open Real Matrix Cvs.Finite.SymmetricModeSet Cvs.Finite.OddEigenvectorResolvent Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.ParitySectorDefect
open Cvs.ZeroCounting

/-! ### The odd sector over the zeros, for any symmetric mode set -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} {mode : ι → ℤ} {neg : ι → ι}

/-- **The odd CvS form is the zero side of its sine polynomial**: `L·oᵀMo = ∑ m_ρ Re sq_o(z_ρ)`. -/
theorem quadForm_odd_eq_zeroSide (hL : 0 < L) (hinj : Function.Injective mode)
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ}
    (hodd : ∀ i, o (neg i) = -o i) :
    L * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ o))
      = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Cvs.Detection.sqTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L mode o))
              (Cvs.ZeroCounting.zPoint rho)).re := by
  have h := Cvs.Finite.OddSectorZeroSide.zeroSide_sineSum hL mode o 0 0
  rw [Cvs.Finite.OddSectorSineSums.weilForm_sineSum_eq_ddMatrix hL _ _ hinj hinv hmode hodd] at h
  unfold Cvs.ZeroCounting.kernelZeroSide at h
  exact h.symm

omit [DecidableEq ι] in
/-- The odd zero side is summable. -/
theorem summable_zeroSide_sine (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Cvs.Detection.sqTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L mode o))
          (Cvs.ZeroCounting.zPoint rho)).re := by
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := Cvs.Finite.OddSectorZeroSide.admissible_of_C2 hL
    (Cvs.Finite.OddSectorZeroSide.hasDerivAt_sinePoly L mode o)
    (Cvs.Finite.OddSectorZeroSide.hasDerivAt_sinePoly' L mode o)
    (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly L mode o)
    (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly' L mode o)
    (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly'' L mode o)
    (Cvs.Finite.OddSectorZeroSide.sinePoly_zero L mode o) (Cvs.Finite.OddSectorZeroSide.sinePoly_L hL mode o)
    (Cvs.Finite.OddSectorZeroSide.abs_sinePoly_le L mode o) (Cvs.Finite.OddSectorZeroSide.abs_sinePoly''_le L mode o)
  exact Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide.summable_sqTransform_zeroSide₂ hC0 hC2 hplain hquad

end General

/-! ### Both sectors through the division vector -/

variable {L : ℝ} {N : ℕ}

/-- The CvS matrix with every prime power below `e^L`, on `Idx N`. -/
abbrev MX (L : ℝ) (N : ℕ) : Matrix (Idx N) (Idx N) ℝ :=
  Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N)

/-- The division vector's square transform. -/
abbrev sqX (L : ℝ) (N : ℕ) (o : Idx N → ℝ) : ℂ → ℂ :=
  Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)))

/-- **The odd form over the zeros, through the division vector**: `L·oᵀMo = ∑ m_ρ Re[z_ρ²·sq_x(z_ρ)]`. -/
theorem oddForm_zeroSide (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) :
    L * (o ⬝ᵥ (MX L N *ᵥ o)) = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.ZeroCounting.zPoint rho ^ 2 * sqX L N o (Cvs.ZeroCounting.zPoint rho)).re := by
  rw [quadForm_odd_eq_zeroSide hL (mode_injective N) (negI_involutive N) (mode_negI N) hodd]
  exact tsum_congr fun rho => by rw [Cvs.Finite.DivisionVector.sqTransform_sinePoly_eq_sq_mul hL hodd]

/-- **The even form of the division vector over the zeros**: `L·xᵀMx = ∑ m_ρ Re sq_x(z_ρ)`. -/
theorem evenForm_zeroSide (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) :
    L * (xdiv L N o ⬝ᵥ (MX L N *ᵥ xdiv L N o)) = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ) * (sqX L N o (Cvs.ZeroCounting.zPoint rho)).re := by
  have h := Cvs.Finite.ZeroSideGramMatrix.zeroSide_eq_ddMatrix hL (mode_injective N) (negI_involutive N)
    (mode_negI N) (xdiv_even hL N hodd) 0 0
  unfold Cvs.ZeroCounting.kernelZeroSide at h
  exact h.symm

/-- The odd zero side through the division vector is summable. -/
theorem summable_odd (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Cvs.ZeroCounting.zPoint rho ^ 2 * sqX L N o (Cvs.ZeroCounting.zPoint rho)).re :=
  (summable_zeroSide_sine hL (mode N) o).congr fun rho => by
    rw [Cvs.Finite.DivisionVector.sqTransform_sinePoly_eq_sq_mul hL hodd]

/-- The even zero side of the division vector is summable. -/
theorem summable_even (hL : 0 < L) (o : Idx N → ℝ) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ) * (sqX L N o (Cvs.ZeroCounting.zPoint rho)).re := by
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := Cvs.Finite.OddSectorZeroSide.admissible_of_C2 hL
    (Cvs.Finite.EvenSectorZeroSide.hasDerivAt_cosPoly L (mode N) (xdiv L N o))
    (Cvs.Finite.EvenSectorZeroSide.hasDerivAt_cosPoly' L (mode N) (xdiv L N o))
    (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L (mode N) (xdiv L N o))
    (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly' L (mode N) (xdiv L N o))
    (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly'' L (mode N) (xdiv L N o))
    (Cvs.Finite.DivisionVector.cosPoly_xdiv_zero L o) (Cvs.Finite.DivisionVector.cosPoly_xdiv_L hL o)
    (Cvs.Finite.EvenSectorZeroSide.abs_cosPoly_le L (mode N) (xdiv L N o))
    (Cvs.Finite.EvenSectorZeroSide.abs_cosPoly''_le L (mode N) (xdiv L N o))
  exact Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide.summable_sqTransform_zeroSide₂ hC0 hC2 hplain hquad

/-! ### The exact defect, with no hypothesis on the zeros -/

/-- The odd zero-side term `m_ρ·Re[z_ρ²·sq_x(z_ρ)]`. -/
def bTerm (L : ℝ) (N : ℕ) (o : Idx N → ℝ) (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : ℝ :=
  (Cvs.Criterion.divisorWeight rho : ℝ)
    * (Cvs.ZeroCounting.zPoint rho ^ 2 * sqX L N o (Cvs.ZeroCounting.zPoint rho)).re

/-- The defect term at level `a`, `m_ρ·Re[(a − z_ρ²)·sq_x(z_ρ)]`. -/
def tTerm (L : ℝ) (N : ℕ) (o : Idx N → ℝ) (a : ℝ) (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    ℝ :=
  (Cvs.Criterion.divisorWeight rho : ℝ)
    * (((a : ℂ) - Cvs.ZeroCounting.zPoint rho ^ 2) * sqX L N o (Cvs.ZeroCounting.zPoint rho)).re

theorem tTerm_eq (L : ℝ) (N : ℕ) (o : Idx N → ℝ) (a : ℝ)
    (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    tTerm L N o a rho = a * ((Cvs.Criterion.divisorWeight rho : ℝ)
      * (sqX L N o (Cvs.ZeroCounting.zPoint rho)).re) - bTerm L N o rho := by
  unfold tTerm bTerm
  rw [sub_mul, Complex.sub_re, Complex.re_ofReal_mul]
  ring

/-- The defect terms at level `a` are summable. -/
theorem summable_tTerm (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (a : ℝ) :
    Summable (tTerm L N o a) :=
  (((summable_even (N := N) hL o).mul_left a).sub (summable_odd hL hodd)).congr fun rho =>
    (tTerm_eq L N o a rho).symm

/-- **The exact defect over the zeros**, at every real level `a`:
`L·(a·xᵀMx − oᵀMo) = ∑ m_ρ Re[(a − z_ρ²)·sq_x(z_ρ)]`. -/
theorem defect_eq (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (a : ℝ) :
    L * (a * (xdiv L N o ⬝ᵥ (MX L N *ᵥ xdiv L N o)) - o ⬝ᵥ (MX L N *ᵥ o))
      = ∑' rho, tTerm L N o a rho := by
  have hA := (summable_even (N := N) hL o).mul_left a
  have hB : Summable (bTerm L N o) := summable_odd hL hodd
  rw [tsum_congr (tTerm_eq L N o a), hA.tsum_sub hB, tsum_mul_left]
  have he := evenForm_zeroSide hL hodd
  have ho := oddForm_zeroSide hL hodd
  unfold bTerm
  rw [← he, ← ho]
  ring

/-! ### On the critical line -/

/-- On the critical line the odd term is `m_ρ·γ²·‖Ŵ_x(γ)‖²`. -/
theorem bTerm_of_re (L : ℝ) (N : ℕ) (o : Idx N → ℝ) {rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (h : (rho : ℂ).re = 1 / 2) :
    bTerm L N o rho = (Cvs.Criterion.divisorWeight rho : ℝ) * (((rho : ℂ).im) ^ 2
      * ‖Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)))
          (((rho : ℂ).im : ℝ) : ℂ)‖ ^ 2) := by
  unfold bTerm sqX
  rw [Cvs.ZeroCounting.zPoint_of_re_eq_half h]
  have hs := Cvs.Detection.sqTransform_real L
    (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)) ((rho : ℂ).im)
  change Cvs.Detection.sqTransform L (cf _) _ = _ at hs
  rw [hs, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

/-- On the critical line the defect term at level `a` is `m_ρ·(a − γ²)·‖Ŵ_x(γ)‖²`. -/
theorem tTerm_of_re (L : ℝ) (N : ℕ) (o : Idx N → ℝ) (a : ℝ)
    {rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (h : (rho : ℂ).re = 1 / 2) :
    tTerm L N o a rho = (Cvs.Criterion.divisorWeight rho : ℝ) * ((a - ((rho : ℂ).im) ^ 2)
      * ‖Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)))
          (((rho : ℂ).im : ℝ) : ℂ)‖ ^ 2) := by
  unfold tTerm sqX
  rw [Cvs.ZeroCounting.zPoint_of_re_eq_half h]
  have hs := Cvs.Detection.sqTransform_real L
    (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)) ((rho : ℂ).im)
  change Cvs.Detection.sqTransform L (cf _) _ = _ at hs
  rw [hs, show ((a : ℂ) - (((rho : ℂ).im : ℝ) : ℂ) ^ 2) = (((a - ((rho : ℂ).im) ^ 2) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

end Cvs.Finite.ParitySectorDefect
