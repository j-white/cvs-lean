import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ZeroConfigCounting
import Cvs.Zeta.ZeroConfigDefs
import Cvs.Zeta.ZetaReflect
import Cvs.Zeta.ZetaSeam
import Cvs.Zeta.ZetaSeamStatement

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Cvs.Zeta.Base/Statement/SeamClosed.lean — the ζ-seam is closed.
All four fields of Cvs.Zeta.Base.ZetaSeam are theorems of Mathlib:
  one_le_mult, finite_window  — Cvs.Zeta.Base/Statement/Seam.lean ;
  reflect_zero, mult_reflect  — Cvs.Zeta.Base/ZetaReflect.lean (Schwarz reflection
                                 riemannZeta_conj + functional equation at the analyticOrderAt level).
Hence the abstract ZeroConfig of ζ's nontrivial zeros and [eq:trivialchain] are hypothesis-free.
-/

noncomputable section

namespace Cvs.Zeta.Base

/-- The ζ-seam, fully discharged: no hypotheses. -/
theorem zetaSeam : ZetaSeam := ZetaSeam.of_reflect zeta_reflect_zero zeta_mult_reflect

/-- The nontrivial zeros of ζ with multiplicities, as an abstract Cvs.Zeta.Base.ZeroConfig — hypothesis-free.
carrier = {ρ | IsNontrivialZero ρ}, mult = zeroMult (both rfl). -/
def zetaZeroConfig : ZeroConfig := zetaZeros zetaSeam

@[simp] lemma zetaZeroConfig_carrier : zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl

@[simp] lemma zetaZeroConfig_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N _ _ _
@[simp] lemma zetaZeroConfig_N0star (T₁ T₂ : ℝ) : zetaZeroConfig.N0star T₁ T₂ = N0star T₁ T₂ :=
  zetaZeros_N0star _ _ _
@[simp] lemma zetaZeroConfig_N0s (T₁ T₂ : ℝ) : zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s _ _ _
@[simp] lemma zetaZeroConfig_Nd (T₁ T₂ : ℝ) : zetaZeroConfig.Nd T₁ T₂ = Ndist T₁ T₂ :=
  zetaZeros_Nd _ _ _

/-- [eq:trivialchain] for ζ, hypothesis-free: N₀ˢ ≤ N₀* ≤ N₀ ≤ N and N₀ˢ ≤ Nˢ ≤ N_d ≤ N. -/
theorem trivial_chain₀ (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ ≤ N0star T₁ T₂ ∧ N0star T₁ T₂ ≤ N0 T₁ T₂ ∧ N0 T₁ T₂ ≤ Ncount T₁ T₂ ∧
    N0simple T₁ T₂ ≤ Nsimple T₁ T₂ ∧ Nsimple T₁ T₂ ≤ Ndist T₁ T₂ ∧ Ndist T₁ T₂ ≤ Ncount T₁ T₂ :=
  trivial_chain zetaSeam T₁ T₂

/-- Finiteness of every ordinate window of nontrivial zeros, hypothesis-free. -/
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  simpa [zetaZeros_window] using (zetaZeros zetaSeam).window_finite T₁ T₂

end Cvs.Zeta.Base
