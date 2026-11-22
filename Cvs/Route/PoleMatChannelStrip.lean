import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.PoleMatDefiniteSign
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Positive-channel / cosine-strip decomposition of `ApoleMat` and bulk contraction

`deltaSinQ + deltaCosQ = (∑ ξ_i²) − (t/L)(sinQ + cosQ) ≤ ∑ ξ_i²`, and on `evenModeSub` the boundary
`trigEnergy` collapses to shifted squares of `evenProfile`. With `posChannelQ = Arch + Pole + sinStripQ`,
`ξ ⬝ᵥ (ApoleMat *ᵥ ξ) = posChannelQ ξ − cosStripQ ξ`, so a bulk floor `cP` on `posChannelQ` and
`cosStripQ ≤ ρ · posChannelQ` (`ρ < 1`) give `ApoleBulkFloor` with constant `(1 − ρ) cP > 0`.
-/

noncomputable section

open Real Filter Finset MeasureTheory
open scoped Matrix

namespace Cvs.Route.PoleMatChannelStrip
open Cvs.ZeroCounting

open Cvs.Route.EvenMatrixSlotPoleRestored (Bulk evenModeSub A1Mat ApoleMat)
open Cvs.Route.PoleMatDefiniteSign (deltaSinQ deltaCosQ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Phase complementarity of `deltaSinQ` and `deltaCosQ` -/

/-! ### Even-sector single-square identities for `trigEnergy` on the boundary strip -/

omit [DecidableEq ι] in
/-- **The spatial profile of an even mode vector**: `Φ_ξ(s) = ∑_i ξ_i cos(s ω_i)`. -/
def evenProfile (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ i, ξ i * Real.cos (s * (2 * π * mode i / L))

/-! ### The positive-channel, cosine-strip, and digamma-ladder quadratic forms -/

omit [DecidableEq ι] in
/-- **The sine boundary-strip quadratic form** `∑_{p,r} w_{p,r} 1_{r log p ≤ L} · 2 deltaSinQ`. -/
def sinStripQ (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    Cvs.Zeta.Explicit.Weil.primePowerWeight p r
      * (if (r : ℝ) * Real.log p ≤ L then
          2 * deltaSinQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
        else 0)

omit [DecidableEq ι] in
/-- **The cosine boundary-strip quadratic form** `∑_{p,r} w_{p,r} 1_{r log p ≤ L} · 2 deltaCosQ`. -/
def cosStripQ (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    Cvs.Zeta.Explicit.Weil.primePowerWeight p r
      * (if (r : ℝ) * Real.log p ≤ L then
          2 * deltaCosQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
        else 0)

omit [DecidableEq ι] in
/-- **The positive-channel quadratic form** `posChannelQ`: circle archimedean symbol plus rank-one
pole square plus `sinStripQ`. -/
def posChannelQ (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) : ℝ :=
  (∑ i, ξ i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L))
    + 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2
    + sinStripQ P R L mode ξ

/-- **Difference-of-positives decomposition of `ApoleMat`**:
`ξ ⬝ᵥ (ApoleMat *ᵥ ξ) = posChannelQ ξ − cosStripQ ξ`. -/
theorem ApoleMat_quad_eq_posChannelQ_sub_cosStripQ {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (ApoleMat P R L mode *ᵥ ξ) = posChannelQ P R L mode ξ - cosStripQ P R L mode ξ := by
  rw [Cvs.Route.PoleMatDefiniteSign.ApoleMat_quad_eq_arch_add_pole_add_deltaSinQ_sub_deltaCosQ hL P R hinj ξ]
  unfold posChannelQ sinStripQ cosStripQ
  have hsplit : ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        Cvs.Zeta.Explicit.Weil.primePowerWeight p r
          * (if (r : ℝ) * Real.log p ≤ L then
              2 * deltaSinQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                - 2 * deltaCosQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
            else 0)
      = (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          Cvs.Zeta.Explicit.Weil.primePowerWeight p r
            * (if (r : ℝ) * Real.log p ≤ L then
                2 * deltaSinQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
              else 0))
        - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r
              * (if (r : ℝ) * Real.log p ≤ L then
                  2 * deltaCosQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  ring

/-! ### Bulk contraction of `cosStripQ` relative to `posChannelQ` -/

end Cvs.Route.PoleMatChannelStrip
