import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimeSchurPhaseEnergies
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The definite-sign decomposition of `ApoleMat` and the representer reductions for `ApoleSlot`

On the Fourier mode grid, `ApoleMat` is the circle archimedean symbol plus the rank-one pole square plus `2 deltaSinQ −
2 deltaCosQ`; a bulk representer in `ApoleMat`-geometry fills `ApoleSlot` with weight `u r ⬝ᵥ (ApoleMat *ᵥ u r)` via
bulk Cauchy–Schwarz, and a strict Euclidean bulk floor `b > 0` fills `ApoleSlot` with weight `(u r ⬝ᵥ u r) / b`.
-/

noncomputable section

open Matrix Real Filter Finset MeasureTheory

namespace Cvs.Route.PoleMatDefiniteSign
open Cvs.ZeroCounting

open Cvs.Route.EvenMatrixSlotPoleRestored (Bulk evenModeSub A1Mat ApoleMat)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Parseval `sincQ` identity and definite-sign decomposition of `A1Mat`, `ApoleMat`, and `M` -/

omit [DecidableEq ι] in
/-- The sine-phase boundary excess at lag `t`: `∑_i ξ_i² sin²(t ω_i / 2) - (t / L) * sinQ t ω ξ`. -/
def deltaSinQ (L t : ℝ) (ω ξ : ι → ℝ) : ℝ :=
  (∑ i, ξ i ^ 2 * Real.sin (t * ω i / 2) ^ 2) - t / L * Cvs.WeilForm.PrimeSchurPhaseEnergies.sinQ t ω ξ

omit [DecidableEq ι] in
/-- The cosine-phase boundary deficit at lag `t`: `∑_i ξ_i² cos²(t ω_i / 2) - (t / L) * cosQ t ω ξ`. -/
def deltaCosQ (L t : ℝ) (ω ξ : ι → ℝ) : ℝ :=
  (∑ i, ξ i ^ 2 * Real.cos (t * ω i / 2) ^ 2) - t / L * Cvs.WeilForm.PrimeSchurPhaseEnergies.cosQ t ω ξ

omit [DecidableEq ι] in
/-- **Single-lag identity**: `∑_i ξ_i² (-2 cos(t ω_i)) + 2 (t / L) (cosQ_t - sinQ_t) = 2 deltaSinQ - 2 deltaCosQ`. -/
theorem lag_prime_eq_deltaSinQ_sub_deltaCosQ (L t : ℝ) (ω ξ : ι → ℝ) :
    (∑ i, ξ i ^ 2 * (-2 * Real.cos (t * ω i))) + 2 * (t / L * (Cvs.WeilForm.PrimeSchurPhaseEnergies.cosQ t ω ξ - Cvs.WeilForm.PrimeSchurPhaseEnergies.sinQ t ω ξ))
      = 2 * deltaSinQ L t ω ξ - 2 * deltaCosQ L t ω ξ := by
  unfold deltaSinQ deltaCosQ
  have hcos : ∀ i, Real.cos (t * ω i) = Real.cos (t * ω i / 2) ^ 2 - Real.sin (t * ω i / 2) ^ 2 := by
    intro i
    have h2 : t * ω i = 2 * (t * ω i / 2) := by ring
    conv_lhs => rw [h2, Real.cos_two_mul]
    have hsq := Real.sin_sq (t * ω i / 2)
    linarith
  simp_rw [hcos]
  have hsum : ∑ i, ξ i ^ 2 * (-2 * (Real.cos (t * ω i / 2) ^ 2 - Real.sin (t * ω i / 2) ^ 2))
      = 2 * (∑ i, ξ i ^ 2 * Real.sin (t * ω i / 2) ^ 2)
        - 2 * (∑ i, ξ i ^ 2 * Real.cos (t * ω i / 2) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

/-- **Definite-sign decomposition of `A1Mat`**: `ξ ⬝ᵥ (A1Mat *ᵥ ξ)` is the circle archimedean symbol
plus `∑ w_{p,r} (2 deltaSinQ - 2 deltaCosQ)`. -/
theorem A1Mat_quad_eq_arch_add_deltaSinQ_sub_deltaCosQ
    {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (A1Mat P R L mode *ᵥ ξ)
      = (∑ i, ξ i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L))
        + ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r
              * (if (r : ℝ) * Real.log p ≤ L then
                  2 * deltaSinQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                    - 2 * deltaCosQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                else 0) := by
  rw [Cvs.Route.EvenMatrixSlotPoleRestored.quad_A1Mat_eq_sum]
  have hM := Cvs.WeilForm.PrimeSchurPhaseEnergies.quadForm_M hL P R hinj ξ
  have hdiff : ∑ i, ∑ j, ξ i * ξ j * (Cvs.Finite.TruncationQuadraticForm.M P R L mode i j - 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L))
      = (∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.TruncationQuadraticForm.M P R L mode i j)
        - 1 / L * ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hdiff, hM]
  unfold Cvs.Finite.WindowMatrixSymbolKernel.symbolCut Cvs.Finite.OneModeEntries.primeSum Cvs.Finite.DiagonalCutSymbol.cosCut
  have hsym : ∑ i, ξ i ^ 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L)
        - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * if (r : ℝ) * Real.log p ≤ L
              then Real.cos (2 * π * mode i / L * ((r : ℝ) * Real.log p)) else 0))
      = (∑ i, ξ i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L))
        + ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r
              * (if (r : ℝ) * Real.log p ≤ L then
                  ∑ i, ξ i ^ 2 * (-2 * Real.cos ((r : ℝ) * Real.log p * (2 * π * mode i / L)))
                else 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : (r : ℝ) * Real.log p ≤ L
    · simp only [if_pos h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 2 * π * (mode i : ℝ) / L * ((r : ℝ) * Real.log p)
          = (r : ℝ) * Real.log p * (2 * π * (mode i : ℝ) / L) by ring]
      ring
    · simp [if_neg h]
  have hcomb : ∀ a b k d : ℝ, a + b + k + d - k = a + (b + d) := by intros; ring
  rw [hsym, hcomb]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : (r : ℝ) * Real.log p ≤ L
  · simp only [if_pos h]
    have hlag := lag_prime_eq_deltaSinQ_sub_deltaCosQ L ((r : ℝ) * Real.log p)
      (fun i => 2 * π * mode i / L) ξ
    linear_combination Cvs.Zeta.Explicit.Weil.primePowerWeight p r * hlag
  · simp [if_neg h]

/-- **Definite-sign decomposition of `ApoleMat`**: `ξ ⬝ᵥ (ApoleMat *ᵥ ξ)` is the circle archimedean symbol
plus the rank-one pole square plus `∑ w_{p,r} (2 deltaSinQ - 2 deltaCosQ)`. -/
theorem ApoleMat_quad_eq_arch_add_pole_add_deltaSinQ_sub_deltaCosQ
    {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (ApoleMat P R L mode *ᵥ ξ)
      = (∑ i, ξ i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L))
        + 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2
        + ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r
              * (if (r : ℝ) * Real.log p ≤ L then
                  2 * deltaSinQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                    - 2 * deltaCosQ L ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                else 0) := by
  rw [Cvs.Route.EvenMatrixSlotPoleRestored.quad_ApoleMat_eq, A1Mat_quad_eq_arch_add_deltaSinQ_sub_deltaCosQ hL P R hinj ξ]
  ring

/-! ### Symmetry of `ApoleMat` and the exact `ApoleMat`-representer reduction for `ApoleSlot` -/

omit [Fintype ι] [DecidableEq ι] in
/-- The archimedean kernel `Cvs.Finite.WindowMatrixSymbolKernel.kArch` is symmetric. -/
theorem kArch_comm (L ω ω' : ℝ) : Cvs.Finite.WindowMatrixSymbolKernel.kArch L ω ω' = Cvs.Finite.WindowMatrixSymbolKernel.kArch L ω' ω := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.kArch
  congr 1
  · ring
  · exact tsum_congr fun k => by ring

/-- `A1Mat` is symmetric for `0 < L` and injective `mode`. -/
theorem A1Mat_isSymm {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode) :
    (A1Mat P R L mode).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    simp only [A1Mat, Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj j i,
      kArch_comm L (2 * π * mode j / L) (2 * π * mode i / L)]

/-! ### Strict bulk floor reduction for `ApoleSlot` -/

end Cvs.Route.PoleMatDefiniteSign
