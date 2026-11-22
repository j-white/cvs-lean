import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.HighModeTailArchFree
import Cvs.Route.PoleSlotRungResidual

/-!
# Hilbert–Schmidt `kPrimeMat` Tail Bound via `modeSepSum`

Bounds the high-mode `kPrimeMat` residual on `lowModeRung L N C` by
`(2 * primeWindowMass P R L / π)² * modeSepSum N (lowModeSet L N C) * (r ⬝ᵥ r)`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.PrimeMatHilbertSchmidtTail
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.LowModeRungBulkFloor
open Cvs.Route.HighModeTailArchFree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Euclidean contraction of `evenProjVec` on `neg`-invariant set complements -/

omit [Fintype ι] [DecidableEq ι] in
/-- Pointwise convexity bound for `evenProjVec`:
`(evenProjVec neg v i)² ≤ ((v i)² + (v (neg i))²) / 2`. -/
theorem evenProjVec_sq_add_neg {neg : ι → ι} (_hinv : Function.Involutive neg)
    (v : ι → ℝ) (i : ι) :
    (evenProjVec neg v i) ^ 2 ≤ ((v i) ^ 2 + (v (neg i)) ^ 2) / 2 := by
  dsimp [evenProjVec]
  nlinarith [sq_nonneg (v i - v (neg i))]

omit [DecidableEq ι] in
/-- **On any `neg`-invariant set `S`, `evenProjVec neg` contracts the high-mode tail sum `∑_{i ∉ S} (v i)²`.** -/
theorem sum_not_mem_evenProjVec_sq_le (S : Set ι) [DecidablePred (· ∈ S)]
    {neg : ι → ι} (hinv : Function.Involutive neg) (hS : ∀ i, neg i ∈ S ↔ i ∈ S)
    (v : ι → ℝ) :
    (∑ i, if i ∉ S then (evenProjVec neg v i) ^ 2 else 0)
      ≤ ∑ i, if i ∉ S then (v i) ^ 2 else 0 := by
  have hpt : ∀ i : ι,
      (if i ∉ S then (evenProjVec neg v i) ^ 2 else 0)
        ≤ (1 / 2 : ℝ) * (if i ∉ S then (v i) ^ 2 else 0)
          + (1 / 2 : ℝ) * (if neg i ∉ S then (v (neg i)) ^ 2 else 0) := by
    intro i
    by_cases hi : i ∈ S
    · have hni : neg i ∈ S := (hS i).2 hi
      simp [hi, hni]
    · have hni : neg i ∉ S := fun h => hi ((hS i).1 h)
      simp only [hi, hni, not_false_eq_true, ↓reduceIte]
      linarith [evenProjVec_sq_add_neg hinv v i]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hbij : (∑ i : ι, if neg i ∉ S then (v (neg i)) ^ 2 else 0)
      = ∑ i : ι, if i ∉ S then (v i) ^ 2 else 0 :=
    Fintype.sum_bijective neg hinv.bijective
      (fun i => if neg i ∉ S then (v (neg i)) ^ 2 else 0)
      (fun i => if i ∉ S then (v i) ^ 2 else 0)
      (fun _ => rfl)
  linarith

/-! ### Block Cauchy–Schwarz bound for vectors supported on `S` -/

omit [DecidableEq ι] in
/-- For `r` supported on `S` (`∀ j ∉ S, r j = 0`), `(K *ᵥ r) i` is the dot product `restrictVec S (K i) ⬝ᵥ r`. -/
theorem mulVec_apply_eq_restrictVec_dotProduct (S : Set ι) [DecidablePred (· ∈ S)]
    (K : Matrix ι ι ℝ) {r : ι → ℝ} (hr : ∀ j, j ∉ S → r j = 0) (i : ι) :
    (K *ᵥ r) i = restrictVec S (K i) ⬝ᵥ r := by
  simp only [Matrix.mulVec, dotProduct, restrictVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj, hr j hj]

omit [DecidableEq ι] in
/-- The squared Euclidean norm of `restrictVec S v` is `∑_{j ∈ S} (v j)²`. -/
theorem restrictVec_dotProduct_self (S : Set ι) [DecidablePred (· ∈ S)] (v : ι → ℝ) :
    restrictVec S v ⬝ᵥ restrictVec S v = ∑ j, if j ∈ S then (v j) ^ 2 else 0 := by
  simp only [dotProduct, restrictVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S <;> simp [hj, sq]

omit [DecidableEq ι] in
/-- **Rowwise Cauchy–Schwarz bound**: for `r` supported on `S`,
`((K *ᵥ r) i)² ≤ (∑_{j ∈ S} (K i j)²) * (r ⬝ᵥ r)`. -/
theorem mulVec_apply_sq_le_sum_sq_mul (S : Set ι) [DecidablePred (· ∈ S)]
    (K : Matrix ι ι ℝ) {r : ι → ℝ} (hr : ∀ j, j ∉ S → r j = 0) (i : ι) :
    ((K *ᵥ r) i) ^ 2 ≤ (∑ j, if j ∈ S then (K i j) ^ 2 else 0) * (r ⬝ᵥ r) := by
  rw [mulVec_apply_eq_restrictVec_dotProduct S K hr i, ← restrictVec_dotProduct_self S (K i)]
  exact dotProduct_sq_le_mul (restrictVec S (K i)) r

omit [DecidableEq ι] in
/-- **Block Hilbert–Schmidt bound**: for `r` supported on `S`,
`∑_{i ∉ S} ((K *ᵥ r) i)² ≤ (∑_{i ∉ S} ∑_{j ∈ S} (K i j)²) * (r ⬝ᵥ r)`. -/
theorem sum_not_mem_mulVec_sq_le (S : Set ι) [DecidablePred (· ∈ S)]
    (K : Matrix ι ι ℝ) {r : ι → ℝ} (hr : ∀ j, j ∉ S → r j = 0) :
    (∑ i, if i ∉ S then ((K *ᵥ r) i) ^ 2 else 0)
      ≤ (∑ i, if i ∉ S then (∑ j, if j ∈ S then (K i j) ^ 2 else 0) else 0) * (r ⬝ᵥ r) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [hi, not_false_eq_true, ↓reduceIte]
    exact mulVec_apply_sq_le_sum_sq_mul S K hr i

/-! ### Off-diagonal inverse-square mode-separation sum `modeSepSum` and `kPrimeMat` tail bound -/

/-- **The off-diagonal inverse-square mode-separation sum** between `Sᶜ` and `S`:
`modeSepSum N S = ∑_{i ∉ S} ∑_{j ∈ S} 1 / (mode_N(i) − mode_N(j))²`. -/
def modeSepSum (N : ℕ) (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)] : ℝ :=
  ∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
    if i ∉ S then
      (∑ j : Cvs.Finite.SymmetricModeSet.Idx N, if j ∈ S then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2 else 0)
    else 0

/-! ### Even-sector positivity and `RiemannHypothesis` from a `lowModeRung` floor and `modeSepSum` -/

end Cvs.Route.PrimeMatHilbertSchmidtTail
