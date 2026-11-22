import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.PrimeMatHilbertSchmidtTail

/-!
# `N`-Independent Upper Bound on `modeSepSum` and Uniform Rung-Floor Reduction

Proves `modeSepSum N S ≤ 4 * (2 * M₀ + 1)` for `S ⊆ modeCutoffSet N M₀` via telescoping inverse-square
sums, eliminating `N`-dependence from the Hilbert–Schmidt `kPrimeMat` tail bound.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeSepSumUniformBound
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.PoleSlotRungResidual
open Cvs.Route.LowModeRungBulkFloor
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.HighModeTailArchFree
open Cvs.Route.PrimeMatHilbertSchmidtTail

/-! ### Telescoping bound on the finite inverse-square sum `∑_{k=1}^K 1 / k² ≤ 2` -/

/-- For `1 ≤ k`, `1 / (k + 1)² ≤ 1 / k − 1 / (k + 1)`. -/
theorem inv_sq_le_sub_inv {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  rw [div_sub_div _ _ hk0.ne' hk1.ne', div_le_div_iff₀ (sq_pos_of_pos hk1) (mul_pos hk0 hk1)]
  nlinarith

/-- Telescoping upper bound `∑_{k=1}^{K+1} 1 / k² ≤ 2 − 1 / (K + 1)`. -/
theorem sum_Icc_inv_sq_le_two_sub (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 (K + 1), 1 / (k : ℝ) ^ 2) ≤ 2 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero =>
    simp
    norm_num
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1 + 1)]
    have hstep := inv_sq_le_sub_inv (by omega : 1 ≤ K + 1)
    push_cast at hstep ⊢
    linarith

/-- Uniform upper bound `∑_{k=1}^K 1 / k² ≤ 2` for every `K : ℕ`. -/
theorem sum_Icc_inv_sq_le_two (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2) ≤ 2 := by
  rcases K with _ | K
  · simp
  · have h1 := sum_Icc_inv_sq_le_two_sub K
    have h2 : 0 ≤ 1 / ((K : ℝ) + 1) := by positivity
    linarith

/-! ### Single-row inverse-square mode-separation bound `≤ 4` across `Cvs.Finite.SymmetricModeSet.Idx N` -/

/-- For any integer `z : ℤ`, `(z : ℝ)² = (z.natAbs : ℝ)²`. -/
theorem int_cast_sq_eq_natAbs_sq (z : ℤ) : (z : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 := by
  have h : (z.natAbs : ℤ) = z ∨ (z.natAbs : ℤ) = -z := by omega
  rcases h with h | h
  · have h' : ((z.natAbs : ℤ) : ℝ) = (z : ℝ) := by exact_mod_cast h
    simp only [Int.cast_natCast] at h'
    rw [h']
  · have h' : ((z.natAbs : ℤ) : ℝ) = -(z : ℝ) := by exact_mod_cast h
    simp only [Int.cast_natCast] at h'
    rw [h', neg_sq]

/-- Positive-half row bound: for any `N : ℕ` and `m₀ : ℤ`,
`∑_{i : Idx N, m₀ < mode_N(i)} 1 / (mode_N(i) − m₀)² ≤ 2`. -/
theorem sum_mode_gt_inv_sq_le_two (N : ℕ) (m₀ : ℤ) :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if m₀ < Cvs.Finite.SymmetricModeSet.mode N i then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
      ≤ 2 := by
  let F := Finset.univ.filter (fun i : Cvs.Finite.SymmetricModeSet.Idx N => m₀ < Cvs.Finite.SymmetricModeSet.mode N i)
  let f : Cvs.Finite.SymmetricModeSet.Idx N → ℕ := fun i => (Cvs.Finite.SymmetricModeSet.mode N i - m₀).natAbs
  have hrew : (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
        if m₀ < Cvs.Finite.SymmetricModeSet.mode N i then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
      = ∑ i ∈ F, 1 / (f i : ℝ) ^ 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcast : ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 = (f i : ℝ) ^ 2 := by
      rw [← Int.cast_sub, int_cast_sq_eq_natAbs_sq]
    rw [hcast]
  have hinj : Set.InjOn f F := by
    intro i₁ hi₁ i₂ hi₂ heq
    have h1 : m₀ < Cvs.Finite.SymmetricModeSet.mode N i₁ := (Finset.mem_filter.1 hi₁).2
    have h2 : m₀ < Cvs.Finite.SymmetricModeSet.mode N i₂ := (Finset.mem_filter.1 hi₂).2
    have hm : Cvs.Finite.SymmetricModeSet.mode N i₁ = Cvs.Finite.SymmetricModeSet.mode N i₂ := by
      dsimp [f] at heq
      omega
    exact Cvs.Finite.SymmetricModeSet.mode_injective N hm
  have hsub : F.image f ⊆ Finset.Icc 1 (N + m₀.natAbs) := by
    intro k hk
    rcases Finset.mem_image.1 hk with ⟨i, hi, rfl⟩
    have h1 : m₀ < Cvs.Finite.SymmetricModeSet.mode N i := (Finset.mem_filter.1 hi).2
    have h2 : (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ N := Cvs.Route.FreqThresholdModeCutoff.natAbs_mode_le N i
    rw [Finset.mem_Icc]
    dsimp [f]
    omega
  have himg : (∑ k ∈ F.image f, 1 / (k : ℝ) ^ 2) = ∑ i ∈ F, 1 / (f i : ℝ) ^ 2 :=
    Finset.sum_image hinj
  rw [hrew, ← himg]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
    (sum_Icc_inv_sq_le_two (N + m₀.natAbs))

/-- Negative-half row bound: for any `N : ℕ` and `m₀ : ℤ`,
`∑_{i : Idx N, mode_N(i) < m₀} 1 / (mode_N(i) − m₀)² ≤ 2`. -/
theorem sum_mode_lt_inv_sq_le_two (N : ℕ) (m₀ : ℤ) :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N i < m₀ then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
      ≤ 2 := by
  have hbij : (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
        if Cvs.Finite.SymmetricModeSet.mode N i < m₀ then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
      = ∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
          if -m₀ < Cvs.Finite.SymmetricModeSet.mode N i then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - (-m₀ : ℤ)) ^ 2 else 0 := by
    refine Fintype.sum_bijective (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Finite.SymmetricModeSet.negI_involutive N).bijective _ _ fun i => ?_
    rw [Cvs.Finite.SymmetricModeSet.mode_negI N i]
    have hlt : (-m₀ < -Cvs.Finite.SymmetricModeSet.mode N i) ↔ (Cvs.Finite.SymmetricModeSet.mode N i < m₀) := by omega
    simp only [hlt]
    split_ifs
    · push_cast
      ring
    · rfl
  rw [hbij]
  exact sum_mode_gt_inv_sq_le_two N (-m₀)

/-- **Uniform single-row inverse-square bound**: for any `N : ℕ` and `m₀ : ℤ`,
`∑_{i : Idx N, mode_N(i) ≠ m₀} 1 / (mode_N(i) − m₀)² ≤ 4`. -/
theorem sum_mode_ne_inv_sq_le_four (N : ℕ) (m₀ : ℤ) :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N i ≠ m₀ then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
      ≤ 4 := by
  have hsplit : (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
        if Cvs.Finite.SymmetricModeSet.mode N i ≠ m₀ then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
      = (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
          if m₀ < Cvs.Finite.SymmetricModeSet.mode N i then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0)
        + (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
          if Cvs.Finite.SymmetricModeSet.mode N i < m₀ then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - m₀) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases lt_trichotomy m₀ (Cvs.Finite.SymmetricModeSet.mode N i) with hlt | rfl | hgt
    · have hne : Cvs.Finite.SymmetricModeSet.mode N i ≠ m₀ := ne_of_gt hlt
      have hng : ¬ Cvs.Finite.SymmetricModeSet.mode N i < m₀ := not_lt.2 hlt.le
      simp [hne, hlt, hng]
    · simp
    · have hne : Cvs.Finite.SymmetricModeSet.mode N i ≠ m₀ := ne_of_lt hgt
      have hnl : ¬ m₀ < Cvs.Finite.SymmetricModeSet.mode N i := not_lt.2 hgt.le
      simp [hne, hgt, hnl]
  rw [hsplit]
  linarith [sum_mode_gt_inv_sq_le_two N m₀, sum_mode_lt_inv_sq_le_two N m₀]

/-- For any `S : Set (Idx N)` and `j ∈ S`, the column sum over `i ∉ S` of `1 / (mode_N(i) − mode_N(j))²` is `≤ 4`. -/
theorem sum_not_mem_inv_sq_le_four (N : ℕ) (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)]
    {j : Cvs.Finite.SymmetricModeSet.Idx N} (hj : j ∈ S) :
    (∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if i ∉ S then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2 else 0)
      ≤ 4 := by
  refine (Finset.sum_le_sum fun i _ => ?_).trans (sum_mode_ne_inv_sq_le_four N (Cvs.Finite.SymmetricModeSet.mode N j))
  by_cases hi : i ∈ S
  · simp only [hi, not_true_eq_false, ↓reduceIte]
    split_ifs <;> positivity
  · have hne : Cvs.Finite.SymmetricModeSet.mode N i ≠ Cvs.Finite.SymmetricModeSet.mode N j :=
      fun h => hi (Cvs.Finite.SymmetricModeSet.mode_injective N h ▸ hj)
    simp [hi, hne]

/-! ### Cardinality of `modeCutoffSet N M₀` and `N`-independent `modeSepSum` bounds -/

/-- For any `S : Set (Idx N)`, `modeSepSum N S ≤ 4 * (Finset.univ.filter (· ∈ S)).card`. -/
theorem modeSepSum_le_four_mul_card (N : ℕ) (S : Set (Cvs.Finite.SymmetricModeSet.Idx N)) [DecidablePred (· ∈ S)] :
    modeSepSum N S ≤ 4 * ((Finset.univ.filter (· ∈ S)).card : ℝ) := by
  have hswap : modeSepSum N S
      = ∑ j ∈ Finset.univ.filter (· ∈ S),
          (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
            if i ∉ S then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2 else 0) := by
    unfold modeSepSum
    have h1 : (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
          if i ∉ S then
            (∑ j : Cvs.Finite.SymmetricModeSet.Idx N, if j ∈ S then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2 else 0)
          else 0)
        = ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, ∑ j : Cvs.Finite.SymmetricModeSet.Idx N,
            if j ∈ S then
              (if i ∉ S then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2 else 0)
            else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ S <;> simp [hi]
    rw [h1, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S <;> simp [hj]
  rw [hswap]
  have hle : (∑ j ∈ Finset.univ.filter (· ∈ S),
        (∑ i : Cvs.Finite.SymmetricModeSet.Idx N,
          if i ∉ S then 1 / ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) - Cvs.Finite.SymmetricModeSet.mode N j) ^ 2 else 0))
      ≤ ∑ _j ∈ Finset.univ.filter (· ∈ S), (4 : ℝ) := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact sum_not_mem_inv_sq_le_four N S (Finset.mem_filter.1 hj).2
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  linarith

/-- `modeCutoffSet N M₀` has at most `2 * M₀ + 1` elements, uniformly across all `N : ℕ`. -/
theorem card_filter_modeCutoffSet_le (N M₀ : ℕ)
    [DecidablePred (· ∈ modeCutoffSet N M₀)] :
    (Finset.univ.filter (· ∈ modeCutoffSet N M₀)).card ≤ 2 * M₀ + 1 := by
  let F := Finset.univ.filter (· ∈ modeCutoffSet N M₀)
  have hcard : F.card = (F.image (Cvs.Finite.SymmetricModeSet.mode N)).card :=
    (Finset.card_image_of_injective F (Cvs.Finite.SymmetricModeSet.mode_injective N)).symm
  have hsub : F.image (Cvs.Finite.SymmetricModeSet.mode N) ⊆ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ) := by
    intro m hm
    rcases Finset.mem_image.1 hm with ⟨j, hj, rfl⟩
    have hj' : (Cvs.Finite.SymmetricModeSet.mode N j).natAbs ≤ M₀ := (Finset.mem_filter.1 hj).2
    rw [Finset.mem_Icc]
    omega
  have hle := Finset.card_le_card hsub
  rw [Int.card_Icc] at hle
  change F.card ≤ 2 * M₀ + 1
  rw [hcard]
  omega

/-- **`N`-independent bound on `modeSepSum` for any subset `S ⊆ modeCutoffSet N M₀`**:
`modeSepSum N S ≤ 4 * (2 * M₀ + 1)`. -/
theorem modeSepSum_le_of_subset_modeCutoffSet (N M₀ : ℕ) (S : Set (Cvs.Finite.SymmetricModeSet.Idx N))
    [DecidablePred (· ∈ S)] (hsub : S ⊆ modeCutoffSet N M₀) :
    modeSepSum N S ≤ 4 * (2 * (M₀ : ℝ) + 1) := by
  classical
  have hsubF : Finset.univ.filter (· ∈ S) ⊆ Finset.univ.filter (· ∈ modeCutoffSet N M₀) := by
    intro j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hsub (Finset.mem_filter.1 hj).2⟩
  have hcard : (Finset.univ.filter (· ∈ S)).card ≤ 2 * M₀ + 1 :=
    (Finset.card_le_card hsubF).trans (card_filter_modeCutoffSet_le N M₀)
  have hcardR : ((Finset.univ.filter (· ∈ S)).card : ℝ) ≤ 2 * (M₀ : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith [modeSepSum_le_four_mul_card N S]

/-- **`N`-independent bound on `modeSepSum N (modeCutoffSet N M₀)`**:
`modeSepSum N (modeCutoffSet N M₀) ≤ 4 * (2 * M₀ + 1)` for all `N M₀ : ℕ`. -/
theorem modeSepSum_modeCutoffSet_le (N M₀ : ℕ)
    [DecidablePred (· ∈ modeCutoffSet N M₀)] :
    modeSepSum N (modeCutoffSet N M₀) ≤ 4 * (2 * (M₀ : ℝ) + 1) :=
  modeSepSum_le_of_subset_modeCutoffSet N M₀ (modeCutoffSet N M₀) Set.Subset.rfl

/-! ### `N`-independent `kPrimeMat` tail bound and uniform rung-floor reductions for `A1Mat`, `M`, and `RiemannHypothesis` -/

end Cvs.Route.ModeSepSumUniformBound
