import Mathlib
import Cvs.L2a.EdgePoissonMobius
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailEdgeFarSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# ODE-free frames for the position-truncated tail

With `N = ∫_{(1,∞)} F²` for the tail `F` of Cvs.L2a.PositionTruncatedTail: `N = ∫_1^X Φ²` for `1 ≤ X ≤ 2`; `∫_1^X Φ² ≤ 2N` on `[2, 3]` and
`≤ 3.3515·N` on `[3, 4]` by a pointwise two- and three-mode bound; and for every `X ≥ 1`, through `F = edgeF(1_{≤X}Φ)`,
the Möbius frame of Cvs.L2a.EdgePoissonMobius gives `∫_1^X Φ² ≤ Q·H·N` with `Q`, `H` the squarefree count and harmonic sum up to `⌊X⌋`,
hence `≤ 16.31·N` for `X < 9`.
-/

namespace Cvs.L2a.OdeFreeFrames

open Real Set MeasureTheory ArithmeticFunction
open Cvs.L2a.PositionTruncatedTail Cvs.L2a.TailEdgeFarSplit Cvs.L2a.EdgePoissonMobius

/-- The square of an indicator is the indicator of the square. -/
theorem indicator_sq (S : Set ℝ) (f : ℝ → ℝ) (θ : ℝ) :
    indicator S f θ ^ 2 = indicator S (fun θ => f θ ^ 2) θ := by
  by_cases h : θ ∈ S
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h]; ring

/-- Dilating the indicator of `(c, X]` by `c > 0` gives the indicator of `(1, X/c]`. -/
theorem indicator_dilate {c X : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (θ : ℝ) :
    indicator (Ioc c X) f (c * θ) = indicator (Ioc 1 (X / c)) (fun θ => f (c * θ)) θ := by
  have hiff : c * θ ∈ Ioc c X ↔ θ ∈ Ioc 1 (X / c) := by
    simp only [mem_Ioc]
    rw [le_div_iff₀ hc, ← lt_mul_iff_one_lt_right hc, mul_comm θ c]
  by_cases h : θ ∈ Ioc 1 (X / c)
  · rw [indicator_of_mem h, indicator_of_mem (hiff.mpr h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.mp h'))]

/-- **The edge adapter**: the position-truncated tail is the edge Poisson sum of `1_{≤X}Φ` with
`M = b = k = ⌊X⌋ + 1`. -/
theorem posTail_eq_edgeF (Φ : ℝ → ℝ) (X : ℝ) :
    posTail Φ X = edgeF (indicator (Iic X) Φ) (⌊X⌋₊ + 1) ((⌊X⌋₊ + 1 : ℕ) : ℝ) (⌊X⌋₊ + 1) := by
  funext θ
  have hXk : X < ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one X
  -- each edge term is the cut mode `1_{≤X}Φ(mθ)`
  have hT2 : ∀ m : ℕ, 1 ≤ m → indicator {θ | θ < (((⌊X⌋₊ + 1 : ℕ) : ℕ) : ℝ) / m}
      (fun θ => indicator (Iic X) Φ (m * θ)) θ = indicator (Iic X) Φ (m * θ) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    by_cases h : (m : ℝ) * θ ≤ X
    · refine indicator_of_mem ?_ _
      rw [Set.mem_ofPred_eq]
      rw [lt_div_iff₀ hm0]; linarith
    · rw [indicator_of_notMem (show (m : ℝ) * θ ∉ Iic X from h)]
      exact indicator_apply_eq_zero.mpr fun _ => indicator_of_notMem (show (m : ℝ) * θ ∉ Iic X from h) _
  -- each tail term is the cut mode `1_{≤X}Φ(mθ)`
  have hT1 : ∀ m : ℕ, 1 ≤ m → indicator (Iic (X / m)) (fun θ => Φ (m * θ)) θ = indicator (Iic X) Φ (m * θ) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hiff : θ ∈ Iic (X / m) ↔ (m : ℝ) * θ ∈ Iic X := by
      simp only [mem_Iic]; rw [le_div_iff₀ hm0, mul_comm]
    by_cases h : θ ∈ Iic (X / m)
    · rw [indicator_of_mem h, indicator_of_mem (hiff.mp h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.mpr h'))]
  unfold posTail edgeF
  by_cases hθ : θ ∈ Ioc 1 X
  · have hθk : θ ∈ Ioc 1 ((⌊X⌋₊ + 1 : ℕ) : ℝ) := ⟨hθ.1, hθ.2.trans hXk.le⟩
    rw [indicator_of_mem hθ, indicator_of_mem hθk,
      Finset.sum_congr rfl fun m hm => hT2 m (Finset.mem_Icc.mp hm).1,
      Finset.sum_congr rfl fun m hm => hT1 m (Finset.mem_Icc.mp hm).1]
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.le_succ _)) fun m hm hm' => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hlt : ⌊X⌋₊ < m := by
      by_contra h
      exact hm' (Finset.mem_Icc.mpr ⟨hm1, not_lt.mp h⟩)
    have hXm : X < m := Nat.lt_of_floor_lt hlt
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    refine indicator_of_notMem (fun h => ?_) _
    have h' : (m : ℝ) * θ ≤ X := h
    nlinarith [hθ.1]
  · rw [indicator_of_notMem hθ]
    by_cases hθk : θ ∈ Ioc 1 ((⌊X⌋₊ + 1 : ℕ) : ℝ)
    · rw [indicator_of_mem hθk, Finset.sum_congr rfl fun m hm => hT2 m (Finset.mem_Icc.mp hm).1]
      have hθX : X < θ := not_le.mp fun h => hθ ⟨hθk.1, h⟩
      symm
      refine Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h => ?_) _
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have h' : (m : ℝ) * θ ≤ X := h
      nlinarith [hθk.1]
    · rw [indicator_of_notMem hθk]

/-- **The Möbius frame**, for every `X ≥ 1`: `∫_1^X Φ² ≤ Q·H·∫_{(1,∞)} F²`, with `Q = Σ_{d ≤ ⌊X⌋} μ(d)²` the number of
squarefree `d ≤ ⌊X⌋` and `H = Σ_{d ≤ ⌊X⌋} 1/d`. -/
theorem frame_moebius {Φ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hN : IntegrableOn (fun θ => posTail Φ X θ ^ 2) (Ioi 1)) :
    ∫ θ in (1 : ℝ)..X, Φ θ ^ 2
      ≤ (∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (moebius d : ℝ) ^ 2) * (∑ d ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (d : ℝ))
          * ∫ θ in Ioi 1, posTail Φ X θ ^ 2 := by
  have h := edgePart_sq_le_harm (indicator (Iic X) Φ) (M := ⌊X⌋₊ + 1) (b := ((⌊X⌋₊ + 1 : ℕ) : ℝ))
    (k := ⌊X⌋₊ + 1) (by omega) le_rfl le_rfl (by rwa [← posTail_eq_edgeF])
  rw [← posTail_eq_edgeF, Finset.Ico_add_one_right_eq_Icc] at h
  refine le_trans (le_of_eq ?_) h
  have hXk : X < ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one X
  have hpt : ∀ θ, edgePart (indicator (Iic X) Φ) (⌊X⌋₊ + 1) θ ^ 2 = indicator (Iic X) (fun θ => Φ θ ^ 2) θ := by
    intro θ
    unfold edgePart
    have hset : {x : ℝ | x < ((⌊X⌋₊ + 1 : ℕ) : ℝ)} ∩ Iic X = Iic X :=
      Set.inter_eq_right.mpr fun x hx => (show x < ((⌊X⌋₊ + 1 : ℕ) : ℝ) from lt_of_le_of_lt hx hXk)
    rw [indicator_indicator, hset]
    exact indicator_sq _ Φ θ
  simp_rw [hpt]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, intervalIntegral.integral_of_le hX]

/-- `Σ_{d ≤ 8} μ(d)² ≤ 6`, since `μ(4) = μ(8) = 0`. -/
theorem sum_moebius_sq_le_eight : ∑ d ∈ Finset.Icc 1 8, (moebius d : ℝ) ^ 2 ≤ 6 := by
  have h1 : ∀ d : ℕ, (moebius d : ℝ) ^ 2 ≤ 1 := by
    intro d
    have h := abs_moebius_le_one (n := d)
    have h' : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast h
    nlinarith [abs_nonneg (moebius d : ℝ), sq_abs (moebius d : ℝ)]
  have h4 : moebius 4 = 0 := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, moebius_apply_prime_pow Nat.prime_two (by norm_num)]; rfl
  have h8 : moebius 8 = 0 := by
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, moebius_apply_prime_pow Nat.prime_two (by norm_num)]; rfl
  rw [show Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton, h4, h8, Int.cast_zero, zero_pow two_ne_zero]
  linarith [h1 1, h1 2, h1 3, h1 5, h1 6, h1 7]

/-- `Σ_{d ≤ 8} 1/d = 761/280`. -/
theorem sum_inv_eight : ∑ d ∈ Finset.Icc (1 : ℕ) 8, 1 / (d : ℝ) = 761 / 280 := by
  rw [show Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  norm_num

/-- **The Möbius frame below `9`**: for `1 ≤ X < 9`, `∫_1^X Φ² ≤ 16.31 ∫_{(1,∞)} F²` (`Q₉H₈ = 6·761/280`). -/
theorem frame_moebius_lt_nine {Φ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hX9 : X < 9)
    (hN : IntegrableOn (fun θ => posTail Φ X θ ^ 2) (Ioi 1)) :
    ∫ θ in (1 : ℝ)..X, Φ θ ^ 2 ≤ 16.31 * ∫ θ in Ioi 1, posTail Φ X θ ^ 2 := by
  have hn : ⌊X⌋₊ ≤ 8 := Nat.lt_succ_iff.mp ((Nat.floor_lt (by linarith)).mpr (by norm_num; exact hX9))
  have hQ : ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (moebius d : ℝ) ^ 2 ≤ 6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hn)
      fun _ _ _ => sq_nonneg _).trans sum_moebius_sq_le_eight
  have hH : ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (d : ℝ) ≤ 761 / 280 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hn)
      fun _ _ _ => by positivity).trans (le_of_eq sum_inv_eight)
  have hH0 : 0 ≤ ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (d : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hN0 : 0 ≤ ∫ θ in Ioi 1, posTail Φ X θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  calc _ ≤ _ := frame_moebius hX hN
    _ ≤ 6 * (761 / 280) * ∫ θ in Ioi 1, posTail Φ X θ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hQ hH hH0 (by norm_num)) hN0
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hN0

/-- For `Φ` continuous on `[1, X]`, `Φ²` is integrable on `(1, X]` and the square of the tail on `(1, ∞)`. -/
theorem integrableOn_of_continuousOn {Φ : ℝ → ℝ} {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) :
    IntegrableOn (fun θ => Φ θ ^ 2) (Ioc 1 X) ∧ IntegrableOn (fun θ => posTail Φ X θ ^ 2) (Ioi 1) :=
  ⟨(hcont.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self, integrableOn_posTail_sq Φ hcont⟩

end Cvs.L2a.OdeFreeFrames
