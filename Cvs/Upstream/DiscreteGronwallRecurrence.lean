import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A discrete Gronwall bound for a three-term recurrence

If `U_m = A_{m+1}U_{m+1} + B_{m+1}U_{m+2}` with `‖B‖ ≤ β < 1`, `U_m → V` and `E = Σ‖A_m + B_m − 1‖ < 1 − β`, then
`‖U_0‖ ≤ ‖V‖/(1 − E/(1 − β))`. The differences `Δ_m = U_m − U_{m+1}` satisfy
`Δ_m = (A_{m+1} + B_{m+1} − 1)U_{m+1} − B_{m+1}Δ_{m+1}`, so `(1 − β)Σ‖Δ‖ ≤ E·sup‖U‖` up to a vanishing tail.
-/

noncomputable section

open Filter Topology

namespace Cvs.Upstream.DiscreteGronwallRecurrence

/-- The difference identity `U_m − U_{m+1} = (A + B − 1)U_{m+1} − B(U_{m+1} − U_{m+2})` at index `m + 1`. -/
theorem sub_eq {U A B : ℕ → ℂ} (hrec : ∀ m, U m = A (m + 1) * U (m + 1) + B (m + 1) * U (m + 2)) (m : ℕ) :
    U m - U (m + 1) = (A (m + 1) + B (m + 1) - 1) * U (m + 1) - B (m + 1) * (U (m + 1) - U (m + 2)) := by
  rw [hrec m]; ring

/-- A partial sum of a shifted block of a summable nonnegative sequence is at most its total. -/
theorem sum_shift_le_tsum {f : ℕ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (hf : Summable f) (n N : ℕ) :
    ∑ i ∈ Finset.range N, f (n + i + 1) ≤ ∑' m, f m := by
  have e : ∑ i ∈ Finset.range N, f (n + i + 1) = ∑ m ∈ (Finset.range N).map ⟨fun i => n + i + 1, fun a b h => by
      simp only at h; omega⟩, f m := by rw [Finset.sum_map]; rfl
  rw [e]
  exact hf.sum_le_tsum _ fun m _ => hf0 m

/-- **The discrete Gronwall bound**: under the recurrence, the contraction `‖B‖ ≤ β < 1`, convergence to `V` and
`Σ‖A + B − 1‖ ≤ E < 1 − β`, `‖U_0‖ ≤ ‖V‖/(1 − E/(1 − β))`. -/
theorem norm_le_of_recurrence {U A B : ℕ → ℂ} {V : ℂ} {β E : ℝ}
    (hrec : ∀ m, U m = A (m + 1) * U (m + 1) + B (m + 1) * U (m + 2))
    (hlim : Tendsto U atTop (𝓝 V)) (hβ : ∀ m, ‖B m‖ ≤ β) (hβ1 : β < 1)
    (hsum : Summable fun m => ‖A m + B m - 1‖) (hE : ∑' m, ‖A m + B m - 1‖ ≤ E) (hEβ : E < 1 - β) :
    ‖U 0‖ ≤ ‖V‖ / (1 - E / (1 - β)) := by
  set ε : ℕ → ℝ := fun m => ‖A m + B m - 1‖ with hεd
  set Δ : ℕ → ℂ := fun m => U m - U (m + 1) with hΔd
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0)
  have h1β : 0 < 1 - β := by linarith
  have hE0 : 0 ≤ E := (tsum_nonneg fun m => norm_nonneg _).trans hE
  have hbdd : BddAbove (Set.range fun m => ‖U m‖) := hlim.norm.bddAbove_range
  set K := ⨆ m, ‖U m‖ with hKd
  have hUK : ∀ m, ‖U m‖ ≤ K := fun m => le_ciSup hbdd m
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hUK 0)
  -- one step
  have hstep : ∀ m, ‖Δ m‖ ≤ ε (m + 1) * K + β * ‖Δ (m + 1)‖ := fun m => by
    have e := sub_eq hrec m
    simp only [hΔd, hεd]
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
    · exact hUK _
    · exact hβ _
  -- the block sums
  have hblock : ∀ n N, (1 - β) * ∑ i ∈ Finset.range N, ‖Δ (n + i)‖ ≤ K * E + β * ‖Δ (n + N)‖ := by
    intro n N
    have hs : ∑ i ∈ Finset.range N, ‖Δ (n + i)‖
        ≤ ∑ i ∈ Finset.range N, (ε (n + i + 1) * K + β * ‖Δ (n + i + 1)‖) :=
      Finset.sum_le_sum fun i _ => hstep (n + i)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hs
    have hε : ∑ i ∈ Finset.range N, ε (n + i + 1) ≤ E :=
      (sum_shift_le_tsum (fun m => norm_nonneg _) hsum n N).trans hE
    have hshift : ∑ i ∈ Finset.range N, ‖Δ (n + i + 1)‖
        = ∑ i ∈ Finset.range N, ‖Δ (n + i)‖ - ‖Δ n‖ + ‖Δ (n + N)‖ := by
      have := Finset.sum_range_succ (fun i => ‖Δ (n + i)‖) N
      have h2 := Finset.sum_range_succ' (fun i => ‖Δ (n + i)‖) N
      simp only [add_zero] at h2
      have e3 : ∀ i, n + (i + 1) = n + i + 1 := fun i => by ring
      simp only [e3] at h2
      linarith
    rw [hshift] at hs
    have hΔn : 0 ≤ ‖Δ n‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hε hK0]
  -- the bound from every starting index
  have hn : ∀ n, ‖U n‖ ≤ ‖V‖ + K * E / (1 - β) := by
    intro n
    have hN : ∀ N, ‖U n‖ ≤ ‖U (n + N)‖ + (K * E + β * ‖Δ (n + N)‖) / (1 - β) := fun N => by
      have htel : U n - U (n + N) = ∑ i ∈ Finset.range N, Δ (n + i) := by
        have := Finset.sum_range_sub' (fun i => U (n + i)) N
        simp only [add_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hΔd]; ring_nf
      have h1 : ‖U n‖ ≤ ‖U (n + N)‖ + ∑ i ∈ Finset.range N, ‖Δ (n + i)‖ := by
        have : ‖U n - U (n + N)‖ ≤ ∑ i ∈ Finset.range N, ‖Δ (n + i)‖ := by
          rw [htel]; exact norm_sum_le _ _
        have := norm_sub_norm_le (U n) (U (n + N))
        linarith
      have h2 : ∑ i ∈ Finset.range N, ‖Δ (n + i)‖ ≤ (K * E + β * ‖Δ (n + N)‖) / (1 - β) := by
        rw [le_div_iff₀ h1β, mul_comm]; exact hblock n N
      linarith
    have hshiftlim : Tendsto (fun N => U (n + N)) atTop (𝓝 V) :=
      hlim.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
    have hΔlim : Tendsto (fun N => ‖Δ (n + N)‖) atTop (𝓝 0) := by
      have h2 : Tendsto (fun N => U (n + N + 1)) atTop (𝓝 V) :=
        hlim.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
      have := (hshiftlim.sub h2).norm
      simpa [hΔd, sub_self] using this
    have hR : Tendsto (fun N => ‖U (n + N)‖ + (K * E + β * ‖Δ (n + N)‖) / (1 - β)) atTop
        (𝓝 (‖V‖ + (K * E + β * 0) / (1 - β))) :=
      hshiftlim.norm.add ((tendsto_const_nhds.add (hΔlim.const_mul β)).div_const _)
    have := ge_of_tendsto hR (Eventually.of_forall hN)
    simpa using this
  have hKle : K ≤ ‖V‖ + K * E / (1 - β) := ciSup_le hn
  have hq : 0 < 1 - E / (1 - β) := by
    rw [sub_pos, div_lt_one h1β]; exact hEβ
  refine (hUK 0).trans ?_
  rw [le_div_iff₀ hq]
  have : K * E / (1 - β) = K * (E / (1 - β)) := by ring
  nlinarith

end Cvs.Upstream.DiscreteGronwallRecurrence

end
