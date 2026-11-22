import Mathlib
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Möbius reconstruction: every window function is the window of its Möbius profile

With `E_G(θ) = (a/θ)·Σ_{n ≤ θ/a} G(na/θ)` (Cvs.Xi.EImageWindowPoisson.eimage), the profile `G_v(u) = Σ_{m ≤ 1/u} μ(m)·v(a/(mu))/(mu)`
satisfies `E_{G_v}(θ) = v(θ)` for every `θ ∈ [a, 1]` (`eimage_mobiusProfile`): the double sum over `n, m` with
`mn ≤ θ/a` collapses by `Σ_{m | k} μ(m) = [k = 1]`.  So `window a G_v = v·1_{[a,1]}` (`window_mobiusProfile`), and
the values of `G_v` below `a` are free.  The radical lemma (Cvs.WeilForm.EImageRadical) then needs `G_v`'s regularity, not supplied here.
-/

noncomputable section

open Real
open scoped ArithmeticFunction.Moebius

namespace Cvs.Xi.MobiusReconstruction

open Cvs.Xi.EImageWindowPoisson (eimage window)

/-- The Möbius profile of a window function `v`: `G_v(u) = Σ_{m ≤ 1/u} μ(m)·v(a/(mu))/(mu)`. -/
def mobiusProfile (a : ℝ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊1 / u⌋₊, (μ m : ℝ) * (v (a / (m * u)) / (m * u))

/-- `Σ_{m ∣ k} μ(m) = [k = 1]`. -/
theorem sum_moebius_divisors (k : ℕ) : ∑ m ∈ k.divisors, (μ m : ℝ) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' : ((∑ m ∈ k.divisors, μ m : ℤ) : ℝ) = ((if k = 1 then (1:ℤ) else 0 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

/-- **The double sum over `m·n ≤ N` reindexed by `k = mn` and its divisor `m`.** -/
theorem sum_sigma_mul (N : ℕ) (F c : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n), c m * F (m * n)
      = ∑ k ∈ Finset.Icc 1 N, (∑ m ∈ k.divisors, c m) * F k := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2 * p.1, p.2⟩) (fun q => ⟨q.1 / q.2, q.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hn1, hnN⟩, hm1, hmN⟩ := hp
    have hmn : m * n ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmN
    refine ⟨⟨by nlinarith, hmn⟩, ?_⟩
    rw [Nat.mem_divisors]
    exact ⟨dvd_mul_right m n, by positivity⟩
  · rintro ⟨k, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨hk1, hkN⟩, hmk, hk0⟩ := hq
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hmk (by omega)
    obtain ⟨n, rfl⟩ := hmk
    rw [Nat.mul_div_cancel_left n hm0]
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hk0)
    refine ⟨⟨hn0, le_trans (Nat.le_mul_of_pos_left n hm0) hkN⟩, hm0, ?_⟩
    exact (Nat.le_div_iff_mul_le hn0).2 hkN
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp [Nat.mul_div_cancel_left n (by omega : 0 < m)]
  · rintro ⟨k, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq
    obtain ⟨⟨hk1, hkN⟩, hmk, hk0⟩ := hq
    simp [Nat.mul_div_cancel' hmk]
  · rintro ⟨n, m⟩ hp
    rfl

/-- **Möbius reconstruction**: on the window `[a, 1]`, `E_{G_v} = v`. -/
theorem eimage_mobiusProfile {a θ : ℝ} (ha : 0 < a) (hθ : a ≤ θ) (hθ1 : θ ≤ 1) (v : ℝ → ℝ) :
    eimage a (mobiusProfile a v) θ = v θ := by
  have hθ0 : 0 < θ := lt_of_lt_of_le ha hθ
  unfold eimage mobiusProfile
  set N := ⌊θ / a⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ ha]; linarith)
  -- the inner floor is `N / n`
  have hfl : ∀ n ∈ Finset.Icc 1 N, ⌊1 / ((n : ℝ) * a / θ)⌋₊ = N / n := by
    intro n hn
    have hn0 : (0:ℝ) < n := Nat.cast_pos.2 (Finset.mem_Icc.1 hn).1
    rw [show 1 / ((n : ℝ) * a / θ) = (θ / a) / n by field_simp, Nat.floor_div_natCast]
  -- the summand in the `(n, m)` form
  have hsum : ∀ n ∈ Finset.Icc 1 N, ∀ m ∈ Finset.Icc 1 (N / n),
      (μ m : ℝ) * (v (a / (m * ((n : ℝ) * a / θ))) / (m * ((n : ℝ) * a / θ)))
        = θ / a * ((μ m : ℝ) * (v (θ / ((m * n : ℕ) : ℝ)) / ((m * n : ℕ) : ℝ))) := by
    intro n hn m hm
    have hn0 : (0:ℝ) < n := Nat.cast_pos.2 (Finset.mem_Icc.1 hn).1
    have hm0 : (0:ℝ) < m := Nat.cast_pos.2 (Finset.mem_Icc.1 hm).1
    push_cast
    rw [show a / ((m:ℝ) * ((n:ℝ) * a / θ)) = θ / ((m:ℝ) * n) by field_simp]
    field_simp
  rw [Finset.sum_congr rfl (g := fun n : ℕ => ∑ m ∈ Finset.Icc 1 (N / n),
      θ / a * ((μ m : ℝ) * (v (θ / ((m * n : ℕ) : ℝ)) / ((m * n : ℕ) : ℝ))))
    fun n hn => by rw [hfl n hn]; exact Finset.sum_congr rfl (hsum n hn)]
  simp_rw [← Finset.mul_sum]
  rw [← mul_assoc, show a / θ * (θ / a) = 1 by field_simp, one_mul]
  rw [sum_sigma_mul N (fun k => v (θ / k) / k) (fun m => (μ m : ℝ))]
  simp_rw [sum_moebius_divisors]
  simp [Finset.sum_ite_eq', hN1]

end Cvs.Xi.MobiusReconstruction
