import Mathlib
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.MobiusReconstruction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Mangoldt dilation through the actual E-window

The finite window-side Mangoldt dilation becomes a logarithmic weight
through `window`: its exact image is the anticommutator with centered log.
-/

noncomputable section

open Real Set
open scoped ArithmeticFunction

namespace Cvs.Xi.MangoldtDilationEWindow

open Cvs.Xi.EImageWindowPoisson (eimage window)

/-- The angular-coordinate prime dilation on the window. -/
def primeWindow (a : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  (Icc a 1).indicator (fun u =>
    ∑ m ∈ Finset.Icc 1 ⌊1 / u⌋₊, Λ m * G (m * u))

/-- The centered angular logarithm. -/
def centeredLog (a u : ℝ) : ℝ := Real.log u - Real.log a / 2

/-- Every sample in the E-window lies in the same window. -/
theorem sample_mem_Icc {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1)
    {n : ℕ} (hn : n ∈ Finset.Icc 1 ⌊θ / a⌋₊) :
    (n : ℝ) * a / θ ∈ Icc a 1 := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnle : (n : ℝ) ≤ θ / a :=
    (Nat.le_floor_iff (by positivity : 0 ≤ θ / a)).mp (Finset.mem_Icc.mp hn).2
  constructor
  · rw [le_div_iff₀ hθ0]
    nlinarith [hθ.2]
  · rw [div_le_one hθ0]
    exact (le_div_iff₀ ha).mp hnle

/-- The finite Mangoldt sum through the E-window has weight `log r`. -/
theorem eimage_primeWindow {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1)
    (G : ℝ → ℝ) :
    eimage a (primeWindow a G) θ
      = a / θ * ∑ r ∈ Finset.Icc 1 ⌊θ / a⌋₊,
          Real.log r * G (r * a / θ) := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  unfold eimage
  congr 1
  set N := ⌊θ / a⌋₊ with hN
  have hfl : ∀ n ∈ Finset.Icc 1 N,
      ⌊1 / ((n : ℝ) * a / θ)⌋₊ = N / n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    rw [show 1 / ((n : ℝ) * a / θ) = (θ / a) / n by field_simp,
      Nat.floor_div_natCast]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n),
        Λ m * G (((m * n : ℕ) : ℝ) * a / θ) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [primeWindow, indicator_of_mem (sample_mem_Icc ha hθ hn), hfl n hn]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 2
      push_cast
      ring
    _ = ∑ r ∈ Finset.Icc 1 N, (∑ m ∈ r.divisors, Λ m) * G (r * a / θ) :=
      Cvs.Xi.MobiusReconstruction.sum_sigma_mul N (fun r => G (r * a / θ)) (fun m => Λ m)
    _ = _ := by simp only [ArithmeticFunction.vonMangoldt_sum]

/-- The logarithmic weight is the anticommutator with centered log. -/
theorem eimage_primeWindow_eq_anticommutator {a θ : ℝ} (ha : 0 < a)
    (hθ : θ ∈ Icc a 1) (G : ℝ → ℝ) :
    eimage a (primeWindow a G) θ
      = centeredLog a θ * eimage a G θ
        + eimage a (fun u => centeredLog a u * G u) θ := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  rw [eimage_primeWindow ha hθ G]
  unfold eimage
  calc
    _ = a / θ * (centeredLog a θ *
          (∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)) +
          ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, centeredLog a (n * a / θ) * G (n * a / θ)) := by
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
      have hlog : Real.log ((n : ℝ) * a / θ) = Real.log n + Real.log a - Real.log θ := by
        rw [Real.log_div (mul_pos hn0 ha).ne' hθ0.ne', Real.log_mul hn0.ne' ha.ne']
      rw [centeredLog, centeredLog, hlog]
      ring
    _ = _ := by ring

/-- The actual E-window intertwines prime dilation with its log anticommutator. -/
theorem window_primeWindow_eq_anticommutator {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    window a (primeWindow a G)
      = fun θ => centeredLog a θ * window a G θ
        + window a (fun u => centeredLog a u * G u) θ := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · simp only [window, indicator_of_mem hθ]
    exact eimage_primeWindow_eq_anticommutator ha hθ G
  · simp only [window, indicator_of_notMem hθ, mul_zero, add_zero]

end Cvs.Xi.MangoldtDilationEWindow
