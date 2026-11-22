import Mathlib
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zeros with multiplicity against `1/(1 + (y − γ)²)` and above a height against `1/γ²`

`Cvs.Zeta.ZeroDensityTail`'s local count with multiplicity gives `Σ_{|γ| ≤ H} m_ρ/(1 + (y − γ_ρ)²) ≤ 2112 log(2|y| + H + 5)` and, for
`H ≥ 1`, `Σ'_{|γ| ≥ H} m_ρ/γ_ρ² ≤ 528 (log(H + 5) + 1)/H`, by telescoping `log(v + 4)/v²` against
`φ(v) = (log(v + 5) + 1)/v`.
-/

noncomputable section

open Real Finset
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)

namespace Cvs.Zeta.ZeroCounting.ZeroLorentzianSums
open Cvs.ZeroCounting

/-! ### The local Cauchy sum with multiplicity -/

/-- **The zero sum against `1/(1 + (y − γ)²)` with multiplicity**: over zeros with `|γ| ≤ H`, at most
`2112 log(2|y| + H + 5)`. -/
theorem sum_mult_inv_one_add_sq_le (F : Finset nonTrivialZeroSet) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ ρ ∈ F, |(ρ : ℂ).im| ≤ H) (y : ℝ) :
    ∑ ρ ∈ F, mult ρ * (1 / (1 + (y - (ρ : ℂ).im) ^ 2)) ≤ 2112 * Real.log (2 * |y| + H + 5) := by
  classical
  set K : ℕ := ⌈|y| + H⌉₊ + 1 with hK
  have hKr : (K : ℝ) ≤ |y| + H + 2 := by
    rw [hK]; push_cast; linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ |y| + H)]
  have hKr' : |y| + H ≤ (K : ℝ) - 1 := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (|y| + H)]
  set kf : nonTrivialZeroSet → ℤ := fun ρ => ⌈(ρ : ℂ).im - y⌉ - 1 with hkf
  have hk1 : ∀ ρ : nonTrivialZeroSet, ((kf ρ : ℤ) : ℝ) < (ρ : ℂ).im - y := fun ρ => by
    simp only [hkf]; push_cast; linarith [Int.ceil_lt_add_one ((ρ : ℂ).im - y)]
  have hk2 : ∀ ρ : nonTrivialZeroSet, (ρ : ℂ).im - y ≤ ((kf ρ : ℤ) : ℝ) + 1 := fun ρ => by
    simp only [hkf]; push_cast; linarith [Int.le_ceil ((ρ : ℂ).im - y)]
  have hmaps : ∀ ρ ∈ F, kf ρ ∈ Finset.Icc (-(K : ℤ)) K := by
    intro ρ hρ
    have hγ := hH ρ hρ
    have a1 := hk1 ρ; have a2 := hk2 ρ
    have b1 : -(H : ℝ) ≤ (ρ : ℂ).im := by linarith [neg_abs_le ((ρ : ℂ).im)]
    have b2 : (ρ : ℂ).im ≤ H := (le_abs_self _).trans hγ
    have c1 : -|y| ≤ y := neg_abs_le y
    have c2 : y ≤ |y| := le_abs_self y
    rw [Finset.mem_Icc]
    constructor
    · have : (-(K : ℝ)) < (kf ρ : ℝ) + 1 := by linarith
      have : -(K : ℤ) < kf ρ + 1 := by exact_mod_cast this
      omega
    · have : ((kf ρ : ℤ) : ℝ) < K := by linarith
      exact_mod_cast this.le
  set φ : ℤ → ℝ := fun k => 4 / (1 + (k : ℝ) ^ 2) with hφ
  have hpt : ∀ ρ : nonTrivialZeroSet, 1 / (1 + (y - (ρ : ℂ).im) ^ 2) ≤ φ (kf ρ) := by
    intro ρ
    have a1 := hk1 ρ; have a2 := hk2 ρ
    have hs : (y - (ρ : ℂ).im) ^ 2 = ((ρ : ℂ).im - y) ^ 2 := by ring
    rw [hs]
    simp only [hφ]
    by_cases hk : (0 : ℝ) ≤ (kf ρ : ℝ)
    · exact Cvs.StepA.Edge.DeepPointBlaschkeCount.inv_one_add_sq_le_of_nonneg hk a1
    · have h0 : kf ρ < 0 := by exact_mod_cast (not_le.1 hk)
      have hk' : (kf ρ : ℝ) ≤ -1 := by
        have : kf ρ ≤ -1 := by omega
        exact_mod_cast this
      exact Cvs.StepA.Edge.DeepPointBlaschkeCount.inv_one_add_sq_le_of_le hk' a2
  have hlog : ∀ k ∈ Finset.Icc (-(K : ℤ)) K,
      Real.log (|y + k| + 3) ≤ Real.log (2 * |y| + H + 5) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1a : (-(K : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have h1b : (k : ℝ) ≤ K := by exact_mod_cast hk.2
    have h1 : |(k : ℝ)| ≤ K := abs_le.2 ⟨h1a, h1b⟩
    refine Real.log_le_log (by positivity) ?_
    have := abs_add_le y (k : ℝ)
    linarith
  calc ∑ ρ ∈ F, mult ρ * (1 / (1 + (y - (ρ : ℂ).im) ^ 2))
      ≤ ∑ ρ ∈ F, mult ρ * φ (kf ρ) :=
        Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hpt ρ) (mult_nonneg ρ)
    _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) K, ∑ ρ ∈ F.filter (fun ρ => kf ρ = k), mult ρ * φ (kf ρ) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) K, (∑ ρ ∈ F.filter (fun ρ => kf ρ = k), mult ρ) * φ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]
    _ ≤ ∑ k ∈ Finset.Icc (-(K : ℤ)) K, (88 * Real.log (2 * |y| + H + 5)) * φ k := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine (Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_mult_le_of_window _ (y + k) fun ρ hρ => ?_).trans ?_
        · have hρk := (Finset.mem_filter.1 hρ).2
          have a1 := hk1 ρ; have a2 := hk2 ρ
          rw [hρk] at a1 a2
          constructor <;> linarith
        · exact mul_le_mul_of_nonneg_left (hlog k hk) (by norm_num)
    _ = 88 * Real.log (2 * |y| + H + 5)
          * (4 * ∑ k ∈ Finset.Icc (-(K : ℤ)) K, 1 / (1 + (k : ℝ) ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hφ]; ring
    _ ≤ 88 * Real.log (2 * |y| + H + 5) * (4 * 6) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg y])))
        have := Cvs.StepA.Edge.DeepPointBlaschkeCount.sum_Icc_inv_one_add_sq_le K
        have : 0 < 4 / ((K : ℝ) + 1) := by positivity
        linarith
    _ = 2112 * Real.log (2 * |y| + H + 5) := by ring

/-! ### The tail above a height -/

/-- **One telescoping step**: for `v ≥ 1`, `log(v + 4)/v² ≤ 2(φ(v) − φ(v + 1))` with
`φ(v) = (log(v + 5) + 1)/v`. -/
theorem log_div_sq_le_telescope {v : ℝ} (hv : 1 ≤ v) :
    Real.log (v + 4) / v ^ 2
      ≤ 2 * ((Real.log (v + 5) + 1) / v - (Real.log (v + 1 + 5) + 1) / (v + 1)) := by
  have hv0 : 0 < v := by linarith
  have l45 : Real.log (v + 4) ≤ Real.log (v + 5) := Real.log_le_log (by linarith) (by linarith)
  have l4 : 0 ≤ Real.log (v + 4) := Real.log_nonneg (by linarith)
  have l56 : Real.log (v + 1 + 5) - Real.log (v + 5) ≤ 1 / (v + 5) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  have hfrac : v * (1 / (v + 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hX : Real.log (v + 5) ≤ (v + 1) * (Real.log (v + 5) + 1) - v * (Real.log (v + 1 + 5) + 1) := by
    nlinarith
  have heq : 2 * ((Real.log (v + 5) + 1) / v - (Real.log (v + 1 + 5) + 1) / (v + 1))
      = 2 * ((v + 1) * (Real.log (v + 5) + 1) - v * (Real.log (v + 1 + 5) + 1)) / (v * (v + 1)) := by
    field_simp
  rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
  have hX' : Real.log (v + 4) ≤ (v + 1) * (Real.log (v + 5) + 1) - v * (Real.log (v + 1 + 5) + 1) :=
    l45.trans hX
  have hv1 : v + 1 ≤ 2 * v := by linarith
  have := mul_le_mul_of_nonneg_left hX' (by positivity : (0 : ℝ) ≤ 2 * v ^ 2)
  have := mul_le_mul_of_nonneg_left hv1 (by positivity : (0 : ℝ) ≤ v * Real.log (v + 4))
  nlinarith

/-- **The telescoped sum**: for `H ≥ 1`, `Σ_{k=1}^K log(H + k + 3)/(H + k − 1)² ≤ 2(log(H + 5) + 1)/H`. -/
theorem sum_Icc_log_div_sq_le {H : ℝ} (hH : 1 ≤ H) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, Real.log (H - 1 + k + 4) / (H - 1 + k) ^ 2
      ≤ 2 * ((Real.log (H + 5) + 1) / H) := by
  have hφ0 : ∀ v : ℝ, 1 ≤ v → 0 ≤ (Real.log (v + 5) + 1) / v := fun v hv =>
    div_nonneg (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ v + 5)]) (by linarith)
  suffices h : ∀ K : ℕ, ∑ k ∈ Finset.Icc 1 K, Real.log (H - 1 + k + 4) / (H - 1 + k) ^ 2
      ≤ 2 * ((Real.log (H + 5) + 1) / H - (Real.log (H + K + 5) + 1) / (H + K)) by
    have := hφ0 (H + K) (by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith)
    linarith [h K]
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := log_div_sq_le_telescope (v := H + K) (by
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith)
    push_cast
    have e1 : H - 1 + ((K : ℝ) + 1) = H + K := by ring
    rw [e1, show H + K + 4 = H + (K : ℝ) + 4 by ring]
    rw [show H + ((K : ℝ) + 1) = H + K + 1 by ring, show H + (K : ℝ) + 1 + 5 = H + K + 1 + 5 by ring]
    linarith

/-- **The finite tail above a height**: for `H ≥ 1` and zeros with `|γ| ≥ H`,
`Σ m_ρ/γ_ρ² ≤ 528 (log(H + 5) + 1)/H`. -/
theorem sum_mult_inv_sq_le_of_ge (F : Finset nonTrivialZeroSet) {H : ℝ} (hH : 1 ≤ H)
    (hF : ∀ ρ ∈ F, H ≤ |(ρ : ℂ).im|) :
    ∑ ρ ∈ F, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) ≤ 528 * ((Real.log (H + 5) + 1) / H) := by
  set s := H - 1 with hs
  have hs0 : 0 ≤ s := by linarith
  set K : ℕ := ⌈∑ ρ ∈ F, |(ρ : ℂ).im|⌉₊ with hK
  set g : ℝ → ℝ := fun y => 1 / (y + s) ^ 2 with hg
  have hg0 : ∀ y, 1 ≤ y → 0 ≤ g y := fun y _ => by positivity
  have hgm : ∀ y y', 1 ≤ y → y ≤ y' → g y' ≤ g y := fun y y' hy hyy' => by
    simp only [hg]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hFw : ∀ ρ ∈ F, 1 ≤ |(ρ : ℂ).im| - s ∧ |(ρ : ℂ).im| - s < K + 1 := by
    intro ρ hρ
    refine ⟨by linarith [hF ρ hρ], ?_⟩
    have h1 : |(ρ : ℂ).im| ≤ ∑ ρ ∈ F, |(ρ : ℂ).im| :=
      Finset.single_le_sum (f := fun ρ : nonTrivialZeroSet => |(ρ : ℂ).im|)
        (fun _ _ => abs_nonneg _) hρ
    have h2 := Nat.le_ceil (∑ ρ ∈ F, |(ρ : ℂ).im|)
    linarith
  have hmain := Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_mult_mul_le F hs0 K hg0 hgm hFw
  have hlhs : ∑ ρ ∈ F, mult ρ * g (|(ρ : ℂ).im| - s) = ∑ ρ ∈ F, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hg, sub_add_cancel, sq_abs]
  have hrhs : ∑ k ∈ Finset.Icc 1 K, 264 * Real.log (s + k + 4) * g k
      = 264 * ∑ k ∈ Finset.Icc 1 K, Real.log (H - 1 + k + 4) / (H - 1 + k) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, hs]
    ring_nf
  rw [hlhs, hrhs] at hmain
  have := sum_Icc_log_div_sq_le hH K
  linarith

/-- **The tail above a height**: for `H ≥ 1` and any set `S` of zeros with `|γ| ≥ H`,
`Σ'_S m_ρ/γ_ρ² ≤ 528 (log(H + 5) + 1)/H`. -/
theorem tsum_mult_inv_sq_le_of_ge (S : Set nonTrivialZeroSet) {H : ℝ} (hH : 1 ≤ H)
    (hS : ∀ ρ ∈ S, H ≤ |(ρ : ℂ).im|) :
    ∑' ρ : S, mult ρ * (1 / (((ρ : nonTrivialZeroSet) : ℂ).im) ^ 2)
      ≤ 528 * ((Real.log (H + 5) + 1) / H) := by
  refine Real.tsum_le_of_sum_le (fun ρ => mul_nonneg (mult_nonneg _) (by positivity)) fun u => ?_
  have h := sum_mult_inv_sq_le_of_ge (u.map (Function.Embedding.subtype _)) hH fun ρ hρ => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_map.1 hρ
    exact hS σ σ.2
  rwa [Finset.sum_map] at h

end Cvs.Zeta.ZeroCounting.ZeroLorentzianSums
