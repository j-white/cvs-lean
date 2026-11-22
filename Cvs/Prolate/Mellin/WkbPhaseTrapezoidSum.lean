import Mathlib
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.HolomorphicTrapezoidStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Summing the WKB phase along a line by the trapezoid rule

On `x = Re u ≥ 0`, `|Im u| ≤ (2−ε)c` with `c ≥ 64/ε²`: `‖ĝ″(u)‖ ≤ 21(1 + 2/√(3ε))/(x + √(3ε)c)²`. Hence along
`u_k = u₀ + 2k` with `Re u₀ ≥ 2`, `Σ_{k<K} ĝ(u_k) = ½(Ĝ(u_K) − Ĝ(u₀)) + ½(ĝ(u₀) − ĝ(u_K)) + E` with
`‖E‖ ≤ 42(1 + 2/√(3ε))/(√(3ε)c)`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum

open Cvs.Prolate.Mellin.WkbPhaseAntiderivative

variable {c ε : ℝ} {u : ℂ}

theorem norm_add_sq_ge (hc : 0 < c) (hu : |u.im| < 2 * c) :
    ‖Sq c u‖ ^ 2 + 4 * c ^ 2 ≤ ‖Sq c u + 2 * c‖ ^ 2 := by
  have hre := re_Sq_pos hc hu
  have e1 : ‖Sq c u‖ ^ 2 = (Sq c u).re ^ 2 + (Sq c u).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : ‖Sq c u + 2 * c‖ ^ 2 = ((Sq c u).re + 2 * c) ^ 2 + (Sq c u).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [e1, e2]; nlinarith

/-- **`‖ĝ″‖ ≤ 7‖u‖/‖S‖³`** once `‖S‖ ≥ 3`, `‖S‖² ≥ 3c`, `c ≥ 1`. -/
theorem norm_gh2_le (hc : 1 ≤ c) (hu : |u.im| < 2 * c) (h3 : 3 ≤ ‖Sq c u‖) (h3c : 3 * c ≤ ‖Sq c u‖ ^ 2) :
    ‖gh2 c u‖ ≤ 7 * ‖u‖ / ‖Sq c u‖ ^ 3 := by
  have hc0 : 0 < c := by linarith
  set σ := ‖Sq c u‖
  have hσ : 0 < σ := by linarith
  have hQ := norm_add_sq_ge hc0 hu
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc0.le]
  -- the numerator
  have hP : ‖Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
      + 12 * c ^ 2 * Sq c u + 12 * c ^ 3‖
      ≤ σ ^ 4 + 4 * c * σ ^ 3 + σ ^ 3 + 4 * c ^ 2 * σ ^ 2 + 2 * c * σ ^ 2 + 12 * c ^ 2 * σ + 12 * c ^ 3 := by
    have t := fun (a b : ℂ) => norm_add_le a b
    have s := fun (a b : ℂ) => norm_sub_le a b
    have n1 : ‖Sq c u ^ 4‖ = σ ^ 4 := by rw [norm_pow]
    have n2 : ‖4 * (c : ℂ) * Sq c u ^ 3‖ = 4 * c * σ ^ 3 := by
      rw [norm_mul, norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have n3 : ‖Sq c u ^ 3‖ = σ ^ 3 := by rw [norm_pow]
    have n4 : ‖4 * (c : ℂ) ^ 2 * Sq c u ^ 2‖ = 4 * c ^ 2 * σ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hcn]; norm_num; try (left; rfl)
    have n5 : ‖2 * (c : ℂ) * Sq c u ^ 2‖ = 2 * c * σ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have n6 : ‖12 * (c : ℂ) ^ 2 * Sq c u‖ = 12 * c ^ 2 * σ := by
      rw [norm_mul, norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have n7 : ‖12 * (c : ℂ) ^ 3‖ = 12 * c ^ 3 := by
      rw [norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
      + 12 * c ^ 2 * Sq c u) (12 * c ^ 3)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2)
      (12 * c ^ 2 * Sq c u)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2) (2 * c * Sq c u ^ 2)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3) (4 * c ^ 2 * Sq c u ^ 2)
    have := s (Sq c u ^ 4 + 4 * c * Sq c u ^ 3) (Sq c u ^ 3)
    have := t (Sq c u ^ 4) (4 * c * Sq c u ^ 3)
    linarith
  have hP7 : σ ^ 4 + 4 * c * σ ^ 3 + σ ^ 3 + 4 * c ^ 2 * σ ^ 2 + 2 * c * σ ^ 2 + 12 * c ^ 2 * σ + 12 * c ^ 3
      ≤ 7 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
    have a1 : 4 * c * σ ^ 3 + σ ^ 3 ≤ 2 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 4 * c * σ ≤ σ ^ 2 + 4 * c ^ 2 := by nlinarith [sq_nonneg (σ - 2 * c)]
      have : σ ≤ σ ^ 2 + 4 * c ^ 2 := by nlinarith
      nlinarith [sq_nonneg σ]
    have a2 : 4 * c ^ 2 * σ ^ 2 + 2 * c * σ ^ 2 ≤ 2 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 2 * c ≤ 4 * c ^ 2 := by nlinarith
      nlinarith [sq_nonneg σ]
    have a3 : 12 * c ^ 2 * σ ≤ σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 12 * c ^ 2 ≤ σ * (4 * c ^ 2) := by nlinarith
      nlinarith [sq_nonneg σ]
    have a4 : 12 * c ^ 3 ≤ σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 12 * c ^ 3 ≤ σ ^ 2 * (4 * c ^ 2) := by nlinarith
      nlinarith [sq_nonneg σ, sq_nonneg (σ ^ 2)]
    nlinarith [sq_nonneg σ]
  unfold gh2
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have hD : 0 < σ ^ 5 * ‖Sq c u + 2 * c‖ ^ 2 := by
    have : 0 < ‖Sq c u + 2 * c‖ := norm_pos_iff.mpr (Sq_add_ne_zero hc0 hu)
    positivity
  rw [div_le_div_iff₀ hD (by positivity)]
  calc ‖u‖ * ‖Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
        + 12 * c ^ 2 * Sq c u + 12 * c ^ 3‖ * σ ^ 3
      ≤ ‖u‖ * (7 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2)) * σ ^ 3 := by gcongr; exact hP.trans hP7
    _ = 7 * ‖u‖ * (σ ^ 5 * (σ ^ 2 + 4 * c ^ 2)) := by ring
    _ ≤ 7 * ‖u‖ * (σ ^ 5 * ‖Sq c u + 2 * c‖ ^ 2) := by gcongr

/-- `‖S‖² ≥ x² + 3εc²` on the region. -/
theorem norm_Sq_sq_ge (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hy : |u.im| ≤ (2 - ε) * c) :
    u.re ^ 2 + 3 * ε * c ^ 2 ≤ ‖Sq c u‖ ^ 2 := by
  rw [← norm_pow, Sq_sq]
  have h1 : (u ^ 2 + 4 * c ^ 2).re ≤ ‖u ^ 2 + 4 * (c : ℂ) ^ 2‖ := Complex.re_le_norm _
  have h2 : (u ^ 2 + 4 * (c : ℂ) ^ 2).re = u.re ^ 2 - u.im ^ 2 + 4 * c ^ 2 := by simp [sq]
  have h3 : u.im ^ 2 ≤ ((2 - ε) * c) ^ 2 := by
    have := abs_le.mp hy; nlinarith [sq_abs u.im, abs_nonneg u.im]
  have hεε : ε * ε ≤ ε := by nlinarith
  have h4 : ((2 - ε) * c) ^ 2 ≤ 4 * c ^ 2 - 3 * ε * c ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hεε (sq_nonneg c)]
  linarith

/-- **`ĝ″` on the region.** -/
theorem norm_gh2_region (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 64 / ε ^ 2 ≤ c) (hx : 0 ≤ u.re)
    (hy : |u.im| ≤ (2 - ε) * c) :
    ‖gh2 c u‖ ≤ 21 * (1 + 2 / Real.sqrt (3 * ε)) / (u.re + Real.sqrt (3 * ε) * c) ^ 2 := by
  have hc64 : 64 ≤ c := by
    have : 64 ≤ 64 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hc0 : 0 < c := by linarith
  have hεc : 64 ≤ ε * c := by
    have : 64 / ε ≤ ε * c := by
      rw [div_le_iff₀ hε]; have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hc; nlinarith
    have : 64 ≤ 64 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  have hu : |u.im| < 2 * c := by nlinarith
  set σ := ‖Sq c u‖
  set a := Real.sqrt (3 * ε) * c
  have hs3 : 0 < Real.sqrt (3 * ε) := Real.sqrt_pos.mpr (by linarith)
  have hsq3 : Real.sqrt (3 * ε) ^ 2 = 3 * ε := Real.sq_sqrt (by linarith)
  have ha : 0 < a := by positivity
  have hσ2 := norm_Sq_sq_ge hε hε1 hc0 hy
  have ha2 : a ^ 2 = 3 * ε * c ^ 2 := by simp only [a]; rw [mul_pow, hsq3]
  have h3c : 3 * c ≤ σ ^ 2 := by nlinarith [sq_nonneg u.re]
  have h3 : 3 ≤ σ := by
    have : 9 ≤ σ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (Sq c u)]
  have hg := norm_gh2_le (by linarith) hu h3 h3c
  -- `σ³ ≥ (x + a)³/3`
  have hσxa : (u.re + a) ^ 2 ≤ 2 * σ ^ 2 := by nlinarith [sq_nonneg (u.re - a)]
  have hσ0 : 0 ≤ σ := norm_nonneg _
  have hxa : 0 < u.re + a := by linarith
  have hcube : (u.re + a) ^ 3 ≤ 3 * σ ^ 3 := by
    -- `(x+a)³ ≤ (√2 σ)³ = 2√2 σ³ ≤ 3σ³`
    have h1 : u.re + a ≤ Real.sqrt 2 * σ := by
      rw [← Real.sqrt_sq hxa.le, ← Real.sqrt_sq hσ0, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h22 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have := pow_le_pow_left₀ hxa.le h1 3
    calc (u.re + a) ^ 3 ≤ (Real.sqrt 2 * σ) ^ 3 := this
      _ = Real.sqrt 2 ^ 2 * Real.sqrt 2 * σ ^ 3 := by ring
      _ ≤ 2 * (3 / 2) * σ ^ 3 := by rw [h2]; gcongr
      _ = 3 * σ ^ 3 := by ring
  -- `‖u‖ ≤ x + 2c ≤ (1 + 2/√(3ε))(x + a)`
  have hu' : ‖u‖ ≤ u.re + 2 * c := by
    have := Complex.norm_le_abs_re_add_abs_im u
    rw [abs_of_nonneg hx] at this; linarith
  have h2c : 2 * c = 2 / Real.sqrt (3 * ε) * a := by simp only [a]; field_simp
  have hu2 : ‖u‖ ≤ (1 + 2 / Real.sqrt (3 * ε)) * (u.re + a) := by
    rw [h2c] at hu'
    have : 0 ≤ 2 / Real.sqrt (3 * ε) * u.re := by positivity
    nlinarith
  have hσpos : 0 < σ := by linarith
  calc ‖gh2 c u‖ ≤ 7 * ‖u‖ / σ ^ 3 := hg
    _ ≤ 7 * ((1 + 2 / Real.sqrt (3 * ε)) * (u.re + a)) / ((u.re + a) ^ 3 / 3) :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) (by linarith)
    _ = 21 * (1 + 2 / Real.sqrt (3 * ε)) / (u.re + a) ^ 2 := by field_simp; ring

/-- `Σ_{k<K} 1/(X + 2k)² ≤ 1/(X − 2)` for `X > 2`. -/
theorem sum_inv_sq_le {X : ℝ} (hX : 2 < X) (K : ℕ) : ∑ k ∈ range K, 1 / (X + 2 * k) ^ 2 ≤ 1 / (X - 2) := by
  have key : ∀ K : ℕ, ∑ k ∈ range K, 1 / (X + 2 * k) ^ 2 ≤ 1 / 2 * (1 / (X - 2) - 1 / (X + 2 * K - 2)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hy : 2 < X + 2 * (K : ℝ) := by have := K.cast_nonneg (α := ℝ); linarith
      have e : X + 2 * ((K + 1 : ℕ) : ℝ) - 2 = X + 2 * (K : ℝ) := by push_cast; ring
      rw [e]
      have : 1 / (X + 2 * (K : ℝ)) ^ 2 ≤ 1 / 2 * (1 / (X + 2 * (K : ℝ) - 2) - 1 / (X + 2 * (K : ℝ))) := by
        generalize X + 2 * (K : ℝ) = y at hy ⊢
        have hy2 : y - 2 ≠ 0 := by linarith
        have hy0 : y ≠ 0 := by linarith
        rw [show 1 / (y - 2) - 1 / y = 2 / ((y - 2) * y) by field_simp; try ring]
        rw [div_le_iff₀ (by positivity)]
        rw [show 1 / 2 * (2 / ((y - 2) * y)) * y ^ 2 = y / (y - 2) by field_simp; try ring]
        rw [le_div_iff₀ (by linarith)]; linarith
      linarith
  refine (key K).trans ?_
  have : 0 < X + 2 * (K : ℝ) - 2 := by have := K.cast_nonneg (α := ℝ); linarith
  have : 0 ≤ 1 / (X + 2 * (K : ℝ) - 2) := by positivity
  have : 0 < 1 / (X - 2) := by apply div_pos one_pos; linarith
  linarith

/-- **The trapezoid sum along a line.** -/
theorem norm_sum_gh_sub_le (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 64 / ε ^ 2 ≤ c) {u₀ : ℂ} (hx : 2 ≤ u₀.re)
    (hy : |u₀.im| ≤ (2 - ε) * c) (K : ℕ) :
    ‖∑ k ∈ range K, gh c (u₀ + 2 * k) - (1 / 2 * (Gh c (u₀ + 2 * K) - Gh c u₀)
        + 1 / 2 * (gh c u₀ - gh c (u₀ + 2 * K)))‖
      ≤ 42 * (1 + 2 / Real.sqrt (3 * ε)) / (Real.sqrt (3 * ε) * c) := by
  have hc64 : 64 ≤ c := by
    have : 64 ≤ 64 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hc0 : 0 < c := by linarith
  set κ := 21 * (1 + 2 / Real.sqrt (3 * ε))
  set a := Real.sqrt (3 * ε) * c
  have ha : 0 < a := by have : 0 < Real.sqrt (3 * ε) := Real.sqrt_pos.mpr (by linarith); positivity
  have hκ : 0 ≤ κ := by positivity
  have hstrip : ∀ v : ℂ, |v.im| ≤ (2 - ε) * c → |v.im| < 2 * c := fun v hv => by nlinarith
  -- per-step error
  set err := fun k : ℕ => Gh c (u₀ + 2 * (k + 1 : ℕ)) - Gh c (u₀ + 2 * k) - (gh c (u₀ + 2 * k) + gh c (u₀ + 2 * (k + 1 : ℕ)))
  have herr : ∀ k : ℕ, ‖err k‖ ≤ 4 * (κ / (u₀.re + 2 * k + a) ^ 2) := by
    intro k
    set v := u₀ + 2 * (k : ℂ)
    have hvim : v.im = u₀.im := by simp [v]
    have hvre : v.re = u₀.re + 2 * k := by simp [v]
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 2, |(v + t).im| ≤ (2 - ε) * c ∧ v.re ≤ (v + t).re := by
      intro t ht; simp [hvim]; exact ⟨hy, ht.1⟩
    have h := Cvs.Upstream.HolomorphicTrapezoidStep.norm_trapezoid_le (F := Gh c) (f := gh c) (f₁ := gh1 c) (f₂ := gh2 c)
      (u := v) (M := κ / (u₀.re + 2 * k + a) ^ 2)
      (fun t ht => hasDerivAt_Gh hc0 (hstrip _ (hpt t ht).1))
      (fun t ht => hasDerivAt_gh hc0 (hstrip _ (hpt t ht).1))
      (fun t ht => hasDerivAt_gh1 hc0 (hstrip _ (hpt t ht).1))
      (fun t ht => by
        have h1 := norm_gh2_region hε hε1 hc (by linarith [(hpt t ht).2, hvre, k.cast_nonneg (α := ℝ)])
          (hpt t ht).1
        refine h1.trans ?_
        apply div_le_div_of_nonneg_left hκ (by positivity)
        have := (hpt t ht).2; rw [hvre] at this
        have : 0 < u₀.re + 2 * (k : ℝ) + a := by have := k.cast_nonneg (α := ℝ); linarith
        gcongr)
    have e : v + 2 = u₀ + 2 * ((k + 1 : ℕ) : ℂ) := by simp only [v]; push_cast; ring
    rw [e] at h
    exact h
  -- telescoping identity
  have htel : ∑ k ∈ range K, err k = Gh c (u₀ + 2 * K) - Gh c u₀ - (2 * ∑ k ∈ range K, gh c (u₀ + 2 * k)
      - gh c u₀ + gh c (u₀ + 2 * K)) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [err]; push_cast; ring
  have e : ∑ k ∈ range K, gh c (u₀ + 2 * k) - (1 / 2 * (Gh c (u₀ + 2 * K) - Gh c u₀)
      + 1 / 2 * (gh c u₀ - gh c (u₀ + 2 * K))) = -(1 / 2 : ℂ) * ∑ k ∈ range K, err k := by
    rw [htel]; ring
  rw [e, norm_mul]
  have hn : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  have hsum : ‖∑ k ∈ range K, err k‖ ≤ 4 * κ * (1 / (u₀.re + a - 2)) := by
    calc _ ≤ ∑ k ∈ range K, ‖err k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range K, 4 * κ * (1 / (u₀.re + a + 2 * k) ^ 2) := Finset.sum_le_sum fun k _ => by
          refine (herr k).trans (le_of_eq ?_); ring_nf
      _ = 4 * κ * ∑ k ∈ range K, 1 / (u₀.re + a + 2 * k) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * κ * (1 / (u₀.re + a - 2)) := by
          gcongr; exact sum_inv_sq_le (by linarith) K
  have h2 : 1 / (u₀.re + a - 2) ≤ 1 / a := by
    apply one_div_le_one_div_of_le ha; linarith
  calc 1 / 2 * ‖∑ k ∈ range K, err k‖ ≤ 1 / 2 * (4 * κ * (1 / (u₀.re + a - 2))) := by gcongr
    _ ≤ 1 / 2 * (4 * κ * (1 / a)) := by gcongr
    _ = 42 * (1 + 2 / Real.sqrt (3 * ε)) / a := by simp only [κ]; ring

end Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum
