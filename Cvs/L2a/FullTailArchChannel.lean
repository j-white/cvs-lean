import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.LevyConditionL1Modulus
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.LevyUnitBlocks

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean channel of `F_X` converges to that of `F_∞`

Off `θ = 2πk/c`, `F_∞` is a Poisson piece with derivative `O(1/θ)`, and it jumps by `πA/(cθ)` there. So `f_∞` has
a linear block modulus, `LevyUnitBlocks`'s block lemma gives `archFull (f_∞ − f_X) → 0`, and `archFull f_X → archFull f_∞`.
-/

set_option maxHeartbeats 1600000

namespace Cvs.L2a.FullTailArchChannel

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence Cvs.L2a.TailLogScaleTest

/-- The Poisson piece selected by `θ`: index `k = ⌊cθ/(2π)⌋`. -/
noncomputable def regTail (c : ℝ) (g : ℝ → ℝ) (θ : ℝ) : ℝ := poissonPiece c g ⌊c * θ / (2 * π)⌋₊ θ

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-! ### The Poisson pieces -/

/-- **The Poisson piece has derivative `O(1/θ)`** past its first lattice point: `|P_k'(θ)| ≤ (1 + π/c) G_s/θ`. -/
theorem abs_deriv_poissonPiece_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hc : 0 < c) {Gs : ℝ}
    (hGs : ∀ s ∈ Icc (-1 : ℝ) 1, |g s| + |g₁ s| ≤ Gs) {k : ℕ} {θ : ℝ} (hθ1 : 1 ≤ θ)
    (hk : 2 * π * k / c ≤ θ) :
    ∃ d, HasDerivAt (poissonPiece c g k) d θ ∧ |d| ≤ (1 + π / c) * Gs / θ := by
  have hθ0 : 0 < θ := by linarith
  have hπ := pi_pos
  have hcθ : 0 < c * θ := by positivity
  have hk' : 2 * π * k ≤ c * θ := by rw [div_le_iff₀ hc] at hk; linarith
  have hGs0 : 0 ≤ Gs := le_trans (by positivity) (hGs 0 ⟨by norm_num, by norm_num⟩)
  set I := Finset.Icc (-(k : ℤ)) k with hI
  set x : ℤ → ℝ := fun n => 2 * π * n / (c * θ) with hx
  have hxI : ∀ n ∈ I, x n ∈ Icc (-1 : ℝ) 1 := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have h1 : -(k : ℝ) ≤ n := by exact_mod_cast hn'.1
    have h2 : (n : ℝ) ≤ k := by exact_mod_cast hn'.2
    constructor
    · simp only [hx]; rw [le_div_iff₀ hcθ]; nlinarith
    · simp only [hx]; rw [div_le_iff₀ hcθ]; nlinarith
  have hterm : ∀ n ∈ I, HasDerivAt (fun θ : ℝ => g (2 * π * n / (c * θ))) (g₁ (x n) * (-(x n) / θ)) θ := by
    intro n hn
    have h1 : HasDerivAt (fun y : ℝ => (2 * π * n / c) * y⁻¹) ((2 * π * n / c) * (-(θ ^ 2)⁻¹)) θ :=
      (hasDerivAt_inv hθ0.ne').const_mul _
    have e : (fun y : ℝ => 2 * π * n / (c * y)) = fun y => (2 * π * n / c) * y⁻¹ := by
      funext y; rw [div_mul_eq_div_div, div_eq_mul_inv]
    have hin : HasDerivAt (fun y : ℝ => 2 * π * n / (c * y)) (-(x n) / θ) θ := by
      rw [e]; convert h1 using 1; simp only [hx]; field_simp
    exact (hg (x n) (by rw [uIcc_of_le (by norm_num)]; exact hxI n hn)).comp θ hin
  have hS := HasDerivAt.fun_sum hterm
  have hpre : HasDerivAt (fun y : ℝ => π / (c * y)) (-(π / (c * θ)) / θ) θ := by
    have h1 : HasDerivAt (fun y : ℝ => (π / c) * y⁻¹) ((π / c) * (-(θ ^ 2)⁻¹)) θ :=
      (hasDerivAt_inv hθ0.ne').const_mul _
    have e : (fun y : ℝ => π / (c * y)) = fun y => (π / c) * y⁻¹ := by
      funext y; rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [e]; convert h1 using 1; field_simp
  have hP := (hpre.mul hS).sub_const (1 / 2 * ∫ s in (-1 : ℝ)..1, g s)
  refine ⟨_, hP, ?_⟩
  have hd : -(π / (c * θ)) / θ * ∑ n ∈ I, g (2 * π * n / (c * θ))
        + π / (c * θ) * ∑ n ∈ I, g₁ (x n) * (-(x n) / θ)
      = ∑ n ∈ I, (-(π / (c * θ) / θ)) * (g (x n) + x n * g₁ (x n)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hx]; ring
  have hcard : (I.card : ℝ) = 2 * k + 1 := by
    rw [hI, Int.card_Icc]
    have : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
    rw [this]; push_cast; ring
  have hq : 0 ≤ π / (c * θ) / θ := by positivity
  rw [hd]
  calc |∑ n ∈ I, (-(π / (c * θ) / θ)) * (g (x n) + x n * g₁ (x n))|
      ≤ ∑ n ∈ I, |(-(π / (c * θ) / θ)) * (g (x n) + x n * g₁ (x n))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ I, π / (c * θ) / θ * Gs := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [abs_mul, abs_neg, abs_of_nonneg hq]
        refine mul_le_mul_of_nonneg_left ?_ hq
        have hxn := hxI n hn
        have hxa : |x n| ≤ 1 := abs_le.mpr ⟨hxn.1, hxn.2⟩
        calc |g (x n) + x n * g₁ (x n)| ≤ |g (x n)| + |x n| * |g₁ (x n)| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ |g (x n)| + 1 * |g₁ (x n)| := by gcongr
          _ ≤ Gs := by rw [one_mul]; exact hGs _ hxn
    _ = (2 * k + 1) * (π / (c * θ) / θ) * Gs := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
    _ ≤ (1 + π / c) / θ * Gs := by
        refine mul_le_mul_of_nonneg_right ?_ hGs0
        have e : (2 * k + 1) * (π / (c * θ) / θ) = (2 * π * k / (c * θ) + π / (c * θ)) / θ := by
          field_simp
        rw [e]
        refine div_le_div_of_nonneg_right (add_le_add ((div_le_one hcθ).mpr hk') ?_) hθ0.le
        exact div_le_div_of_nonneg_left hπ.le hc (by nlinarith)
    _ = (1 + π / c) * Gs / θ := by ring

/-- **The jump of the Poisson pieces** at `θ_k = 2πk/c` is `πA/(cθ_k)`, `A = g(1) + g(−1)`. -/
theorem poissonPiece_jump (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) :
    poissonPiece c g k (2 * π * k / c) - poissonPiece c g (k - 1) (2 * π * k / c)
      = π * (g 1 + g (-1)) / (c * (2 * π * k / c)) := by
  have hπ := pi_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hcast : (((k - 1 : ℕ) : ℤ)) = (k : ℤ) - 1 := by omega
  have hset : Finset.Icc (-(k : ℤ)) k
      = insert (-(k : ℤ)) (insert (k : ℤ) (Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ))) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert, hcast]; omega
  have hn1 : (k : ℤ) ∉ Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ) := by
    simp only [Finset.mem_Icc, hcast]; omega
  have hn2 : -(k : ℤ) ∉ insert (k : ℤ) (Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc, hcast]; omega
  unfold poissonPiece
  rw [hset, Finset.sum_insert hn2, Finset.sum_insert hn1]
  have e1 : 2 * π * ((-(k : ℤ) : ℤ) : ℝ) / (c * (2 * π * k / c)) = -1 := by
    push_cast; field_simp
  have e2 : 2 * π * (((k : ℤ) : ℤ) : ℝ) / (c * (2 * π * k / c)) = 1 := by
    push_cast; field_simp
  rw [e1, e2]
  ring

/-- **The mean value bound** on a Poisson piece past its first lattice point. -/
theorem abs_poissonPiece_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hc : 0 < c) {Gs : ℝ}
    (hGs : ∀ s ∈ Icc (-1 : ℝ) 1, |g s| + |g₁ s| ≤ Gs) {k : ℕ} {x y : ℝ} (hx1 : 1 ≤ x)
    (hk : 2 * π * k / c ≤ x) (hxy : x ≤ y) :
    |poissonPiece c g k y - poissonPiece c g k x| ≤ (1 + π / c) * Gs / x * (y - x) := by
  have hx0 : 0 < x := by linarith
  have hGs0 : 0 ≤ Gs := le_trans (by positivity) (hGs 0 ⟨by norm_num, by norm_num⟩)
  have hD : ∀ θ ∈ Icc x y, ∃ d, HasDerivAt (poissonPiece c g k) d θ ∧ |d| ≤ (1 + π / c) * Gs / θ :=
    fun θ hθ => abs_deriv_poissonPiece_le hg hc hGs (hx1.trans hθ.1) (hk.trans hθ.1)
  choose! d hd using hD
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := poissonPiece c g k) (f' := d)
    (s := Icc x y) (C := (1 + π / c) * Gs / x) (fun θ hθ => (hd θ hθ).1.hasDerivWithinAt)
    (fun θ hθ => by
      rw [Real.norm_eq_abs]
      refine (hd θ hθ).2.trans ?_
      exact div_le_div_of_nonneg_left (by positivity) hx0 hθ.1) (convex_Icc x y)
    ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at h

/-! ### The selected Poisson piece -/

/-- **Off the lattice `(2π/c)ℕ` the full tail is the selected Poisson piece.** -/
theorem fullTail_eq_regTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 1 < θ) (hθk : ∀ k : ℕ, c * θ / (2 * π) ≠ k) :
    fullTail (psi c g) θ = regTail c g θ := by
  have hx0 : 0 ≤ c * θ / (2 * π) := by
    have := pi_pos; have : (0 : ℝ) < θ := (by linarith); positivity
  exact fullTail_eq_poissonPiece hg hg₁ hg₂c hc hθ
    (lt_of_le_of_ne (Nat.floor_le hx0) (hθk _).symm) (Nat.lt_floor_add_one _)

/-- **The variation of the selected piece**: `|P(b) − P(a)| ≤ (K/a)(b − a) + (π|A|/(ca)) · #{lattice points in (a, b]}`,
`K = (1 + π/c) G_s`. -/
theorem abs_regTail_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hc : 0 < c) {Gs : ℝ}
    (hGs : ∀ s ∈ Icc (-1 : ℝ) 1, |g s| + |g₁ s| ≤ Gs) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |regTail c g b - regTail c g a|
      ≤ (1 + π / c) * Gs / a * (b - a)
        + π * |g 1 + g (-1)| / (c * a) * ((⌊c * b / (2 * π)⌋₊ : ℝ) - ⌊c * a / (2 * π)⌋₊) := by
  have hπ := pi_pos
  have hGs0 : 0 ≤ Gs := le_trans (by positivity) (hGs 0 ⟨by norm_num, by norm_num⟩)
  have hK0 : 0 ≤ (1 + π / c) * Gs := by positivity
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, 1 ≤ a → a ≤ b → ⌊c * b / (2 * π)⌋₊ = ⌊c * a / (2 * π)⌋₊ + n →
      |regTail c g b - regTail c g a|
        ≤ (1 + π / c) * Gs / a * (b - a)
          + π * |g 1 + g (-1)| / (c * a) * ((⌊c * b / (2 * π)⌋₊ : ℝ) - ⌊c * a / (2 * π)⌋₊) by
    have hmono : ⌊c * a / (2 * π)⌋₊ ≤ ⌊c * b / (2 * π)⌋₊ :=
      Nat.floor_le_floor (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab hc.le) (by positivity))
    exact H (⌊c * b / (2 * π)⌋₊ - ⌊c * a / (2 * π)⌋₊) a b ha hab (by omega)
  have hkle : ∀ a : ℝ, 1 ≤ a → 2 * π * (⌊c * a / (2 * π)⌋₊ : ℝ) / c ≤ a := by
    intro a ha
    have h1 := Nat.floor_le (show 0 ≤ c * a / (2 * π) by have : (0 : ℝ) < a := (by linarith); positivity)
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ hc]; linarith
  intro n
  induction n with
  | zero =>
    intro a b ha hab hn
    simp only [add_zero] at hn
    have h := abs_poissonPiece_sub_le hg hc hGs ha (hkle a ha) hab
    unfold regTail
    rw [hn, sub_self, mul_zero, add_zero]
    exact h
  | succ n ih =>
    intro a b ha hab hn
    have ha0 : 0 < a := by linarith
    set ka := ⌊c * a / (2 * π)⌋₊ with hka
    set a' := 2 * π * ((ka + 1 : ℕ) : ℝ) / c with ha'
    have hka' : ⌊c * a' / (2 * π)⌋₊ = ka + 1 := by
      have : c * a' / (2 * π) = ((ka + 1 : ℕ) : ℝ) := by rw [ha']; field_simp
      rw [this, Nat.floor_natCast]
    have haa' : a < a' := by
      have h1 := Nat.lt_floor_add_one (c * a / (2 * π))
      rw [div_lt_iff₀ (by positivity)] at h1
      rw [ha', lt_div_iff₀ hc]; push_cast; linarith
    have ha'0 : 0 < a' := ha0.trans haa'
    have hkb : (⌊c * b / (2 * π)⌋₊ : ℝ) = ka + 1 + n := by rw [hn]; push_cast; ring
    have ha'b : a' ≤ b := by
      have h1 := Nat.floor_le (show 0 ≤ c * b / (2 * π) by have : (0 : ℝ) < b := (by linarith); positivity)
      rw [hkb, le_div_iff₀ (by positivity)] at h1
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [ha', div_le_iff₀ hc]; push_cast; nlinarith
    have ih' := ih a' b (by linarith) ha'b (by rw [hka']; omega)
    rw [hka', hkb] at ih'
    have hjump := poissonPiece_jump (g := g) hc (k := ka + 1) (by omega)
    rw [show ka + 1 - 1 = ka by omega] at hjump
    have hra' : regTail c g a' = poissonPiece c g (ka + 1) a' := by unfold regTail; rw [hka']
    have hra : regTail c g a = poissonPiece c g ka a := rfl
    have hsm := abs_poissonPiece_sub_le hg hc hGs (k := ka) ha (hkle a ha) haa'.le
    set A := g 1 + g (-1) with hA
    have hJ : |poissonPiece c g (ka + 1) a' - poissonPiece c g ka a'| = π * |A| / (c * a') := by
      rw [hjump, abs_div, abs_mul, abs_of_pos hπ, abs_of_pos (by positivity : 0 < c * a')]
    have hsplit : regTail c g b - regTail c g a = (regTail c g b - regTail c g a')
        + (poissonPiece c g (ka + 1) a' - poissonPiece c g ka a')
        + (poissonPiece c g ka a' - poissonPiece c g ka a) := by
      rw [hra', hra]; ring
    have hKa : (1 + π / c) * Gs / a' ≤ (1 + π / c) * Gs / a := div_le_div_of_nonneg_left hK0 ha0 haa'.le
    have hJa : π * |A| / (c * a') ≤ π * |A| / (c * a) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left haa'.le hc.le)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hJ0 : 0 ≤ π * |A| / (c * a') := by positivity
    have e1 : ((ka : ℝ) + 1 + n - ((ka + 1 : ℕ) : ℝ)) = n := by push_cast; ring
    rw [e1] at ih'
    rw [hkb, hsplit]
    calc |(regTail c g b - regTail c g a') + (poissonPiece c g (ka + 1) a' - poissonPiece c g ka a')
          + (poissonPiece c g ka a' - poissonPiece c g ka a)|
        ≤ |regTail c g b - regTail c g a'| + |poissonPiece c g (ka + 1) a' - poissonPiece c g ka a'|
          + |poissonPiece c g ka a' - poissonPiece c g ka a| := abs_add_three _ _ _
      _ ≤ ((1 + π / c) * Gs / a' * (b - a') + π * |A| / (c * a') * n) + π * |A| / (c * a')
          + (1 + π / c) * Gs / a * (a' - a) := by rw [hJ]; linarith
      _ ≤ ((1 + π / c) * Gs / a * (b - a') + π * |A| / (c * a) * n) + π * |A| / (c * a)
          + (1 + π / c) * Gs / a * (a' - a) := by
          gcongr
      _ = (1 + π / c) * Gs / a * (b - a) + π * |A| / (c * a) * ((ka : ℝ) + 1 + n - ka) := by ring

/-! ### Pointwise bounds on the log scale -/

/-- `|f_∞(s)| ≤ B_G e^{−s/2}`. -/
theorem abs_logScale_fullTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (s : ℝ) :
    |logScale (fullTail (psi c g)) s|
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) * exp (-(s / 2)) := by
  unfold logScale
  rw [abs_mul, abs_of_pos (exp_pos _)]
  calc |fullTail (psi c g) (exp s)| * exp (s / 2)
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / exp s * exp (s / 2) :=
        mul_le_mul_of_nonneg_right (abs_fullTail_le hg hg₁ hg₂c hc (exp_pos s)) (exp_pos _).le
    _ = _ := by
        rw [div_mul_eq_mul_div, div_eq_iff (exp_pos _).ne', mul_assoc, ← exp_add]; ring_nf

/-- `|f_X(s)| ≤ B_G e^{−s/2}`. -/
theorem abs_logScale_posTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (X s : ℝ) :
    |logScale (posTail (psi c g) X) s|
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) * exp (-(s / 2)) := by
  unfold logScale
  rw [abs_mul, abs_of_pos (exp_pos _)]
  calc |posTail (psi c g) X (exp s)| * exp (s / 2)
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / exp s * exp (s / 2) :=
        mul_le_mul_of_nonneg_right (abs_posTail_le hg hg₁ hg₂c hc X (exp_pos s)) (exp_pos _).le
    _ = _ := by
        rw [div_mul_eq_mul_div, div_eq_iff (exp_pos _).ne', mul_assoc, ← exp_add]; ring_nf

/-- `f_∞` vanishes on `(−∞, 0]`. -/
theorem logScale_fullTail_of_nonpos (Φ : ℝ → ℝ) {s : ℝ} (hs : s ≤ 0) : logScale (fullTail Φ) s = 0 := by
  unfold logScale fullTail
  rw [if_neg (not_lt.mpr (exp_le_one_iff.mpr hs)), zero_mul]

/-- `f_X` vanishes on `(−∞, 0]`. -/
theorem logScale_posTail_of_nonpos (Φ : ℝ → ℝ) (X : ℝ) {s : ℝ} (hs : s ≤ 0) : logScale (posTail Φ X) s = 0 := by
  unfold logScale
  rw [posTail_zero _ _ (exp_le_one_iff.mpr hs), zero_mul]

/-- `e^h − 1 ≤ 2h` for `0 ≤ h ≤ 1`. -/
theorem exp_sub_one_le_two_mul {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) : exp h - 1 ≤ 2 * h := by
  have := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := h) (by rw [abs_of_nonneg hh]; exact hh1))
  nlinarith [this.2]

/-- `e^{h/2} − 1 ≤ h` for `0 ≤ h ≤ 1`. -/
theorem exp_half_sub_one_le {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) : exp (h / 2) - 1 ≤ h := by
  have := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := h / 2) (by rw [abs_of_nonneg (by linarith)]; linarith))
  nlinarith [this.2]

/-- **The translation difference of a monotone function** over a unit interval:
`∫_{a−1}^{a} (u(s + h) − u(s)) ≤ h u(a + 1)` for `u ≥ 0` monotone and `0 ≤ h ≤ 1`. -/
theorem integral_shift_sub_le {u : ℝ → ℝ} (hu : Monotone u) (hu0 : ∀ s, 0 ≤ u s) (a : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1) : ∫ s in (a - 1)..a, (u (s + h) - u s) ≤ h * u (a + 1) := by
  have i : ∀ x y : ℝ, IntervalIntegrable u volume x y := fun x y => hu.intervalIntegrable
  have hu' : Monotone fun s => u (s + h) := fun s t hst => hu (by linarith)
  rw [intervalIntegral.integral_sub hu'.intervalIntegrable (i _ _), intervalIntegral.integral_comp_add_right,
    ← intervalIntegral.integral_add_adjacent_intervals (i (a - 1 + h) a) (i a (a + h)),
    ← intervalIntegral.integral_add_adjacent_intervals (i (a - 1) (a - 1 + h)) (i (a - 1 + h) a)]
  have h1 : ∫ s in a..(a + h), u s ≤ ∫ s in a..(a + h), u (a + 1) :=
    intervalIntegral.integral_mono_on (by linarith) (i _ _) intervalIntegrable_const
      fun s hs => hu (by linarith [hs.2])
  have h2 : 0 ≤ ∫ s in (a - 1)..(a - 1 + h), u s := intervalIntegral.integral_nonneg (by linarith) fun s _ => hu0 s
  rw [intervalIntegral.integral_const, smul_eq_mul, show a + h - a = h by ring] at h1
  linarith

/-! ### The block modulus of `f_∞` -/

/-- **The block modulus of `f_∞`**: on `[L − 1, L)`, `∫|f_∞(s) − f_∞(s + h)| ≤ h V_L` with
`V_L = e^{(L+1)/2}(e(1 + π/c) G_s + |A|(e²/2 + πe/c)) + e B_G`. -/
theorem modulus_logScale_fullTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {Gs : ℝ} (hGs : ∀ s ∈ Icc (-1 : ℝ) 1, |g s| + |g₁ s| ≤ Gs) (L : ℕ) {h : ℝ}
    (hh : h ∈ Ioc (0 : ℝ) 1) :
    ∫ s in Ico ((L : ℝ) - 1) L, |logScale (fullTail (psi c g)) s - logScale (fullTail (psi c g)) (s + h)|
      ≤ h * (Real.exp (((L : ℝ) + 1) / 2) * (Real.exp 1 * (1 + π / c) * Gs
          + |g 1 + g (-1)| * (Real.exp 2 / 2 + π * Real.exp 1 / c))
        + Real.exp 1 * BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) := by
  obtain ⟨hh0, hh1⟩ := hh
  have hπ := pi_pos
  set A := g 1 + g (-1) with hA
  set B := BG c A (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hBd
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  have hGs0 : 0 ≤ Gs := le_trans (by positivity) (hGs 0 ⟨by norm_num, by norm_num⟩)
  set K := (1 + π / c) * Gs with hK
  have hK0 : 0 ≤ K := by positivity
  set f := logScale (fullTail (psi c g)) with hf
  set u : ℝ → ℝ := fun s => (⌊c * exp s / (2 * π)⌋₊ : ℝ) with hu
  have humono : Monotone u := fun s t hst => Nat.cast_le.mpr (Nat.floor_le_floor
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hst) hc.le) (by positivity)))
  have hu0 : ∀ s, 0 ≤ u s := fun s => Nat.cast_nonneg _
  have hdu : ∀ s, 0 ≤ u (s + h) - u s := fun s => sub_nonneg.mpr (humono (by linarith))
  set E := exp (((L : ℝ) + 1) / 2) with hE
  set J := π * |A| * exp (1 - L) / c with hJ
  have hJ0 : 0 ≤ J := by positivity
  set C0 := E * (K * (2 * h)) + B * h with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set Φ : ℝ → ℝ := fun s => (Ioc (-h) 0).indicator (fun _ => B) s + C0 + E * J * (u (s + h) - u s) with hΦ
  have hΦ0 : ∀ s, C0 + E * J * (u (s + h) - u s) ≤ Φ s := fun s => by
    have : 0 ≤ (Ioc (-h) 0).indicator (fun _ => B) s := indicator_nonneg (fun _ _ => hB) s
    simp only [hΦ]; linarith
  have hΦ1 : ∀ s, 0 ≤ C0 + E * J * (u (s + h) - u s) := fun s => by have := hdu s; positivity
  -- the lattice points `2πk/c`, on the log scale
  set S : Set ℝ := range (fun k : ℕ => log (2 * π * k / c)) with hS
  have hSc : S.Countable := countable_range _
  have hgood : ∀ s, s ∉ S → 0 < s → fullTail (psi c g) (exp s) = regTail c g (exp s) := by
    intro s hs hs0
    refine fullTail_eq_regTail hg hg₁ hg₂c hc (one_lt_exp_iff.mpr hs0) fun k hk => hs ⟨k, ?_⟩
    have : 2 * π * k / c = exp s := by rw [← hk]; field_simp
    simp only [this, log_exp]
  have hae : ∀ᵐ s ∂(volume.restrict (Ico ((L : ℝ) - 1) L)), s ∉ S ∧ s + h ∉ S := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hSc.ae_notMem volume, (hSc.image fun x => x - h).ae_notMem volume] with s hs1 hs2
    exact ⟨hs1, fun hm => hs2 ⟨s + h, hm, by ring⟩⟩
  have hpt : ∀ᵐ s ∂(volume.restrict (Ico ((L : ℝ) - 1) L)), |f s - f (s + h)| ≤ Φ s := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ico] with s hs hsI
    obtain ⟨hs1, hs2⟩ := hs
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [hf, logScale_fullTail_of_nonpos _ hs0, zero_sub, abs_neg]
      rcases le_or_gt (s + h) 0 with hsh | hsh
      · rw [logScale_fullTail_of_nonpos _ hsh, abs_zero]
        exact (hΦ1 s).trans (hΦ0 s)
      · have hmem : s ∈ Ioc (-h) 0 := ⟨by linarith, hs0⟩
        have h1 := abs_logScale_fullTail_le hg hg₁ hg₂c hc (s + h)
        have h2 : exp (-((s + h) / 2)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
        have h3 := hΦ1 s
        simp only [hΦ, indicator_of_mem hmem]
        calc |logScale (fullTail (psi c g)) (s + h)| ≤ B * exp (-((s + h) / 2)) := h1
          _ ≤ B * 1 := mul_le_mul_of_nonneg_left h2 hB
          _ ≤ B + C0 + E * J * (u (s + h) - u s) := by linarith
    · have ha1 : 1 < exp s := one_lt_exp_iff.mpr hs0
      have hab : exp s ≤ exp (s + h) := exp_le_exp.mpr (by linarith)
      have hFa := hgood s hs1 hs0
      have hFb := hgood (s + h) hs2 (by linarith)
      have hfs : f s = fullTail (psi c g) (exp s) * exp (s / 2) := rfl
      have hfsh : f (s + h) = regTail c g (exp (s + h)) * exp ((s + h) / 2) := by
        show fullTail (psi c g) (exp (s + h)) * exp ((s + h) / 2) = _
        rw [hFb]
      have hdiff : f s - f (s + h) = (regTail c g (exp s) - regTail c g (exp (s + h))) * exp ((s + h) / 2)
          + fullTail (psi c g) (exp s) * (exp (s / 2) - exp ((s + h) / 2)) := by
        rw [hfs, hfsh, ← hFa]; ring
      have hvar := abs_regTail_sub_le hg hc hGs ha1.le hab
      have hKpart : K / exp s * (exp (s + h) - exp s) ≤ K * (2 * h) := by
        have e : K / exp s * (exp (s + h) - exp s) = K * (exp h - 1) := by
          rw [exp_add]; field_simp
        rw [e]; exact mul_le_mul_of_nonneg_left (exp_sub_one_le_two_mul hh0.le hh1) hK0
      have hJpart : π * |A| / (c * exp s) ≤ J := by
        have h1 : exp (-s) ≤ exp (1 - L) := exp_le_exp.mpr (by linarith [hsI.1])
        rw [show π * |A| / (c * exp s) = π * |A| * exp (-s) / c by rw [exp_neg]; field_simp]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hc.le
      have hEb : exp ((s + h) / 2) ≤ E := exp_le_exp.mpr (by linarith [hsI.2])
      have hFbd : |fullTail (psi c g) (exp s)| ≤ B / exp s := abs_fullTail_le hg hg₁ hg₂c hc (exp_pos s)
      have hh2 : 0 ≤ exp (h / 2) - 1 := sub_nonneg.mpr (one_le_exp (by linarith))
      have hsecond : |fullTail (psi c g) (exp s) * (exp (s / 2) - exp ((s + h) / 2))| ≤ B * h := by
        have e : exp ((s + h) / 2) - exp (s / 2) = exp (s / 2) * (exp (h / 2) - 1) := by
          rw [show (s + h) / 2 = s / 2 + h / 2 by ring, exp_add]; ring
        rw [abs_mul, abs_sub_comm, e, abs_of_nonneg (mul_nonneg (exp_pos _).le hh2)]
        calc |fullTail (psi c g) (exp s)| * (exp (s / 2) * (exp (h / 2) - 1))
            ≤ B / exp s * (exp (s / 2) * (exp (h / 2) - 1)) :=
              mul_le_mul_of_nonneg_right hFbd (mul_nonneg (exp_pos _).le hh2)
          _ = B * exp (-(s / 2)) * (exp (h / 2) - 1) := by
              rw [← exp_half_sq s, exp_neg]; field_simp
          _ ≤ B * 1 * h := mul_le_mul (mul_le_mul_of_nonneg_left (exp_le_one_iff.mpr (by linarith)) hB)
              (exp_half_sub_one_le hh0.le hh1) hh2 (by positivity)
          _ = B * h := by ring
      have hR : |regTail c g (exp s) - regTail c g (exp (s + h))| ≤ K * (2 * h) + J * (u (s + h) - u s) := by
        rw [abs_sub_comm]
        refine hvar.trans (add_le_add hKpart (mul_le_mul_of_nonneg_right hJpart (hdu s)))
      calc |f s - f (s + h)|
          ≤ |regTail c g (exp s) - regTail c g (exp (s + h))| * exp ((s + h) / 2) + B * h := by
            rw [hdiff]
            refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) hsecond)
            rw [abs_mul, abs_of_pos (exp_pos _)]
        _ ≤ (K * (2 * h) + J * (u (s + h) - u s)) * E + B * h := by
            gcongr
            exact le_trans (abs_nonneg _) hR
        _ = C0 + E * J * (u (s + h) - u s) := by rw [hC0]; ring
        _ ≤ Φ s := hΦ0 s
  -- integrate the majorant
  have hind : Integrable ((Ioc (-h) 0).indicator (fun _ : ℝ => B)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const measure_Ioc_lt_top.ne)
  have hui : IntegrableOn (fun s => u (s + h) - u s) (Ico ((L : ℝ) - 1) L) := by
    have hu' : Monotone fun s => u (s + h) := fun s t hst => humono (by linarith)
    have := (hu'.intervalIntegrable (μ := volume) (a := (L : ℝ) - 1) (b := L)).sub humono.intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at this
    exact ((integrableOn_Icc_iff_integrableOn_Ioc).mpr this).mono_set Ico_subset_Icc_self
  have hi1 : IntegrableOn (fun s => (Ioc (-h) 0).indicator (fun _ : ℝ => B) s + C0) (Ico ((L : ℝ) - 1) L) :=
    hind.integrableOn.add (integrableOn_const measure_Ico_lt_top.ne)
  have hi2 : IntegrableOn (fun s => E * J * (u (s + h) - u s)) (Ico ((L : ℝ) - 1) L) := hui.const_mul _
  have hΦi : IntegrableOn Φ (Ico ((L : ℝ) - 1) L) := hi1.add hi2
  have hJu : J * u ((L : ℝ) + 1) ≤ |A| * exp 2 / 2 := by
    have h1 : u ((L : ℝ) + 1) ≤ c * exp ((L : ℝ) + 1) / (2 * π) := Nat.floor_le (by positivity)
    calc J * u ((L : ℝ) + 1) ≤ J * (c * exp ((L : ℝ) + 1) / (2 * π)) := mul_le_mul_of_nonneg_left h1 hJ0
      _ = |A| * (exp (1 - L) * exp ((L : ℝ) + 1)) / 2 := by rw [hJ]; field_simp
      _ = |A| * exp 2 / 2 := by rw [← exp_add]; ring_nf
  have he2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  calc ∫ s in Ico ((L : ℝ) - 1) L, |f s - f (s + h)| ≤ ∫ s in Ico ((L : ℝ) - 1) L, Φ s :=
        integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hΦi hpt
    _ = (∫ s in Ico ((L : ℝ) - 1) L, (Ioc (-h) 0).indicator (fun _ : ℝ => B) s)
          + (∫ s in Ico ((L : ℝ) - 1) L, C0) + ∫ s in Ico ((L : ℝ) - 1) L, E * J * (u (s + h) - u s) := by
        rw [integral_add hi1 hi2, integral_add hind.integrableOn (integrableOn_const measure_Ico_lt_top.ne)]
    _ ≤ B * h + C0 + E * J * (h * u ((L : ℝ) + 1)) := by
        gcongr ?_ + ?_ + ?_
        · calc ∫ s in Ico ((L : ℝ) - 1) L, (Ioc (-h) 0).indicator (fun _ : ℝ => B) s
              ≤ ∫ s, (Ioc (-h) 0).indicator (fun _ : ℝ => B) s :=
                setIntegral_le_integral hind (Eventually.of_forall fun s => indicator_nonneg (fun _ _ => hB) s)
            _ = B * h := by
                rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc_of_le (by linarith),
                  smul_eq_mul]; ring
        · rw [setIntegral_const, Real.volume_real_Ico_of_le (by linarith), smul_eq_mul]; simp
        · rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
            ← intervalIntegral.integral_of_le (by linarith)]
          exact integral_shift_sub_le humono hu0 (L : ℝ) hh0.le hh1
    _ ≤ h * (E * (Real.exp 1 * (1 + π / c) * Gs + |A| * (Real.exp 2 / 2 + π * Real.exp 1 / c))
          + Real.exp 1 * B) := by
        have hE0 : 0 < E := exp_pos _
        have hk1 : K * 2 ≤ Real.exp 1 * (1 + π / c) * Gs := by
          rw [hK, show Real.exp 1 * (1 + π / c) * Gs = (1 + π / c) * Gs * Real.exp 1 by ring]
          exact mul_le_mul_of_nonneg_left he2 hK0
        have hk2 : J * u ((L : ℝ) + 1) ≤ |A| * (Real.exp 2 / 2 + π * Real.exp 1 / c) := by
          have : 0 ≤ |A| * (π * Real.exp 1 / c) := by positivity
          nlinarith
        have hk3 : 2 * B ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_right he2 hB
        rw [hC0]
        have := mul_le_mul_of_nonneg_left (add_le_add hk1 hk2) (mul_nonneg hE0.le hh0.le)
        nlinarith

/-! ### The modulus of `f_X` -/

/-- `|ψ(ξ)| ≤ B_G/ξ` for `ξ ≥ 1`. -/
theorem abs_psi_le_BG (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |psi c g ξ| ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / ξ := by
  have h := abs_partial_le hg hg₁ hg₂c hc hξ 1
  simpa using h

/-- `|ψ'(ξ)| ≤ c ∫|g|`. -/
theorem exists_hasDerivAt_psi (hgc : ContinuousOn g (uIcc (-1) 1)) (hc : 0 < c) (ξ : ℝ) :
    ∃ d, HasDerivAt (psi c g) d ξ ∧ |d| ≤ c * ∫ s in (-1 : ℝ)..1, |g s| := by
  refine ⟨_, Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (C := |c|) (k := fun ξ s => Real.cos (c * ξ * s))
    (k' := fun ξ s => -(c * s * Real.sin (c * ξ * s))) hgc (fun s => by fun_prop) (fun ξ => by fun_prop)
    (fun ξ => by fun_prop)
    (fun ξ s => by
      have h := (((hasDerivAt_id ξ).const_mul c).mul_const s).cos
      exact h.congr_deriv (by simp only [id, mul_one]; ring))
    (fun ξ s hs => by
      rw [abs_neg, abs_mul, abs_mul]
      have := abs_sin_le_one (c * ξ * s)
      calc |c| * |s| * |Real.sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) this (abs_nonneg _) (by positivity)
        _ = |c| := by ring) ξ, ?_⟩
  unfold Cvs.Prolate.SlepianCommutingRelation.kint
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s hs => ?_
  · exact ((hgc.mul (by fun_prop : Continuous fun s => -(c * s * Real.sin (c * ξ * s))).continuousOn).abs
      ).intervalIntegrable
  · exact (hgc.abs.intervalIntegrable).const_mul c
  · have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
    rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos hc]
    have := abs_sin_le_one (c * ξ * s)
    have h0 : 0 ≤ |g s| := abs_nonneg _
    calc |g s| * (c * |s| * |Real.sin (c * ξ * s)|) ≤ |g s| * (c * 1 * 1) := by gcongr
      _ = c * |g s| := by ring

/-- **The `L¹` modulus of `f_X`**: each of the `⌊X⌋` cut pieces has sup `≤ B_G` and Lipschitz constant
`≤ c(∫|g|)X^{3/2} + B_G√X/2` on an interval of length `≤ log X`. -/
theorem modulus_logScale_posTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) {v : ℝ} (hv : 0 ≤ v) :
    ∫ s, |logScale (posTail (psi c g) X) s - logScale (posTail (psi c g) X) (s + v)|
      ≤ X * ((c * (∫ s in (-1 : ℝ)..1, |g s|) * X ^ ((3 : ℝ) / 2)
          + BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) * √X / 2) * Real.log X
        + 2 * BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) * v := by
  have hX0 : 0 < X := by linarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  set G1 := ∫ s in (-1 : ℝ)..1, |g s| with hG1d
  have hG1 : 0 ≤ G1 := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hBd
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  have hsX : 1 ≤ √X := Real.one_le_sqrt.mpr hX
  have hX32 : X ^ ((3 : ℝ) / 2) = X * √X := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add hX0, rpow_one, sqrt_eq_rpow]
  set Lh := c * G1 * X ^ ((3 : ℝ) / 2) + B * √X / 2 with hLhd
  have hLh : 0 ≤ Lh := by rw [hLhd, hX32]; positivity
  have hψc : Continuous (psi c g) := (contDiff_psi hgc c).continuous
  choose dψ hdψ using exists_hasDerivAt_psi hgc hc
  have hpiece : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊,
      Integrable (fun s => indicator (Ioc 0 (Real.log (X / m))) (fun s => psi c g (m * exp s) * exp (s / 2)) s
        - indicator (Ioc 0 (Real.log (X / m))) (fun s => psi c g (m * exp s) * exp (s / 2)) (s + v)) volume
      ∧ ∫ s, |indicator (Ioc 0 (Real.log (X / m))) (fun s => psi c g (m * exp s) * exp (s / 2)) s
          - indicator (Ioc 0 (Real.log (X / m))) (fun s => psi c g (m * exp s) * exp (s / 2)) (s + v)|
        ≤ (Lh * Real.log X + 2 * B) * v := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmX : (m : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (Finset.mem_Icc.mp hm).2
    have hXm : 0 < X / m := div_pos hX0 hm0
    have hbm : 0 ≤ Real.log (X / m) := Real.log_nonneg ((one_le_div hm0).mpr hmX)
    have hbX : Real.log (X / m) ≤ Real.log X := Real.log_le_log hXm (div_le_self hX0.le hm1)
    have hmem : ∀ s ∈ Icc 0 (Real.log (X / m)), 1 ≤ (m : ℝ) * exp s ∧ (m : ℝ) * exp s ≤ X
        ∧ exp (s / 2) ≤ √X ∧ exp (s / 2) ≤ (m : ℝ) * exp s := by
      intro s hs
      have he1 : 1 ≤ exp s := one_le_exp hs.1
      have he2 : exp s ≤ X / m := by rw [← exp_log hXm]; exact exp_le_exp.mpr hs.2
      have he3 : (m : ℝ) * exp s ≤ X := by rw [le_div_iff₀ hm0] at he2; linarith
      have hh : exp (s / 2) ≤ exp s := exp_le_exp.mpr (by linarith [hs.1])
      refine ⟨by nlinarith, he3, ?_, by nlinarith⟩
      rw [Real.le_sqrt (exp_pos _).le hX0.le, sq, exp_half_sq]
      nlinarith
    have hbd : ∀ s ∈ Icc 0 (Real.log (X / m)), |psi c g (m * exp s) * exp (s / 2)| ≤ B := by
      intro s hs
      obtain ⟨h1, -, -, h4⟩ := hmem s hs
      rw [abs_mul, abs_of_pos (exp_pos _)]
      calc |psi c g (m * exp s)| * exp (s / 2) ≤ B / (m * exp s) * exp (s / 2) :=
            mul_le_mul_of_nonneg_right (abs_psi_le_BG hg hg₁ hg₂c hc h1) (exp_pos _).le
        _ ≤ B / (m * exp s) * (m * exp s) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = B := by field_simp
    have hder : ∀ s, HasDerivAt (fun s => psi c g (m * exp s) * exp (s / 2))
        (dψ (m * exp s) * (m * exp s) * exp (s / 2) + psi c g (m * exp s) * (exp (s / 2) * (1 / 2))) s := by
      intro s
      have h1 : HasDerivAt (fun s => (m : ℝ) * exp s) (m * exp s) s := (hasDerivAt_exp s).const_mul _
      have h2 : HasDerivAt (fun s => exp (s / 2)) (exp (s / 2) * (1 / 2)) s :=
        ((hasDerivAt_id' s).div_const 2).exp
      exact ((hdψ (m * exp s)).1.comp s h1).mul h2
    have hderb : ∀ s ∈ Icc 0 (Real.log (X / m)),
        ‖dψ (m * exp s) * (m * exp s) * exp (s / 2) + psi c g (m * exp s) * (exp (s / 2) * (1 / 2))‖ ≤ Lh := by
      intro s hs
      obtain ⟨h1, h2, h3, h4⟩ := hmem s hs
      have hd := (hdψ (m * exp s)).2
      have hp := abs_psi_le_BG hg hg₁ hg₂c hc h1
      rw [Real.norm_eq_abs]
      have t1 : |dψ (m * exp s) * (m * exp s) * exp (s / 2)| ≤ c * G1 * X ^ ((3 : ℝ) / 2) := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < m * exp s), abs_of_pos (exp_pos _), hX32]
        calc |dψ (m * exp s)| * (m * exp s) * exp (s / 2) ≤ (c * G1) * X * √X := by gcongr
          _ = c * G1 * (X * √X) := by ring
      have t2 : |psi c g (m * exp s) * (exp (s / 2) * (1 / 2))| ≤ B * √X / 2 := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < exp (s / 2) * (1 / 2))]
        calc |psi c g (m * exp s)| * (exp (s / 2) * (1 / 2)) ≤ B / (m * exp s) * ((m * exp s) * (1 / 2)) := by
              gcongr
          _ = B * 1 / 2 := by field_simp
          _ ≤ B * √X / 2 := by gcongr
      exact (abs_add_le _ _).trans (add_le_add t1 t2)
    have hlip : ∀ s ∈ Ioc 0 (Real.log (X / m)), ∀ t ∈ Ioc 0 (Real.log (X / m)),
        |psi c g (m * exp s) * exp (s / 2) - psi c g (m * exp t) * exp (t / 2)| ≤ Lh * |s - t| := by
      intro s hs t ht
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x _ => (hder x).hasDerivWithinAt) hderb (convex_Icc 0 (Real.log (X / m)))
        (Ioc_subset_Icc_self ht) (Ioc_subset_Icc_self hs)
      simpa only [Real.norm_eq_abs] using h
    have hcont : Continuous fun s => psi c g (m * exp s) * exp (s / 2) := by fun_prop
    have hint : IntegrableOn (fun s => psi c g (m * exp s) * exp (s / 2)) (Ioc 0 (Real.log (X / m))) volume :=
      (hcont.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    obtain ⟨h1, h2⟩ := Cvs.Upstream.LevyConditionL1Modulus.modulus_cut hbm hv hLh hB hint
      (fun s hs => hbd s (Ioc_subset_Icc_self hs)) hlip
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ hv)⟩
    gcongr
  rw [Cvs.L2a.PositionTailAdmissible.logScale_posTail (psi c g) hX0]
  set ind : ℕ → ℝ → ℝ := fun m => indicator (Ioc 0 (Real.log (X / m)))
    (fun s => psi c g (m * exp s) * exp (s / 2)) with hind
  have hint : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, Integrable (fun s => ind m s - ind m (s + v)) volume :=
    fun m hm => (hpiece m hm).1
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hK0 : 0 ≤ (Lh * Real.log X + 2 * B) * v := by
    have := Real.log_nonneg hX; positivity
  calc ∫ s, |∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ind m s - ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ind m (s + v)|
      = ∫ s, |∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (ind m s - ind m (s + v))| := by
        congr 1; funext s; rw [Finset.sum_sub_distrib]
    _ ≤ ∫ s, ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, |ind m s - ind m (s + v)| :=
        integral_mono (integrable_finsetSum _ hint).abs (integrable_finsetSum _ fun m hm => (hint m hm).abs)
          fun s => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∫ s, |ind m s - ind m (s + v)| :=
        integral_finsetSum _ fun m hm => (hint m hm).abs
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (Lh * Real.log X + 2 * B) * v := Finset.sum_le_sum fun m hm => (hpiece m hm).2
    _ = (⌊X⌋₊ : ℝ) * ((Lh * Real.log X + 2 * B) * v) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    _ ≤ X * ((Lh * Real.log X + 2 * B) * v) := mul_le_mul_of_nonneg_right hfl hK0
    _ = _ := by rw [hLhd]; ring

/-! ### Finite Lévy energy of `f_∞` -/

/-- **The block sum** with `ā_L = ε e^{−L/2}` and `H_L V_L ≤ 2εY` is summable and at most
`ε((1 + |log Y|) Σ e^{−L/2} + ½ Σ L e^{−L/2})`. -/
theorem block_sum_le {ε Y : ℝ} (hε : 0 < ε) (hY : 0 < Y) {H V : ℕ → ℝ} (hHV0 : ∀ L, 0 ≤ H L * V L)
    (hHV : ∀ L, H L * V L ≤ 2 * ε * Y) :
    Summable (fun L : ℕ => ε * exp (-((L : ℝ) / 2))
        * max 1 (Real.log (H L * V L / (2 * (ε * exp (-((L : ℝ) / 2)))))))
      ∧ ∑' L : ℕ, ε * exp (-((L : ℝ) / 2)) * max 1 (Real.log (H L * V L / (2 * (ε * exp (-((L : ℝ) / 2))))))
        ≤ ε * ((1 + |Real.log Y|) * ∑' L : ℕ, exp (-((L : ℝ) / 2))
          + 1 / 2 * ∑' L : ℕ, (L : ℝ) * exp (-((L : ℝ) / 2))) := by
  have hs0 : Summable fun L : ℕ => exp (-((L : ℝ) / 2)) := by
    refine (Real.summable_pow_mul_exp_neg_nat_mul 0 (r := 1 / 2) (by norm_num)).congr fun L => ?_
    rw [pow_zero, one_mul]; ring_nf
  have hs1 : Summable fun L : ℕ => (L : ℝ) * exp (-((L : ℝ) / 2)) := by
    refine (Real.summable_pow_mul_exp_neg_nat_mul 1 (r := 1 / 2) (by norm_num)).congr fun L => ?_
    rw [pow_one]; ring_nf
  set T := fun L : ℕ => ε * exp (-((L : ℝ) / 2))
    * max 1 (Real.log (H L * V L / (2 * (ε * exp (-((L : ℝ) / 2)))))) with hT
  set M := fun L : ℕ => ε * (1 + |Real.log Y|) * exp (-((L : ℝ) / 2))
    + ε / 2 * ((L : ℝ) * exp (-((L : ℝ) / 2))) with hMd
  have hM : Summable M := (hs0.mul_left _).add (hs1.mul_left _)
  have hpt : ∀ L, 0 ≤ T L ∧ T L ≤ M L := by
    intro L
    have he : 0 < exp (-((L : ℝ) / 2)) := exp_pos _
    have ha : 0 < ε * exp (-((L : ℝ) / 2)) := mul_pos hε he
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    set x := H L * V L / (2 * (ε * exp (-((L : ℝ) / 2)))) with hx
    have hx0 : 0 ≤ x := div_nonneg (hHV0 L) (by positivity)
    have hxle : x ≤ Y * exp ((L : ℝ) / 2) := by
      rw [hx, div_le_iff₀ (by positivity)]
      have e : Y * exp ((L : ℝ) / 2) * (2 * (ε * exp (-((L : ℝ) / 2)))) = 2 * ε * Y := by
        rw [show Y * exp ((L : ℝ) / 2) * (2 * (ε * exp (-((L : ℝ) / 2))))
          = 2 * ε * Y * (exp ((L : ℝ) / 2) * exp (-((L : ℝ) / 2))) by ring, ← exp_add, add_neg_cancel,
          exp_zero, mul_one]
      rw [e]; exact hHV L
    have hlog : max 1 (Real.log x) ≤ 1 + |Real.log Y| + (L : ℝ) / 2 := by
      refine max_le (by linarith [abs_nonneg (Real.log Y)]) ?_
      rcases hx0.eq_or_lt with h0 | h0
      · rw [← h0, Real.log_zero]; linarith [abs_nonneg (Real.log Y)]
      · calc Real.log x ≤ Real.log (Y * exp ((L : ℝ) / 2)) := Real.log_le_log h0 hxle
          _ = Real.log Y + (L : ℝ) / 2 := by rw [Real.log_mul hY.ne' (exp_pos _).ne', Real.log_exp]
          _ ≤ 1 + |Real.log Y| + (L : ℝ) / 2 := by linarith [le_abs_self (Real.log Y)]
    refine ⟨mul_nonneg ha.le (le_trans zero_le_one (le_max_left _ _)), ?_⟩
    calc T L = ε * exp (-((L : ℝ) / 2)) * max 1 (Real.log x) := rfl
      _ ≤ ε * exp (-((L : ℝ) / 2)) * (1 + |Real.log Y| + (L : ℝ) / 2) := mul_le_mul_of_nonneg_left hlog ha.le
      _ = M L := by simp only [hMd]; ring
  have hTs : Summable T := Summable.of_nonneg_of_le (fun L => (hpt L).1) (fun L => (hpt L).2) hM
  refine ⟨hTs, ?_⟩
  calc ∑' L, T L ≤ ∑' L, M L := Summable.tsum_le_tsum (fun L => (hpt L).2) hTs hM
    _ = ε * ((1 + |Real.log Y|) * ∑' L : ℕ, exp (-((L : ℝ) / 2))
          + 1 / 2 * ∑' L : ℕ, (L : ℝ) * exp (-((L : ℝ) / 2))) := by
        rw [Summable.tsum_add (hs0.mul_left _) (hs1.mul_left _), tsum_mul_left, tsum_mul_left]; ring

/-- A constant `G_s ≥ |g| + |g₁|` on `[−1, 1]`, by compactness. -/
theorem exists_Gs (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) :
    ∃ Gs, ∀ s ∈ Icc (-1 : ℝ) 1, |g s| + |g₁ s| ≤ Gs := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs =>
    (hg s (by rw [hI]; exact hs)).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (Icc (-1) 1) := fun s hs =>
    (hg₁ s (by rw [hI]; exact hs)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hgc.abs.add hg₁c.abs)
  exact ⟨M, fun s hs => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM s hs)⟩

/-- **`f_∞` has finite Lévy energy**: `LevyUnitBlocks`'s block lemma with `H_L = B_G e^{(1−L)/2}`, `V_L` from the block
modulus and `ā_L = (2eB_G² + 1) e^{−L/2}`. -/
theorem integrableOn_levy_fullTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale (fullTail (psi c g)))) (Ioi 0) volume := by
  obtain ⟨Gs, hGs⟩ := exists_Gs hg hg₁
  have hGs0 : 0 ≤ Gs := le_trans (by positivity) (hGs 0 ⟨by norm_num, by norm_num⟩)
  have hπ := pi_pos
  set A := g 1 + g (-1) with hA
  set B := BG c A (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hBd
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  set f := logScale (fullTail (psi c g)) with hf
  have h2 : MemLp f 2 volume := (memLp_logScale_fullTail hg hg₁ hg₂c hc).1
  have hf0 : ∀ s ≤ 0, f s = 0 := fun s hs => logScale_fullTail_of_nonpos _ hs
  set Q := Real.exp 1 * (1 + π / c) * Gs + |A| * (Real.exp 2 / 2 + π * Real.exp 1 / c) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set H : ℕ → ℝ := fun L => B * exp ((1 - (L : ℝ)) / 2) with hHd
  set V : ℕ → ℝ := fun L => Real.exp (((L : ℝ) + 1) / 2) * Q + Real.exp 1 * B with hVd
  set ε := 2 * Real.exp 1 * B ^ 2 + 1 with hεd
  have hε : 0 < ε := by positivity
  set W := B * Real.exp 1 * Q + Real.exp 1 * B ^ 2 * Real.exp (1 / 2) + 1 with hWd
  have hW : 0 < W := by positivity
  have hH : ∀ L : ℕ, ∀ s ∈ Icc ((L : ℝ) - 1) (L + 1), |f s| ≤ H L := fun L s hs =>
    (abs_logScale_fullTail_le hg hg₁ hg₂c hc s).trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [hs.1])) hB)
  have hV : ∀ L : ℕ, ∀ h ∈ Ioc (0 : ℝ) 1, ∫ s in Ico ((L : ℝ) - 1) L, |f s - f (s + h)| ≤ h * V L :=
    fun L h hh => modulus_logScale_fullTail hg hg₁ hg₂c hc hGs L hh
  have ha : ∀ L : ℕ, ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 ≤ ε * exp (-((L : ℝ) / 2)) := by
    intro L
    have hsq : ∀ s ∈ Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 ≤ B ^ 2 * exp (1 - L) := by
      intro s hs
      calc f s ^ 2 = |f s| ^ 2 := (sq_abs _).symm
        _ ≤ (B * exp ((1 - (L : ℝ)) / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hH L s hs) 2
        _ = B ^ 2 * exp (1 - L) := by rw [mul_pow, sq (exp _), ← exp_add]; ring_nf
    have hL : exp (1 - (L : ℝ)) ≤ Real.exp 1 * exp (-((L : ℝ) / 2)) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
    calc ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 ≤ ∫ s in Icc ((L : ℝ) - 1) (L + 1), B ^ 2 * exp (1 - L) :=
          setIntegral_mono_on h2.integrable_sq.integrableOn (integrableOn_const measure_Icc_lt_top.ne)
            measurableSet_Icc hsq
      _ = 2 * (B ^ 2 * exp (1 - L)) := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]; ring
      _ ≤ 2 * (B ^ 2 * (Real.exp 1 * exp (-((L : ℝ) / 2)))) := by gcongr
      _ ≤ ε * exp (-((L : ℝ) / 2)) := by
          have : 0 ≤ exp (-((L : ℝ) / 2)) := (exp_pos _).le
          rw [hεd]; nlinarith
  have hHV0 : ∀ L, 0 ≤ H L * V L := fun L => by simp only [hHd, hVd]; positivity
  have hHV : ∀ L, H L * V L ≤ 2 * ε * (W / (2 * ε)) := by
    intro L
    rw [show 2 * ε * (W / (2 * ε)) = W by field_simp]
    have hL : exp ((1 - (L : ℝ)) / 2) ≤ Real.exp (1 / 2) :=
      exp_le_exp.mpr (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
    have e : H L * V L = B * Real.exp 1 * Q + Real.exp 1 * B ^ 2 * exp ((1 - (L : ℝ)) / 2) := by
      simp only [hHd, hVd]
      rw [show B * exp ((1 - (L : ℝ)) / 2) * (Real.exp (((L : ℝ) + 1) / 2) * Q + Real.exp 1 * B)
        = B * (exp ((1 - (L : ℝ)) / 2) * Real.exp (((L : ℝ) + 1) / 2)) * Q
          + Real.exp 1 * B ^ 2 * exp ((1 - (L : ℝ)) / 2) by ring, ← exp_add]
      ring_nf
    rw [e, hWd]
    have : Real.exp 1 * B ^ 2 * exp ((1 - (L : ℝ)) / 2) ≤ Real.exp 1 * B ^ 2 * Real.exp (1 / 2) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  obtain ⟨hsum, -⟩ := block_sum_le hε (div_pos hW (by positivity)) hHV0 hHV
  exact (Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_le_block h2 hf0 (abar := fun L => ε * exp (-((L : ℝ) / 2)))
    (fun L => by positivity) hH hV ha hsum).1

/-! ### The archimedean limit -/

/-- `log X / X^{1/4} → 0`. -/
theorem tendsto_log_div_sqrt_sqrt : Tendsto (fun X : ℝ => Real.log X / √√X) atTop (𝓝 0) := by
  have ht : Tendsto (fun X : ℝ => √√X) atTop atTop := tendsto_sqrt_atTop.comp tendsto_sqrt_atTop
  have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht).const_mul 4
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  simp only [Function.comp, pow_one, one_mul, add_zero]
  rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hX.le]
  ring

/-- `√√X ≤ X` for `X ≥ 1`. -/
theorem sqrt_sqrt_le_self {X : ℝ} (hX : 1 ≤ X) : √√X ≤ X := by
  have hX0 : 0 ≤ X := by linarith
  have h1 : √X ≤ X := by
    calc √X ≤ √(X ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = X := Real.sqrt_sq hX0
  have h2 : √√X ≤ √X := by
    calc √√X ≤ √(√X ^ 2) := Real.sqrt_le_sqrt (by nlinarith [Real.one_le_sqrt.mpr hX])
      _ = √X := Real.sqrt_sq (Real.sqrt_nonneg X)
  linarith

/-- **The archimedean channel of `f_∞ − f_X` tends to `0`**: `LevyUnitBlocks`'s block lemma with `H_L = 2B_G e^{(1−L)/2}`,
`V_L` the two block moduli and `ā_L = κ X^{−1/4} e^{−L/2}`, `κ² ≥ 8eB_G² K1b`. -/
theorem tendsto_archFull_sub (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
      (logScale (fullTail (psi c g)) - logScale (posTail (psi c g) X))) atTop (𝓝 0) := by
  obtain ⟨Gs, hGs⟩ := exists_Gs hg hg₁
  have hGs0 : 0 ≤ Gs := le_trans (by positivity) (hGs 0 ⟨by norm_num, by norm_num⟩)
  have hπ := pi_pos
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  set A := g 1 + g (-1) with hA
  set C1 := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC1
  have hC10 : 0 ≤ C1 := C1_nonneg g₁ g₂
  set B := BG c A C1 with hBd
  have hB : 0 ≤ B := BG_nonneg hc _ hC10
  set G1 := ∫ s in (-1 : ℝ)..1, |g s| with hG1d
  have hG1 : 0 ≤ G1 := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  set Kb := K1b c A C1 with hKbd
  have hKb : 0 ≤ Kb := by rw [hKbd]; unfold K1b; positivity
  set Q := Real.exp 1 * (1 + π / c) * Gs + |A| * (Real.exp 2 / 2 + π * Real.exp 1 / c) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set κ := √(8 * Real.exp 1 * B ^ 2 * Kb) + 1 with hκd
  have hκ : 0 < κ := by positivity
  have hκ2 : 8 * Real.exp 1 * B ^ 2 * Kb ≤ κ ^ 2 := by
    have h0 : 0 ≤ 8 * Real.exp 1 * B ^ 2 * Kb := by positivity
    have h1 := Real.sq_sqrt h0
    have h2 := Real.sqrt_nonneg (8 * Real.exp 1 * B ^ 2 * Kb)
    rw [hκd]; nlinarith
  set W0 := 2 * B * Real.exp 1 * Q + 2 * B * Real.exp (1 / 2) * (Real.exp 1 * B + c * G1 + 5 * B / 2) + 1
    with hW0d
  have hW0 : 0 < W0 := by positivity
  set c0 := Real.log (W0 / (2 * κ)) with hc0
  set S0 := ∑' L : ℕ, exp (-((L : ℝ) / 2)) with hS0
  set S1 := ∑' L : ℕ, (L : ℝ) * exp (-((L : ℝ) / 2)) with hS1
  have hS00 : 0 ≤ S0 := tsum_nonneg fun _ => (exp_pos _).le
  set D := 2 * Cvs.WeilForm.Archimedean.LevyUnitBlocks.D2 + 6 with hDd
  have hD : 0 ≤ D := by
    have h1 : exp (-2 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
    have h2 : 0 ≤ Cvs.WeilForm.Archimedean.LevyUnitBlocks.D2 := by
      unfold Cvs.WeilForm.Archimedean.LevyUnitBlocks.D2; exact div_nonneg (by positivity) (by linarith)
    rw [hDd]; linarith
  have hbound : ∀ X : ℝ, 1 ≤ X → Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
      (logScale (fullTail (psi c g)) - logScale (posTail (psi c g) X))
        ≤ D * (Kb / √X) + 2 * (κ / √√X) * ((1 + |c0| + 5 * Real.log X) * S0 + 1 / 2 * S1) := by
    intro X hX
    have hX0 : 0 < X := by linarith
    set fi := logScale (fullTail (psi c g)) with hfi
    set fX := logScale (posTail (psi c g) X) with hfX
    have hmi := memLp_logScale_fullTail hg hg₁ hg₂c hc
    have hadm := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX ((contDiff_psi hgc c).contDiffOn (s := Icc 1 X))
    have h2 : MemLp (fi - fX) 2 volume := hmi.1.sub hadm.1
    have hf0 : ∀ s ≤ 0, (fi - fX) s = 0 := fun s hs => by
      simp only [Pi.sub_apply, hfi, hfX, logScale_fullTail_of_nonpos _ hs, logScale_posTail_of_nonpos _ _ hs,
        sub_zero]
    have hsX : 1 ≤ √X := Real.one_le_sqrt.mpr hX
    have hssX : 1 ≤ √√X := Real.one_le_sqrt.mpr hsX
    have hssX' : √√X ≤ X := sqrt_sqrt_le_self hX
    have hsXX : √X ≤ X := by
      calc √X ≤ √(X ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = X := Real.sqrt_sq hX0.le
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    have hlX : Real.log X ≤ X := (Real.log_le_sub_one_of_pos hX0).trans (by linarith)
    have hX32 : X ^ ((3 : ℝ) / 2) = X * √X := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add hX0, rpow_one, sqrt_eq_rpow]
    set Lpos := X * ((c * G1 * X ^ ((3 : ℝ) / 2) + B * √X / 2) * Real.log X + 2 * B) with hLposd
    have hLpos0 : 0 ≤ Lpos := by rw [hLposd, hX32]; positivity
    have hLpos4 : Lpos ≤ (c * G1 + 5 * B / 2) * X ^ 4 := by
      have hXX : X * √X ≤ X ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hsXX hX0.le
      have hX2 : √X ≤ X ^ 2 := hsXX.trans (by nlinarith)
      have ha1 : c * G1 * (X * √X) + B * √X / 2 ≤ (c * G1 + B / 2) * X ^ 2 := by
        have t1 := mul_le_mul_of_nonneg_left hXX (by positivity : 0 ≤ c * G1)
        have t2 := mul_le_mul_of_nonneg_left hX2 hB
        nlinarith
      have ha2 : (c * G1 * (X * √X) + B * √X / 2) * Real.log X ≤ (c * G1 + B / 2) * X ^ 2 * X :=
        mul_le_mul ha1 hlX hlogX (by positivity)
      have ha3 : 2 * B ≤ 2 * B * X ^ 3 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hX)
      rw [hLposd, hX32]
      calc X * ((c * G1 * (X * √X) + B * √X / 2) * Real.log X + 2 * B)
          ≤ X * ((c * G1 + B / 2) * X ^ 2 * X + 2 * B * X ^ 3) :=
            mul_le_mul_of_nonneg_left (add_le_add ha2 ha3) hX0.le
        _ = (c * G1 + 5 * B / 2) * X ^ 4 := by ring
    set H : ℕ → ℝ := fun L => 2 * B * exp ((1 - (L : ℝ)) / 2) with hHd
    set V : ℕ → ℝ := fun L => (Real.exp (((L : ℝ) + 1) / 2) * Q + Real.exp 1 * B) + Lpos with hVd
    set ε := κ / √√X with hεd
    have hε : 0 < ε := by positivity
    set Y := W0 / (2 * κ) * X ^ 5 with hYd
    have hY : 0 < Y := by positivity
    have hH : ∀ L : ℕ, ∀ s ∈ Icc ((L : ℝ) - 1) (L + 1), |(fi - fX) s| ≤ H L := by
      intro L s hs
      have h1 := abs_logScale_fullTail_le hg hg₁ hg₂c hc s
      have h2' := abs_logScale_posTail_le hg hg₁ hg₂c hc X s
      have h3 : exp (-(s / 2)) ≤ exp ((1 - (L : ℝ)) / 2) := exp_le_exp.mpr (by linarith [hs.1])
      simp only [Pi.sub_apply, hHd]
      calc |fi s - fX s| ≤ |fi s| + |fX s| := abs_sub _ _
        _ ≤ B * exp (-(s / 2)) + B * exp (-(s / 2)) := add_le_add h1 h2'
        _ ≤ 2 * B * exp ((1 - (L : ℝ)) / 2) := by nlinarith [mul_le_mul_of_nonneg_left h3 hB]
    have hV : ∀ L : ℕ, ∀ h ∈ Ioc (0 : ℝ) 1,
        ∫ s in Ico ((L : ℝ) - 1) L, |(fi - fX) s - (fi - fX) (s + h)| ≤ h * V L := by
      intro L h hh
      have hi1 : Integrable (fun s => |fi s - fi (s + h)|) := (hmi.2.sub (hmi.2.comp_add_right h)).abs
      have hi2 : Integrable (fun s => |fX s - fX (s + h)|) := (hadm.2.1.sub (hadm.2.1.comp_add_right h)).abs
      have hm1 := modulus_logScale_fullTail hg hg₁ hg₂c hc hGs L hh
      have hm2 := modulus_logScale_posTail hg hg₁ hg₂c hc hX hh.1.le
      have hm2' : ∫ s in Ico ((L : ℝ) - 1) L, |fX s - fX (s + h)| ≤ Lpos * h :=
        (setIntegral_le_integral hi2 (Eventually.of_forall fun _ => abs_nonneg _)).trans hm2
      calc ∫ s in Ico ((L : ℝ) - 1) L, |(fi - fX) s - (fi - fX) (s + h)|
          ≤ ∫ s in Ico ((L : ℝ) - 1) L, (|fi s - fi (s + h)| + |fX s - fX (s + h)|) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hi1.add hi2).integrableOn
              (Eventually.of_forall fun s => by
                simp only [Pi.sub_apply]
                rw [show fi s - fX s - (fi (s + h) - fX (s + h)) = (fi s - fi (s + h)) - (fX s - fX (s + h)) by
                  ring]
                exact abs_sub _ _)
        _ = (∫ s in Ico ((L : ℝ) - 1) L, |fi s - fi (s + h)|)
              + ∫ s in Ico ((L : ℝ) - 1) L, |fX s - fX (s + h)| := integral_add hi1.integrableOn hi2.integrableOn
        _ ≤ h * (Real.exp (((L : ℝ) + 1) / 2) * Q + Real.exp 1 * B) + Lpos * h := add_le_add hm1 hm2'
        _ = h * V L := by simp only [hVd]; ring
    have hnorm : ∫ s, (fi - fX) s ^ 2 ≤ Kb / √X := by
      have hF : ∀ θ ≤ 1, (fun θ => fullTail (psi c g) θ - posTail (psi c g) X θ) θ = 0 := by
        intro θ hθ; simp only; rw [fullTail, if_neg (not_lt.mpr hθ), posTail_zero _ _ hθ, sub_zero]
      have he : (fun s => (fi - fX) s ^ 2)
          = fun s => logScale (fun θ => fullTail (psi c g) θ - posTail (psi c g) X θ) s ^ 2 := by
        funext s; simp only [Pi.sub_apply, hfi, hfX, logScale]; ring
      have hall : ∫ s, (fi - fX) s ^ 2
          = ∫ θ in Ioi 1, (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2 := by
        rw [he, integral_sq _ hF]; congr 1; funext θ; ring
      rw [hall]
      exact (integral_sub_sq_le hg hg₁ hg₂c hc hX).trans (K1_le hc A C1 hX)
    have ha : ∀ L : ℕ, ∫ s in Icc ((L : ℝ) - 1) (L + 1), (fi - fX) s ^ 2 ≤ ε * exp (-((L : ℝ) / 2)) := by
      intro L
      set m := ∫ s in Icc ((L : ℝ) - 1) (L + 1), (fi - fX) s ^ 2 with hm
      have hm0 : 0 ≤ m := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
      have hmK : m ≤ Kb / √X :=
        (setIntegral_le_integral h2.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)).trans hnorm
      have hmB : m ≤ 8 * Real.exp 1 * B ^ 2 * exp (-(L : ℝ)) := by
        have hsq : ∀ s ∈ Icc ((L : ℝ) - 1) (L + 1), (fi - fX) s ^ 2 ≤ 4 * B ^ 2 * exp (1 - L) := by
          intro s hs
          calc (fi - fX) s ^ 2 = |(fi - fX) s| ^ 2 := (sq_abs _).symm
            _ ≤ (2 * B * exp ((1 - (L : ℝ)) / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hH L s hs) 2
            _ = 4 * B ^ 2 * exp (1 - L) := by rw [mul_pow, mul_pow, sq (exp _), ← exp_add]; ring_nf
        calc m ≤ ∫ s in Icc ((L : ℝ) - 1) (L + 1), 4 * B ^ 2 * exp (1 - L) :=
              setIntegral_mono_on h2.integrable_sq.integrableOn (integrableOn_const measure_Icc_lt_top.ne)
                measurableSet_Icc hsq
          _ = 2 * (4 * B ^ 2 * exp (1 - L)) := by
              rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]; ring
          _ = 8 * Real.exp 1 * B ^ 2 * exp (-(L : ℝ)) := by
              rw [show (1 : ℝ) - L = 1 + -(L : ℝ) by ring, exp_add]; ring
      have hsq : m ^ 2 ≤ (ε * exp (-((L : ℝ) / 2))) ^ 2 := by
        have e1 : (ε * exp (-((L : ℝ) / 2))) ^ 2 = κ ^ 2 / √X * exp (-(L : ℝ)) := by
          rw [hεd, mul_pow, div_pow, Real.sq_sqrt (Real.sqrt_nonneg X), sq (exp _), ← exp_add]; ring_nf
        rw [e1, sq m]
        calc m * m ≤ (Kb / √X) * (8 * Real.exp 1 * B ^ 2 * exp (-(L : ℝ))) :=
              mul_le_mul hmK hmB hm0 (by positivity)
          _ = (8 * Real.exp 1 * B ^ 2 * Kb) / √X * exp (-(L : ℝ)) := by ring
          _ ≤ κ ^ 2 / √X * exp (-(L : ℝ)) := by gcongr
      exact (pow_le_pow_iff_left₀ hm0 (by positivity) two_ne_zero).mp hsq
    have hHV0 : ∀ L, 0 ≤ H L * V L := fun L => by simp only [hHd, hVd]; positivity
    have hHV : ∀ L, H L * V L ≤ 2 * ε * Y := by
      intro L
      have hL : exp ((1 - (L : ℝ)) / 2) ≤ Real.exp (1 / 2) :=
        exp_le_exp.mpr (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
      have e : H L * V L = 2 * B * Real.exp 1 * Q
          + 2 * B * exp ((1 - (L : ℝ)) / 2) * (Real.exp 1 * B + Lpos) := by
        simp only [hHd, hVd]
        rw [show 2 * B * exp ((1 - (L : ℝ)) / 2) * (Real.exp (((L : ℝ) + 1) / 2) * Q + Real.exp 1 * B + Lpos)
          = 2 * B * (exp ((1 - (L : ℝ)) / 2) * Real.exp (((L : ℝ) + 1) / 2)) * Q
            + 2 * B * exp ((1 - (L : ℝ)) / 2) * (Real.exp 1 * B + Lpos) by ring, ← exp_add]
        ring_nf
      have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX
      have h1 : H L * V L ≤ W0 * X ^ 4 := by
        rw [e]
        have t1 : 2 * B * exp ((1 - (L : ℝ)) / 2) * (Real.exp 1 * B + Lpos)
            ≤ 2 * B * Real.exp (1 / 2) * (Real.exp 1 * B + (c * G1 + 5 * B / 2) * X ^ 4) := by
          gcongr
        have t2 : Real.exp 1 * B ≤ Real.exp 1 * B * X ^ 4 := le_mul_of_one_le_right (by positivity) hX4
        have t3 : 2 * B * Real.exp 1 * Q ≤ 2 * B * Real.exp 1 * Q * X ^ 4 :=
          le_mul_of_one_le_right (by positivity) hX4
        have h0 : 0 ≤ 2 * B * Real.exp (1 / 2) := by positivity
        have t4 := mul_le_mul_of_nonneg_left t2 h0
        rw [hW0d]; nlinarith
      have h2' : W0 * X ^ 4 ≤ 2 * ε * Y := by
        have hss0 : 0 < √√X := by positivity
        have e2 : 2 * ε * Y = W0 * X ^ 4 * (X / √√X) := by
          rw [hεd, hYd]; field_simp
        rw [e2]
        exact le_mul_of_one_le_right (by positivity) ((one_le_div hss0).mpr hssX')
      linarith
    obtain ⟨hsum, hsle⟩ := block_sum_le hε hY hHV0 hHV
    obtain ⟨-, hblock⟩ := Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_le_block h2 hf0
      (abar := fun L => ε * exp (-((L : ℝ) / 2))) (fun L => by positivity) hH hV ha hsum
    have hlogY : |Real.log Y| ≤ |c0| + 5 * Real.log X := by
      rw [hYd, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      calc |c0 + 5 * Real.log X| ≤ |c0| + |5 * Real.log X| := abs_add_le _ _
        _ = |c0| + 5 * Real.log X := by rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hlogX)]
    calc Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (fi - fX)
        ≤ D * (∫ s, (fi - fX) s ^ 2) + 2 * ∑' L : ℕ, ε * exp (-((L : ℝ) / 2))
            * max 1 (Real.log (H L * V L / (2 * (ε * exp (-((L : ℝ) / 2)))))) := hblock
      _ ≤ D * (Kb / √X) + 2 * (ε * ((1 + |Real.log Y|) * S0 + 1 / 2 * S1)) := by gcongr
      _ = D * (Kb / √X) + 2 * ε * ((1 + |Real.log Y|) * S0 + 1 / 2 * S1) := by ring
      _ ≤ D * (Kb / √X) + 2 * (κ / √√X) * ((1 + |c0| + 5 * Real.log X) * S0 + 1 / 2 * S1) := by
          have hP : (1 + |Real.log Y|) * S0 + 1 / 2 * S1 ≤ (1 + |c0| + 5 * Real.log X) * S0 + 1 / 2 * S1 := by
            have := mul_le_mul_of_nonneg_right (show 1 + |Real.log Y| ≤ 1 + |c0| + 5 * Real.log X by linarith) hS00
            linarith
          rw [hεd]
          exact add_le_add_right (mul_le_mul_of_nonneg_left hP (by positivity)) _
  have hlim : Tendsto (fun X : ℝ => D * (Kb / √X)
      + 2 * (κ / √√X) * ((1 + |c0| + 5 * Real.log X) * S0 + 1 / 2 * S1)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun X : ℝ => Kb / √X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_sqrt_atTop
    have t2 : Tendsto (fun X : ℝ => κ / √√X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp tendsto_sqrt_atTop)
    have t3 := tendsto_log_div_sqrt_sqrt
    have e : (fun X : ℝ => D * (Kb / √X) + 2 * (κ / √√X) * ((1 + |c0| + 5 * Real.log X) * S0 + 1 / 2 * S1))
        = fun X => D * (Kb / √X) + 2 * ((κ / √√X) * ((1 + |c0|) * S0 + 1 / 2 * S1)
          + 5 * κ * S0 * (Real.log X / √√X)) := by
      funext X; ring
    rw [e]
    have := (t1.const_mul D).add (((t2.mul_const ((1 + |c0|) * S0 + 1 / 2 * S1)).add
      (t3.const_mul (5 * κ * S0))).const_mul 2)
    simpa using this
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_nonneg ((memLp_logScale_fullTail hg hg₁ hg₂c hc).1.sub
      (Cvs.L2a.PositionTailAdmissible.admissible_posTail hX ((contDiff_psi hgc c).contDiffOn (s := Icc 1 X))).1)
  · filter_upwards [eventually_ge_atTop 1] with X hX using hbound X hX

/-- **The archimedean channel converges**: `archFull f_X → archFull f_∞`, by `|√E f_∞ − √E f_X| ≤ √E(f_∞ − f_X)`. -/
theorem tendsto_archFull (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail (psi c g) X))) atTop
      (𝓝 (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c g))))) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hmi := memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hli := integrableOn_levy_fullTail hg hg₁ hg₂c hc
  have hsq : Tendsto (fun X : ℝ => √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail (psi c g) X)))) atTop
      (𝓝 (√(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c g)))))) := by
    have h0 : Tendsto (fun X : ℝ => √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
        (logScale (fullTail (psi c g)) - logScale (posTail (psi c g) X)))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_archFull_sub hg hg₁ hg₂c hc)
      rwa [Real.sqrt_zero] at this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hadm := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX ((contDiff_psi hgc c).contDiffOn (s := Icc 1 X))
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact Cvs.WeilForm.Archimedean.LevyUnitBlocks.abs_sqrt_archFull_sub_le hmi.1 hadm.1 hli hadm.2.2.2.2
  have h := hsq.pow 2
  rw [Real.sq_sqrt (Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_nonneg hmi.1)] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hadm := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX ((contDiff_psi hgc c).contDiffOn (s := Icc 1 X))
  exact Real.sq_sqrt (Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_nonneg hadm.1)

end Cvs.L2a.FullTailArchChannel
