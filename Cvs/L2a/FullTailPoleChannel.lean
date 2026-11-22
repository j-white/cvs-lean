import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.Prolate.CosineTransformSecondOrder

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole channel: `∫F_X → Π₊` and `∫F_X/θ → Π₋`

With `K_I = 2|A| + C₁`: `|∫_t^Y ψ| ≤ K_I/(c²t)`, so `I(t) = ∫_t^∞ ψ` exists as a limit, `Π₊ = Σ_m I(m)/m` is a
`tsum`, `|∫F_X − Π₊| ≤ (K_I/c²)(3 + log X)/X`, `|∫F_X/θ − ∫F_∞/θ| ≤ √K1(X)`, and the product converges.
-/

namespace Cvs.L2a.FullTailPoleChannel

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence

/-- The improper integral `∫_t^∞ Φ`, as the limit of `∫_t^Y Φ` as `Y → ∞`. -/
noncomputable def tailInt (Φ : ℝ → ℝ) (t : ℝ) : ℝ := limUnder atTop (fun Y : ℝ => ∫ ξ in t..Y, Φ ξ)

/-- The pole constant `Π₊ = Σ_{m ≥ 1} I(m)/m` with `I(t) = ∫_t^∞ Φ`. -/
noncomputable def piPlus (Φ : ℝ → ℝ) : ℝ := ∑' m : ℕ, tailInt Φ ((m : ℝ) + 1) / ((m : ℝ) + 1)

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-- A sum over `[1, n]` is the shifted sum over `range n`. -/
theorem sum_Icc_eq_sum_range (F : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, F m = ∑ m ∈ Finset.range n, F (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- A shifted sum over `range N` is the sum over `(n, n + N]`. -/
theorem sum_range_eq_sum_Ioc (F : ℕ → ℝ) (n N : ℕ) :
    ∑ i ∈ Finset.range N, F (i + n + 1) = ∑ m ∈ Finset.Ioc n (n + N), F m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, show n + (N + 1) = n + N + 1 by omega,
      Finset.sum_Ioc_succ_top (by omega), Nat.add_comm N n]

/-- **The tail integral bound** `|∫_t^Y ψ| ≤ (2|A| + C₁)/(c²t)` for `1 ≤ t ≤ Y`: one integration by parts
against `−A cos(cξ)/(c²ξ)`, remainder `≤ (C₁ + |A|)/(c²ξ²)`. -/
theorem abs_integral_psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {t Y : ℝ} (ht : 1 ≤ t) (htY : t ≤ Y) :
    |∫ ξ in t..Y, psi c g ξ|
      ≤ (2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) / (c ^ 2 * t) := by
  set A := g 1 + g (-1) with hA
  set C1 := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC1d
  have hC1 : 0 ≤ C1 := C1_nonneg g₁ g₂
  have ht0 : 0 < t := by linarith
  have hY0 : 0 < Y := by linarith
  have hψ : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hpos : ∀ ξ ∈ uIcc t Y, 0 < ξ := fun ξ hξ => by
    rw [uIcc_of_le htY] at hξ; linarith [hξ.1]
  have hderiv : ∀ ξ ∈ uIcc t Y, HasDerivAt (fun ξ => -A * Real.cos (c * ξ) / (c ^ 2 * ξ))
      (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)) ξ := by
    intro ξ hξ
    have hξ0 := hpos ξ hξ
    have h1 : HasDerivAt (fun ξ => -A * Real.cos (c * ξ)) (A * c * Real.sin (c * ξ)) ξ := by
      have := ((hasDerivAt_id ξ).const_mul c).cos.const_mul (-A)
      refine this.congr_deriv ?_
      simp only [id, mul_one]; ring
    have h2 : HasDerivAt (fun ξ => c ^ 2 * ξ) (c ^ 2) ξ := by
      simpa using (hasDerivAt_id ξ).const_mul (c ^ 2)
    refine (h1.div h2 (by positivity)).congr_deriv ?_
    field_simp
    ring
  have hh'c : ContinuousOn (fun ξ => A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2))
      (uIcc t Y) := by
    have hn1 : ContinuousOn (fun ξ : ℝ => A * Real.sin (c * ξ)) (uIcc t Y) := by fun_prop
    have hd1 : ContinuousOn (fun ξ : ℝ => c * ξ) (uIcc t Y) := by fun_prop
    have hn2 : ContinuousOn (fun ξ : ℝ => A * Real.cos (c * ξ)) (uIcc t Y) := by fun_prop
    have hd2 : ContinuousOn (fun ξ : ℝ => c ^ 2 * ξ ^ 2) (uIcc t Y) := by fun_prop
    have hz1 : ∀ ξ ∈ uIcc t Y, c * ξ ≠ 0 := fun ξ hξ => by have := hpos ξ hξ; positivity
    have hz2 : ∀ ξ ∈ uIcc t Y, c ^ 2 * ξ ^ 2 ≠ 0 := fun ξ hξ => by have := hpos ξ hξ; positivity
    exact (hn1.div₀ hd1 hz1).add (hn2.div₀ hd2 hz2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hh'c.intervalIntegrable
  have hsplit : ∫ ξ in t..Y, psi c g ξ
      = (-A * Real.cos (c * Y) / (c ^ 2 * Y) - -A * Real.cos (c * t) / (c ^ 2 * t))
        + ∫ ξ in t..Y, (psi c g ξ
            - (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2))) := by
    rw [intervalIntegral.integral_sub (hψ.intervalIntegrable _ _) hh'c.intervalIntegrable, hFTC]
    ring
  set E := (C1 + |A|) / c ^ 2 with hEd
  have hE : 0 ≤ E := by positivity
  have hrem : ∀ ξ, 0 < ξ → |psi c g ξ - (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2))|
      ≤ E * (1 / ξ ^ 2) := by
    intro ξ hξ
    have hcξ : c * ξ ≠ 0 := by positivity
    have h1 := Cvs.Prolate.CosineTransformSecondOrder.psi_sub_le hg hg₁ hg₂c hcξ
    have h2 : |A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)| ≤ |A| / (c ^ 2 * ξ ^ 2) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < c ^ 2 * ξ ^ 2), abs_mul]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
        (by positivity)
    calc |psi c g ξ - (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2))|
        = |(psi c g ξ - A * Real.sin (c * ξ) / (c * ξ)) - A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)| := by
          congr 1; ring
      _ ≤ |psi c g ξ - A * Real.sin (c * ξ) / (c * ξ)| + |A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)| :=
          abs_sub _ _
      _ ≤ C1 / (c * ξ) ^ 2 + |A| / (c ^ 2 * ξ ^ 2) := add_le_add h1 h2
      _ = E * (1 / ξ ^ 2) := by rw [hEd]; field_simp
  have hinvc : ContinuousOn (fun ξ : ℝ => 1 / ξ ^ 2) (uIcc t Y) :=
    continuousOn_const.div₀ (continuousOn_pow 2) fun ξ hξ => pow_ne_zero 2 (hpos ξ hξ).ne'
  have hq : ∫ ξ in t..Y, E * (1 / ξ ^ 2) = E * (1 / t - 1 / Y) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hd : ∀ ξ ∈ uIcc t Y, HasDerivAt (fun ξ : ℝ => -ξ⁻¹) (1 / ξ ^ 2) ξ := fun ξ hξ => by
      have hξ0 := (hpos ξ hξ).ne'
      refine (hasDerivAt_inv hξ0).neg.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hinvc.intervalIntegrable]
    simp only [one_div]; ring
  have hI : |∫ ξ in t..Y, (psi c g ξ
      - (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)))| ≤ E * (1 / t - 1 / Y) := by
    rw [← hq, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le htY (ae_of_all _ fun ξ hξ => ?_)
      (hinvc.intervalIntegrable.const_mul E)
    rw [Real.norm_eq_abs]
    exact hrem ξ (ht0.trans hξ.1)
  have hb : ∀ ξ, 0 < ξ → |-A * Real.cos (c * ξ) / (c ^ 2 * ξ)| ≤ |A| / (c ^ 2 * ξ) := fun ξ hξ => by
    rw [abs_div, abs_of_pos (by positivity : 0 < c ^ 2 * ξ), abs_mul, abs_neg]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
      (by positivity)
  have hbY := hb Y hY0
  have hbt := hb t ht0
  have hlast : |A| / (c ^ 2 * Y) + |A| / (c ^ 2 * t) + E * (1 / t - 1 / Y)
      = (2 * |A| + C1) / (c ^ 2 * t) - C1 / (c ^ 2 * Y) := by
    rw [hEd]; field_simp; ring
  have hC1Y : 0 ≤ C1 / (c ^ 2 * Y) := by positivity
  rw [hsplit]
  calc |(-A * Real.cos (c * Y) / (c ^ 2 * Y) - -A * Real.cos (c * t) / (c ^ 2 * t))
        + ∫ ξ in t..Y, (psi c g ξ
            - (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)))|
      ≤ |-A * Real.cos (c * Y) / (c ^ 2 * Y) - -A * Real.cos (c * t) / (c ^ 2 * t)|
        + |∫ ξ in t..Y, (psi c g ξ
            - (A * Real.sin (c * ξ) / (c * ξ) + A * Real.cos (c * ξ) / (c ^ 2 * ξ ^ 2)))| := abs_add_le _ _
    _ ≤ (|A| / (c ^ 2 * Y) + |A| / (c ^ 2 * t)) + E * (1 / t - 1 / Y) :=
        add_le_add ((abs_sub _ _).trans (add_le_add hbY hbt)) hI
    _ ≤ (2 * |A| + C1) / (c ^ 2 * t) := by linarith

/-- **The tail integral converges**: `∫_t^Y ψ → I(t)` as `Y → ∞`, for `t ≥ 1`. -/
theorem tendsto_tailInt (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {t : ℝ} (ht : 1 ≤ t) :
    Tendsto (fun Y : ℝ => ∫ ξ in t..Y, psi c g ξ) atTop (𝓝 (tailInt (psi c g) t)) := by
  apply tendsto_nhds_limUnder
  apply cauchySeq_tendsto_of_complete
  have hψ : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  set K := 2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hKd
  have hK : 0 ≤ K := add_nonneg (by positivity) (C1_nonneg g₁ g₂)
  rw [Metric.cauchySeq_iff']
  intro ε hε
  refine ⟨max t (K / (c ^ 2 * ε) + 1), fun Y hY => ?_⟩
  set N := max t (K / (c ^ 2 * ε) + 1) with hNd
  have hN1 : 1 ≤ N := ht.trans (le_max_left _ _)
  have hN0 : 0 < N := by linarith
  have hNK : K / (c ^ 2 * ε) < N := by have := le_max_right t (K / (c ^ 2 * ε) + 1); linarith
  rw [Real.dist_eq, intervalIntegral.integral_interval_sub_left (hψ.intervalIntegrable _ _)
    (hψ.intervalIntegrable _ _)]
  refine (abs_integral_psi_le hg hg₁ hg₂c hc hN1 hY).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at hNK
  nlinarith

/-- `|I(t)| ≤ (2|A| + C₁)/(c²t)` for `t ≥ 1`. -/
theorem abs_tailInt_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {t : ℝ} (ht : 1 ≤ t) :
    |tailInt (psi c g) t|
      ≤ (2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) / (c ^ 2 * t) :=
  le_of_tendsto (tendsto_tailInt hg hg₁ hg₂c hc ht).abs
    ((eventually_ge_atTop t).mono fun _ hY => abs_integral_psi_le hg hg₁ hg₂c hc ht hY)

/-- `I(t) − I(u) = ∫_t^u ψ` for `t, u ≥ 1`. -/
theorem tailInt_sub (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {t u : ℝ} (ht : 1 ≤ t) (hu : 1 ≤ u) :
    tailInt (psi c g) t - tailInt (psi c g) u = ∫ ξ in t..u, psi c g ξ := by
  have hψ : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have h := (tendsto_tailInt hg hg₁ hg₂c hc ht).sub (tendsto_tailInt hg hg₁ hg₂c hc hu)
  have e : (fun Y : ℝ => (∫ ξ in t..Y, psi c g ξ) - ∫ ξ in u..Y, psi c g ξ)
      = fun _ => ∫ ξ in t..u, psi c g ξ := by
    funext Y
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := u) (hψ.intervalIntegrable _ _)
      (hψ.intervalIntegrable _ _)]
    ring
  rw [e] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The terms of `Π₊`: `|I(m + 1)/(m + 1)| ≤ ((2|A| + C₁)/c²) · 1/(m + 1)²`. -/
theorem abs_tailInt_div_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (m : ℕ) :
    |tailInt (psi c g) ((m : ℝ) + 1) / ((m : ℝ) + 1)|
      ≤ (2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) / c ^ 2
        * (1 / ((m : ℝ) + 1) ^ 2) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := m.cast_nonneg (α := ℝ); linarith
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have h := abs_tailInt_le hg hg₁ hg₂c hc hm
  rw [abs_div, abs_of_pos hm0]
  calc |tailInt (psi c g) ((m : ℝ) + 1)| / ((m : ℝ) + 1)
      ≤ (2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) / (c ^ 2 * ((m : ℝ) + 1))
        / ((m : ℝ) + 1) := div_le_div_of_nonneg_right h hm0.le
    _ = _ := by field_simp

/-- **`Π₊` is a convergent series**: `Σ_m I(m + 1)/(m + 1)` is summable. -/
theorem summable_piPlus (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Summable fun m : ℕ => tailInt (psi c g) ((m : ℝ) + 1) / ((m : ℝ) + 1) := by
  have hs : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast this
  refine Summable.of_norm_bounded (hs.mul_left
    ((2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) / c ^ 2)) fun m => ?_
  rw [Real.norm_eq_abs]
  exact abs_tailInt_div_le hg hg₁ hg₂c hc m

/-- **The pole rate** (Theorem L (3)): `|∫_{(1,∞)} F_X − Π₊| ≤ ((2|A| + C₁)/c²)(3 + log X)/X` for `X ≥ 1`. -/
theorem abs_integral_posTail_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    |(∫ θ in Ioi 1, posTail (psi c g) X θ) - piPlus (psi c g)|
      ≤ (2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)) / c ^ 2
        * (3 + Real.log X) / X := by
  set K := 2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hKd
  have hK : 0 ≤ K := add_nonneg (by positivity) (C1_nonneg g₁ g₂)
  have hψ : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hX0 : 0 < X := by linarith
  set n := ⌊X⌋₊ with hnd
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hX)
  have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0.le
  have hXn : X < n + 1 := Nat.lt_floor_add_one X
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set H := ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹ with hHd
  have hint : ∫ θ in Ioi 1, posTail (psi c g) X θ
      = ∑ m ∈ Finset.Icc 1 n, tailInt (psi c g) m / m - tailInt (psi c g) X * H := by
    have h := Cvs.L2a.PositionTailSpanAdapters.integral_posTail_mul (ψ := psi c g) (w := fun _ => 1) hX
      hψ.continuousOn continuousOn_const
    simp only [mul_one] at h
    rw [h, hHd, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_Icc.mp hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm'.1
    rw [← tailInt_sub hg hg₁ hg₂c hc hm1 hX]
    ring
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ => by positivity
  have hH : H ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log n
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    exact h.trans (by linarith [Real.log_le_log hn0 hnX])
  set f : ℕ → ℝ := fun m => tailInt (psi c g) ((m : ℝ) + 1) / ((m : ℝ) + 1) with hfd
  have hsum : Summable f := summable_piPlus hg hg₁ hg₂c hc
  have hpi : piPlus (psi c g) = ∑ m ∈ Finset.range n, f m + ∑' i, f (i + n) :=
    (hsum.sum_add_tsum_nat_add n).symm
  have hfin : ∑ m ∈ Finset.Icc 1 n, tailInt (psi c g) m / m = ∑ m ∈ Finset.range n, f m := by
    rw [sum_Icc_eq_sum_range (fun m => tailInt (psi c g) m / m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hfd]; push_cast; rfl
  have htail : |∑' i, f (i + n)| ≤ K / c ^ 2 * (1 / (n : ℝ)) := by
    have hs' : Summable fun i => f (i + n) := (summable_nat_add_iff n).mpr hsum
    refine le_of_tendsto' hs'.hasSum.tendsto_sum_nat.abs fun N => ?_
    calc |∑ i ∈ Finset.range N, f (i + n)| ≤ ∑ i ∈ Finset.range N, |f (i + n)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, K / c ^ 2 * (1 / (((i + n + 1 : ℕ)) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => (abs_tailInt_div_le hg hg₁ hg₂c hc (i + n)).trans_eq (by push_cast; ring)
      _ = K / c ^ 2 * ∑ m ∈ Finset.Ioc n (n + N), 1 / (m : ℝ) ^ 2 := by
          rw [← Finset.mul_sum, sum_range_eq_sum_Ioc (fun m => 1 / (m : ℝ) ^ 2)]
      _ ≤ K / c ^ 2 * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_one_div_sq_le hn1 _) (by positivity)
  have h1n : 1 / (n : ℝ) ≤ 2 / X := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [div_le_div_iff₀ hn0 hX0]; linarith
  have hIX := abs_tailInt_le hg hg₁ hg₂c hc hX
  have hdiff : (∫ θ in Ioi 1, posTail (psi c g) X θ) - piPlus (psi c g)
      = -(tailInt (psi c g) X * H) - ∑' i, f (i + n) := by
    rw [hint, hpi, hfin]; ring
  rw [hdiff]
  calc |-(tailInt (psi c g) X * H) - ∑' i, f (i + n)|
      ≤ |-(tailInt (psi c g) X * H)| + |∑' i, f (i + n)| := abs_sub _ _
    _ = |tailInt (psi c g) X| * H + |∑' i, f (i + n)| := by rw [abs_neg, abs_mul, abs_of_nonneg hH0]
    _ ≤ K / (c ^ 2 * X) * (1 + Real.log X) + K / c ^ 2 * (2 / X) :=
        add_le_add (mul_le_mul hIX hH hH0 (by positivity))
          (htail.trans (mul_le_mul_of_nonneg_left h1n (by positivity)))
    _ = K / c ^ 2 * (3 + Real.log X) / X := by field_simp; ring

/-- **The `Π₋` rate**: `|∫_{(1,∞)} F_X/θ − ∫_{(1,∞)} F_∞/θ| ≤ √K1(X)`, by Cauchy–Schwarz with `∫_{(1,∞)} θ⁻² = 1`. -/
theorem abs_integral_posTail_div_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    |(∫ θ in Ioi 1, posTail (psi c g) X θ / θ) - ∫ θ in Ioi 1, fullTail (psi c g) θ / θ|
      ≤ √(K1 c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) X) := by
  set a := posTail (psi c g) X with had
  set b := fullTail (psi c g) with hbd
  have ham := measurable_posTail_psi hg c X
  have hbm := measurable_fullTail hg hg₁ hg₂c hc
  have hwm : Measurable fun θ : ℝ => θ⁻¹ := measurable_inv
  have hwb : ∀ θ : ℝ, 0 < θ → |θ⁻¹| ≤ 1 / θ := fun θ hθ => by
    rw [abs_of_pos (inv_pos.mpr hθ), one_div]
  have ia : IntegrableOn (fun θ => a θ * θ⁻¹) (Ioi 1) :=
    integrableOn_mul_of_le ham hwm (fun θ hθ => abs_posTail_le hg hg₁ hg₂c hc X hθ) hwb
  have ib : IntegrableOn (fun θ => b θ * θ⁻¹) (Ioi 1) :=
    integrableOn_mul_of_le hbm hwm (fun θ hθ => abs_fullTail_le hg hg₁ hg₂c hc hθ) hwb
  have hdb : ∀ θ, 0 < θ → |a θ - b θ| ≤ _ / θ := fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
  have id : IntegrableOn (fun θ => (a θ - b θ) * θ⁻¹) (Ioi 1) :=
    integrableOn_mul_of_le (f := fun θ => a θ - b θ) (ham.sub hbm) hwm hdb hwb
  have hd2 : IntegrableOn (fun θ => (a θ - b θ) ^ 2) (Ioi 1) :=
    integrableOn_sq_of_le (f := fun θ => a θ - b θ) (ham.sub hbm) hdb
  have hw2 : IntegrableOn (fun θ : ℝ => θ⁻¹ ^ 2) (Ioi 1) := integrableOn_sq_of_le hwm hwb
  have hw1 : ∫ θ in Ioi 1, (θ⁻¹ : ℝ) ^ 2 = 1 := by
    have h := integral_one_div_sq (a := 1) one_pos
    simpa only [one_div, inv_pow, inv_one] using h
  have e : (∫ θ in Ioi 1, a θ / θ) - ∫ θ in Ioi 1, b θ / θ = ∫ θ in Ioi 1, (a θ - b θ) * θ⁻¹ := by
    simp only [div_eq_mul_inv]
    rw [← integral_sub ia ib]
    congr 1; funext θ; ring
  rw [e]
  refine (abs_setIntegral_mul_le (f := fun θ => a θ - b θ) (w := fun θ => θ⁻¹) hd2 hw2 id).trans ?_
  rw [hw1, Real.sqrt_one, mul_one]
  exact Real.sqrt_le_sqrt (integral_sub_sq_le hg hg₁ hg₂c hc hX)

/-- **The pole channel converges**: `2 (∫F_X)(∫F_X/θ) → 2 Π₊ ∫_{(1,∞)} F_∞/θ`. -/
theorem tendsto_pole (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => 2 * (∫ θ in Ioi 1, posTail (psi c g) X θ) * (∫ θ in Ioi 1, posTail (psi c g) X θ / θ))
      atTop (𝓝 (2 * piPlus (psi c g) * ∫ θ in Ioi 1, fullTail (psi c g) θ / θ)) := by
  set K := 2 * |g 1 + g (-1)| + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hKd
  have hu : Tendsto (fun X : ℝ => K / c ^ 2 * (3 + Real.log X) / X) atTop (𝓝 0) := by
    have h3 : Tendsto (fun X : ℝ => 3 / X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hl : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa only [pow_one, one_mul, add_zero] using this
    have := (h3.add hl).const_mul (K / c ^ 2)
    rw [add_zero, mul_zero] at this
    refine this.congr fun X => ?_
    ring
  have h1 : Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (psi c g) X θ) atTop (𝓝 (piPlus (psi c g))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_ hu
    filter_upwards [eventually_ge_atTop 1] with X hX
    rw [Real.norm_eq_abs]
    exact abs_integral_posTail_sub_le hg hg₁ hg₂c hc hX
  have h2 : Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (psi c g) X θ / θ) atTop
      (𝓝 (∫ θ in Ioi 1, fullTail (psi c g) θ / θ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_
      (tendsto_sqrt_div_sqrt (K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)))
    filter_upwards [eventually_ge_atTop 1] with X hX
    rw [Real.norm_eq_abs]
    exact (abs_integral_posTail_div_sub_le hg hg₁ hg₂c hc hX).trans (Real.sqrt_le_sqrt (K1_le hc _ _ hX))
  exact (h1.const_mul 2).mul h2

end Cvs.L2a.FullTailPoleChannel
