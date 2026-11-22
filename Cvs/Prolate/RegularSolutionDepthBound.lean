import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A regular solution normalised at `1` is bounded on `[0, 1]` by its depth

For `y' = v`, `(t² − 1)v = u`, `u' = (χ − c²t²)y` on `[0, 1]`, with turning point `τ = √χ/c` and depth `D = c² − χ`:
on `[τ, 1]`, `u ≤ D(1 − t)y` and `ye^{Dt}` increases, so `y ≤ e^{D(1 − τ)}`; on `[σ, τ]` the energy
`y² + u²/c²` grows at most at rate `c(1 + c²/D)`; on `[0, σ]` Sonin's `y² + u²/(pq)` increases.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.RegularSolutionDepthBound

/-- A function with a nonnegative derivative on `[a, b]` is monotone there. -/
theorem monotoneOn_of_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ f' t) : MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hn t (interior_subset ht))

/-- The first-order radial system `y' = v`, `(t² − 1)v = u`, `u' = (χ − c²t²)y` on `[0, 1]`. -/
def IsSys (c χ : ℝ) (y v u : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt y (v t) t ∧ (t ^ 2 - 1) * v t = u t ∧
    HasDerivAt u ((χ - c ^ 2 * t ^ 2) * y t) t

variable {c χ τ : ℝ} {y v u : ℝ → ℝ}

/-! ### The forbidden zone `[τ, 1]` -/

/-- `v ≤ 0` on `[τ, 1]` when `u ≥ 0` there and `v(1) ≤ 0`. -/
theorem v_nonpos (hs : IsSys c χ y v u) (hτ0 : 0 ≤ τ) (hu0 : ∀ t ∈ Icc τ 1, 0 ≤ u t) (hv1 : v 1 ≤ 0) :
    ∀ t ∈ Icc τ 1, v t ≤ 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]; exact hv1
  · have he := (hs t ⟨hτ0.trans ht.1, ht.2⟩).2.1
    have := hu0 t ht
    have ht0 := hτ0.trans ht.1
    have h1 : 0 < 1 - t ^ 2 := by nlinarith
    by_contra hc
    push Not at hc
    nlinarith [mul_pos h1 hc]

/-- **The flux is at most `D(1 − t)y`** on `[τ, 1]`, `D = c² − χ`, `c²τ² = χ`. -/
theorem u_le (hs : IsSys c χ y v u) (hτ0 : 0 ≤ τ) (hy0 : ∀ t ∈ Icc τ 1, 0 ≤ y t)
    (hu0 : ∀ t ∈ Icc τ 1, 0 ≤ u t) (hu1 : u 1 = 0) (hv1 : v 1 ≤ 0) (hD : 0 ≤ c ^ 2 - χ) :
    ∀ t ∈ Icc τ 1, u t ≤ (c ^ 2 - χ) * (1 - t) * y t := by
  have hv := v_nonpos hs hτ0 hu0 hv1
  have hd : ∀ t ∈ Icc τ 1, HasDerivAt (fun t => u t - (c ^ 2 - χ) * (1 - t) * y t)
      ((χ - c ^ 2 * t ^ 2) * y t - ((c ^ 2 - χ) * (-1) * y t + (c ^ 2 - χ) * (1 - t) * v t)) t := by
    intro t ht
    have h := hs t ⟨hτ0.trans ht.1, ht.2⟩
    exact h.2.2.sub ((((hasDerivAt_id t).const_sub 1).const_mul (c ^ 2 - χ)).mul h.1 |>.congr_deriv (by simp))
  have hm := monotoneOn_of_deriv hd fun t ht => by
    have h1 := hy0 t ht
    have h2 := hv t ht
    have h3 : 0 ≤ (c ^ 2 - χ) * (1 - t) * (-v t) := mul_nonneg (mul_nonneg hD (by linarith [ht.2])) (by linarith)
    have ht0 := hτ0.trans ht.1
    have h5 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.2]
    have h4 : 0 ≤ c ^ 2 * (1 - t ^ 2) * y t := mul_nonneg (mul_nonneg (sq_nonneg c) h5) h1
    have e : (χ - c ^ 2 * t ^ 2) * y t - ((c ^ 2 - χ) * (-1) * y t + (c ^ 2 - χ) * (1 - t) * v t)
        = c ^ 2 * (1 - t ^ 2) * y t + (c ^ 2 - χ) * (1 - t) * (-v t) := by ring
    rw [e]; linarith
  intro t ht
  have := hm ht ⟨by linarith [ht.1, ht.2], le_rfl⟩ ht.2
  simp only [hu1, sub_self, mul_zero, zero_mul] at this
  linarith

/-- **The edge growth**: `y(t) ≤ y(τ) ≤ e^{D(1 − τ)}` on `[τ, 1]` and `u(τ) ≤ D(1 − τ)y(τ)`. -/
theorem forbidden (hs : IsSys c χ y v u) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hy0 : ∀ t ∈ Icc τ 1, 0 ≤ y t) (hu0 : ∀ t ∈ Icc τ 1, 0 ≤ u t) (hy1 : y 1 = 1) (hu1 : u 1 = 0)
    (hv1 : v 1 = -(c ^ 2 - χ) / 2) (hD : 0 ≤ c ^ 2 - χ) :
    (∀ t ∈ Icc τ 1, y t ≤ y τ) ∧ y τ ≤ Real.exp ((c ^ 2 - χ) * (1 - τ)) ∧
      u τ ≤ (c ^ 2 - χ) * (1 - τ) * y τ := by
  have hv1' : v 1 ≤ 0 := by rw [hv1]; linarith
  have hv := v_nonpos hs hτ0 hu0 hv1'
  have hu := u_le hs hτ0 hy0 hu0 hu1 hv1' hD
  have hτm : τ ∈ Icc τ 1 := ⟨le_rfl, hτ1⟩
  refine ⟨fun t ht => ?_, ?_, hu τ hτm⟩
  · have hd : ∀ r ∈ Icc τ 1, HasDerivAt (fun r => -y r) (-v r) r := fun r hr =>
      (hs r ⟨hτ0.trans hr.1, hr.2⟩).1.neg
    have := monotoneOn_of_deriv hd (fun r hr => by linarith [hv r hr]) hτm ht ht.1
    linarith
  · set D := c ^ 2 - χ
    have hd : ∀ r ∈ Icc τ 1, HasDerivAt (fun r => y r * Real.exp (D * r))
        (v r * Real.exp (D * r) + y r * (Real.exp (D * r) * (D * 1))) r := fun r hr =>
      (hs r ⟨hτ0.trans hr.1, hr.2⟩).1.mul (((hasDerivAt_id r).const_mul D).exp)
    have hm := monotoneOn_of_deriv hd fun r hr => by
      have hvD : 0 ≤ v r + D * y r := by
        rcases eq_or_lt_of_le hr.2 with h | h
        · rw [h, hv1, hy1]; linarith
        · have he := (hs r ⟨hτ0.trans hr.1, hr.2⟩).2.1
          have h1 := hu r hr
          have h2 := hv r hr
          have h3 := hy0 r hr
          have hr0 : 0 ≤ r := hτ0.trans hr.1
          -- `(1 − r)(1 + r)(−v) = u ≤ D(1 − r)y`, so `(1 + r)(−v) ≤ Dy`
          have h4 : (1 + r) * (-v r) ≤ D * y r := by
            have h5 : (1 - r) * ((1 + r) * (-v r)) ≤ (1 - r) * (D * y r) := by nlinarith
            exact le_of_mul_le_mul_left h5 (by linarith)
          nlinarith
      have := Real.exp_pos (D * r)
      nlinarith
    have := hm hτm ⟨hτ1, le_rfl⟩ hτ1
    simp only [hy1, one_mul, mul_one] at this
    rw [show D * (1 - τ) = D - D * τ by ring, Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
    simpa using this

/-! ### The near-turning zone `[σ, τ]` -/

/-- **Energy growth** on `[σ, τ]`: `y² + u²/c² ≤ (y(τ)² + u(τ)²/c²)·e^{c(1 + c²/D)(τ − r)}`. -/
theorem near (hs : IsSys c χ y v u) (hc : 0 < c) {σ : ℝ} (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hτ1 : τ < 1)
    (hτχ : c ^ 2 * τ ^ 2 = χ) (hD : 0 < c ^ 2 - χ) :
    ∀ r ∈ Icc σ τ, y r ^ 2 + u r ^ 2 / c ^ 2
      ≤ (y τ ^ 2 + u τ ^ 2 / c ^ 2) * Real.exp (c * (1 + c ^ 2 / (c ^ 2 - χ)) * (τ - r)) := by
  set D := c ^ 2 - χ
  set L := c * (1 + c ^ 2 / D)
  have hsub : ∀ r ∈ Icc σ τ, r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hσ0.trans hr.1, hr.2.trans hτ1.le⟩
  have hd : ∀ r ∈ Icc σ τ, HasDerivAt (fun r => (y r ^ 2 + u r ^ 2 / c ^ 2) * Real.exp (L * r))
      ((2 * y r * v r + 2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) / c ^ 2) * Real.exp (L * r)
        + (y r ^ 2 + u r ^ 2 / c ^ 2) * (Real.exp (L * r) * (L * 1))) r := by
    intro r hr
    obtain ⟨h1, -, h3⟩ := hs r (hsub r hr)
    have hF : HasDerivAt (fun r => y r ^ 2 + u r ^ 2 / c ^ 2)
        (2 * y r * v r + 2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) / c ^ 2) r := by
      have := (h1.pow 2).add ((h3.pow 2).div_const (c ^ 2))
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat]; ring
    exact hF.mul (((hasDerivAt_id r).const_mul L).exp)
  have hm := monotoneOn_of_deriv hd fun r hr => by
    obtain ⟨-, h2, -⟩ := hs r (hsub r hr)
    have hr0 : 0 ≤ r := hσ0.trans hr.1
    have hrτ : r ≤ τ := hr.2
    have hp : D / c ^ 2 ≤ 1 - r ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : r ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hr0 hrτ 2
      nlinarith
    have hpD : 0 < D / c ^ 2 := by positivity
    have hp0 : 0 < 1 - r ^ 2 := lt_of_lt_of_le hpD hp
    have hq0 : 0 ≤ χ - c ^ 2 * r ^ 2 := by
      have : r ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hr0 hrτ 2
      nlinarith [sq_nonneg c]
    have hqc : χ - c ^ 2 * r ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg r]
    -- `v = −u/p`
    have hv : v r = -(u r) / (1 - r ^ 2) := by
      field_simp; linarith
    have hinvp : 1 / (1 - r ^ 2) ≤ c ^ 2 / D := by
      rw [div_le_div_iff₀ hp0 (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hp
      linarith
    -- `|2uy| ≤ c(y² + u²/c²)`
    have hamgm : |2 * u r * y r| ≤ c * (y r ^ 2 + u r ^ 2 / c ^ 2) := by
      have e : c * (y r ^ 2 + u r ^ 2 / c ^ 2) = (c * y r ^ 2 + u r ^ 2 / c) := by field_simp
      rw [e, abs_le]
      constructor
      · have : 0 ≤ (c * y r + u r) ^ 2 / c := by positivity
        have e2 : (c * y r + u r) ^ 2 / c = c * y r ^ 2 + u r ^ 2 / c + 2 * u r * y r := by
          field_simp; ring
        linarith
      · have : 0 ≤ (c * y r - u r) ^ 2 / c := by positivity
        have e2 : (c * y r - u r) ^ 2 / c = c * y r ^ 2 + u r ^ 2 / c - 2 * u r * y r := by
          field_simp; ring
        linarith
    -- `|q/c² − 1/p| ≤ 1 + c²/D`
    have hm1 : |(χ - c ^ 2 * r ^ 2) / c ^ 2 - 1 / (1 - r ^ 2)| ≤ 1 + c ^ 2 / D := by
      have a1 : 0 ≤ (χ - c ^ 2 * r ^ 2) / c ^ 2 := by positivity
      have a2 : (χ - c ^ 2 * r ^ 2) / c ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hqc
      have a3 : 0 ≤ 1 / (1 - r ^ 2) := by positivity
      rw [abs_le]; constructor <;> linarith
    have hF0 : 0 ≤ y r ^ 2 + u r ^ 2 / c ^ 2 := by positivity
    have key : 2 * y r * v r + 2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) / c ^ 2
        = (2 * u r * y r) * ((χ - c ^ 2 * r ^ 2) / c ^ 2 - 1 / (1 - r ^ 2)) := by
      rw [hv]; field_simp; ring
    have hbound : -(L * (y r ^ 2 + u r ^ 2 / c ^ 2))
        ≤ 2 * y r * v r + 2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) / c ^ 2 := by
      rw [key]
      have := abs_mul (2 * u r * y r) ((χ - c ^ 2 * r ^ 2) / c ^ 2 - 1 / (1 - r ^ 2))
      have h5 : |2 * u r * y r| * |(χ - c ^ 2 * r ^ 2) / c ^ 2 - 1 / (1 - r ^ 2)|
          ≤ c * (y r ^ 2 + u r ^ 2 / c ^ 2) * (1 + c ^ 2 / D) :=
        mul_le_mul hamgm hm1 (abs_nonneg _) (by positivity)
      have h6 := neg_abs_le ((2 * u r * y r) * ((χ - c ^ 2 * r ^ 2) / c ^ 2 - 1 / (1 - r ^ 2)))
      have e : L * (y r ^ 2 + u r ^ 2 / c ^ 2) = c * (y r ^ 2 + u r ^ 2 / c ^ 2) * (1 + c ^ 2 / D) := by
        simp only [L]; ring
      linarith
    have := Real.exp_pos (L * r)
    have e : (2 * y r * v r + 2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) / c ^ 2) * Real.exp (L * r)
        + (y r ^ 2 + u r ^ 2 / c ^ 2) * (Real.exp (L * r) * (L * 1))
        = (2 * y r * v r + 2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) / c ^ 2 + L * (y r ^ 2 + u r ^ 2 / c ^ 2))
          * Real.exp (L * r) := by ring
    rw [e]
    exact mul_nonneg (by linarith) this.le
  intro r hr
  have h := hm hr ⟨hστ, le_rfl⟩ hr.2
  simp only at h
  have e : Real.exp (L * (τ - r)) = Real.exp (L * τ) / Real.exp (L * r) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, mul_div_assoc', le_div_iff₀ (Real.exp_pos _)]
  exact h

/-! ### The allowed zone `[0, σ]`: Sonin -/

/-- The Sonin derivative: with `v = −u/p` the cross terms cancel, leaving `−u²(pq)'/(pq)²`. -/
theorem sonin_alg {y v u r c χ : ℝ} (hp : 1 - r ^ 2 ≠ 0) (hq : χ - c ^ 2 * r ^ 2 ≠ 0) (hv : v = -u / (1 - r ^ 2)) :
    2 * y * v + (2 * u * ((χ - c ^ 2 * r ^ 2) * y) * ((1 - r ^ 2) * (χ - c ^ 2 * r ^ 2))
        - u ^ 2 * ((-(2 * r)) * (χ - c ^ 2 * r ^ 2) + (1 - r ^ 2) * (-(c ^ 2 * (2 * r)))))
        / ((1 - r ^ 2) * (χ - c ^ 2 * r ^ 2)) ^ 2
      = -(u ^ 2 * ((-(2 * r)) * (χ - c ^ 2 * r ^ 2) + (1 - r ^ 2) * (-(c ^ 2 * (2 * r)))))
        / ((1 - r ^ 2) * (χ - c ^ 2 * r ^ 2)) ^ 2 := by
  set p := 1 - r ^ 2
  set q := χ - c ^ 2 * r ^ 2
  rw [hv]; field_simp; ring

/-- **Sonin's function increases** on `[0, σ]` where `χ − c²σ² > 0` and `σ < 1`. -/
theorem sonin_le (hs : IsSys c χ y v u) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hq : 0 < χ - c ^ 2 * σ ^ 2) :
    ∀ r ∈ Icc 0 σ, y r ^ 2 ≤ y σ ^ 2 + u σ ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)) := by
  set P : ℝ → ℝ := fun r => (1 - r ^ 2) * (χ - c ^ 2 * r ^ 2) with hP
  have hsub : ∀ r ∈ Icc 0 σ, r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hr.1, hr.2.trans hσ1.le⟩
  have hpos : ∀ r ∈ Icc 0 σ, 0 < 1 - r ^ 2 ∧ 0 < χ - c ^ 2 * r ^ 2 := by
    intro r hr
    have : r ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    have : σ ^ 2 < 1 := by nlinarith
    constructor
    · linarith
    · nlinarith [sq_nonneg c]
  have hP0 : ∀ r ∈ Icc 0 σ, 0 < P r := fun r hr => mul_pos (hpos r hr).1 (hpos r hr).2
  have hd : ∀ r ∈ Icc 0 σ, HasDerivAt (fun r => y r ^ 2 + u r ^ 2 / P r)
      (2 * y r * v r + (2 * u r * ((χ - c ^ 2 * r ^ 2) * y r) * P r
        - u r ^ 2 * ((-(2 * r)) * (χ - c ^ 2 * r ^ 2) + (1 - r ^ 2) * (-(c ^ 2 * (2 * r))))) / P r ^ 2) r := by
    intro r hr
    obtain ⟨h1, -, h3⟩ := hs r (hsub r hr)
    have hPd : HasDerivAt P ((-(2 * r)) * (χ - c ^ 2 * r ^ 2) + (1 - r ^ 2) * (-(c ^ 2 * (2 * r)))) r := by
      have a := (hasDerivAt_pow 2 r).const_sub 1
      have b := ((hasDerivAt_pow 2 r).const_mul (c ^ 2)).const_sub χ
      refine (a.mul b).congr_deriv ?_
      simp only [Nat.cast_ofNat]; ring
    have := (h1.pow 2).add ((h3.pow 2).div hPd (hP0 r hr).ne')
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Pi.pow_apply]; ring
  have hm := monotoneOn_of_deriv hd fun r hr => by
    obtain ⟨-, h2, -⟩ := hs r (hsub r hr)
    obtain ⟨hp, hq'⟩ := hpos r hr
    have hP' := hP0 r hr
    have hv : v r = -(u r) / (1 - r ^ 2) := by field_simp; linarith
    have e := sonin_alg (y := y r) (u := u r) (r := r) (c := c) (χ := χ) hp.ne' hq'.ne' hv
    simp only [hP] at e ⊢
    rw [e]
    have := hr.1
    have h1 : 0 ≤ 2 * r * (χ - c ^ 2 * r ^ 2) + 2 * r * c ^ 2 * (1 - r ^ 2) := by positivity
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [sq_nonneg (u r)]
  intro r hr
  have h := hm hr ⟨hσ0, le_rfl⟩ hr.2
  simp only at h
  have : 0 ≤ u r ^ 2 / P r := div_nonneg (sq_nonneg _) (hP0 r hr).le
  simp only [hP] at h this
  linarith

/-! ### The bound on `[0, 1]` -/

/-- **The regular solution is bounded by its depth**: with `D = c² − χ > 0`, `c²τ² = χ` and `0 ≤ σ < τ < 1`, every
`t ∈ [0, 1]` has `y(t)² ≤ e^{2D(1 − τ)}(1 + D²(1 − τ)²/c²)·e^{c(1 + c²/D)(τ − σ)}·(1 + c²/((1 − σ²)(χ − c²σ²)))`. -/
theorem sq_le (hs : IsSys c χ y v u) (hc : 0 < c) {σ : ℝ} (hσ0 : 0 ≤ σ) (hστ : σ < τ) (hτ1 : τ < 1)
    (hτχ : c ^ 2 * τ ^ 2 = χ) (hD : 0 < c ^ 2 - χ) (hy0 : ∀ t ∈ Icc τ 1, 0 ≤ y t)
    (hu0 : ∀ t ∈ Icc τ 1, 0 ≤ u t) (hy1 : y 1 = 1) (hu1 : u 1 = 0) (hv1 : v 1 = -(c ^ 2 - χ) / 2) :
    ∀ t ∈ Icc (0 : ℝ) 1, y t ^ 2 ≤ Real.exp (2 * ((c ^ 2 - χ) * (1 - τ))) * (1 + ((c ^ 2 - χ) * (1 - τ)) ^ 2 / c ^ 2)
      * Real.exp (c * (1 + c ^ 2 / (c ^ 2 - χ)) * (τ - σ))
      * (1 + c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2))) := by
  set D := c ^ 2 - χ
  have hτ0 : 0 ≤ τ := hσ0.trans hστ.le
  obtain ⟨hF1, hF2, hF3⟩ := forbidden hs hτ0 hτ1.le hy0 hu0 hy1 hu1 hv1 hD.le
  set Y := Real.exp (2 * (D * (1 - τ)))
  set B := 1 + (D * (1 - τ)) ^ 2 / c ^ 2
  set E := Real.exp (c * (1 + c ^ 2 / D) * (τ - σ))
  have hqσ : 0 < χ - c ^ 2 * σ ^ 2 := by
    have : σ ^ 2 < τ ^ 2 := pow_lt_pow_left₀ hστ hσ0 two_ne_zero
    have : c ^ 2 * σ ^ 2 < c ^ 2 * τ ^ 2 := mul_lt_mul_of_pos_left this (by positivity)
    linarith
  have hσ1 : σ < 1 := hστ.trans hτ1
  have hpσ : 0 < 1 - σ ^ 2 := by nlinarith
  set R := 1 + c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2))
  have hyτ0 : 0 ≤ y τ := hy0 τ ⟨le_rfl, hτ1.le⟩
  have hYτ : y τ ^ 2 ≤ Y := by
    have := pow_le_pow_left₀ hyτ0 hF2 2
    rw [← Real.exp_nat_mul] at this
    simpa [Y, mul_comm] using this
  have hY1 : 1 ≤ Y := Real.one_le_exp (by have := hτ1.le; positivity)
  have hB1 : 1 ≤ B := by
    have : 0 ≤ (D * (1 - τ)) ^ 2 / c ^ 2 := by positivity
    linarith
  have hE1 : 1 ≤ E := Real.one_le_exp (by
    have : 0 ≤ τ - σ := by linarith
    positivity)
  have hR1 : 1 ≤ R := by
    have : 0 ≤ c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)) := by positivity
    linarith
  -- the energy at `τ`
  have huτ0 : 0 ≤ u τ := hu0 τ ⟨le_rfl, hτ1.le⟩
  have hFτ : y τ ^ 2 + u τ ^ 2 / c ^ 2 ≤ Y * B := by
    have h1 : u τ ^ 2 ≤ (D * (1 - τ)) ^ 2 * y τ ^ 2 := by
      have := pow_le_pow_left₀ huτ0 hF3 2
      nlinarith
    have h2 : u τ ^ 2 / c ^ 2 ≤ (D * (1 - τ)) ^ 2 / c ^ 2 * y τ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]; linarith
    have : y τ ^ 2 + u τ ^ 2 / c ^ 2 ≤ B * y τ ^ 2 := by simp only [B]; nlinarith
    nlinarith
  have hN := near hs hc hσ0 hστ.le hτ1 hτχ hD
  have hFr : ∀ r ∈ Icc σ τ, y r ^ 2 + u r ^ 2 / c ^ 2 ≤ Y * B * E := by
    intro r hr
    refine (hN r hr).trans ?_
    have hEr : Real.exp (c * (1 + c ^ 2 / D) * (τ - r)) ≤ E := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ c * (1 + c ^ 2 / D) := by positivity
      nlinarith [hr.1]
    exact mul_le_mul hFτ hEr (Real.exp_pos _).le (by positivity)
  intro t ht
  rcases le_or_gt τ t with htτ | htτ
  · -- forbidden zone
    have h := hF1 t ⟨htτ, ht.2⟩
    have := pow_le_pow_left₀ (hy0 t ⟨htτ, ht.2⟩) h 2
    calc y t ^ 2 ≤ Y := this.trans hYτ
      _ = Y * 1 * 1 * 1 := by ring
      _ ≤ Y * B * E * R := by gcongr
  rcases le_or_gt σ t with htσ | htσ
  · -- near the turning point
    have h := hFr t ⟨htσ, htτ.le⟩
    have : 0 ≤ u t ^ 2 / c ^ 2 := by positivity
    calc y t ^ 2 ≤ Y * B * E := by linarith
      _ = Y * B * E * 1 := by ring
      _ ≤ Y * B * E * R := by gcongr
  · -- Sonin
    have hS := sonin_le hs hσ0 hσ1 hqσ t ⟨ht.1, htσ.le⟩
    have hFσ := hFr σ ⟨le_rfl, hστ.le⟩
    have hu2 : u σ ^ 2 ≤ c ^ 2 * (Y * B * E) := by
      have : u σ ^ 2 / c ^ 2 ≤ Y * B * E := by nlinarith [sq_nonneg (y σ)]
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have hy2 : y σ ^ 2 ≤ Y * B * E := by
      have : 0 ≤ u σ ^ 2 / c ^ 2 := by positivity
      linarith
    have hPσ : 0 < (1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2) := mul_pos hpσ hqσ
    have h3 : u σ ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2))
        ≤ Y * B * E * (c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2))) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hPσ]; linarith
    calc y t ^ 2 ≤ y σ ^ 2 + u σ ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)) := hS
      _ ≤ Y * B * E + Y * B * E * (c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2))) := add_le_add hy2 h3
      _ = Y * B * E * R := by simp only [R]; ring

end Cvs.Prolate.RegularSolutionDepthBound
