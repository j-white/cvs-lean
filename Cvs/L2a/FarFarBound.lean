import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarIntegrationByParts
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far-far bound `‖wK(wΦ)‖² ≤ (C_η/c)·∫_{Ioi 1} Φ²` on the rung span

`R = A₁/Q + A₂/Q² + A₃/Q³` (Cvs.L2a.FarIntegrationByParts) expands in `σ² = c² − χ` over `Q₀ = Q|_{σ=0}`, so `I(y) = ∫_{3/2}^∞ wΦe^{icxy}`
is `Σ_k ∫ e R⁽ᵏ⁾Φ_k` with `Φ_k = Σ aₙσₙ^{2k}ψₙ`, `‖Φ_k‖ ≤ c^{2k}√P` (Cvs.Prolate.RungExactOrthogonality), and `|I(y)| ≤ η(y)√P` with
`η = N₁/(1 − ρ) + N₂/(1 − ρ)² + N₃/(1 − ρ)³`, `N_j = ‖A_j/|Q₀|ʲ‖_{L²(3/2,∞)}`. Truncation and the `L²` limit
(Cvs.Upstream.CosineTransformHalfLine) give `calK(wΦ) = √(2c/π) Re I` a.e., hence the bound for any `B ≥ η` with `(2c/π)∫ w²B² ≤ C_η/c`.
-/

namespace Cvs.L2a.FarFarBound

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts

/-! ### The atoms of `R` and the expansion in `σ²` -/

/-- The first atom `A₁ = (2x + 2icy p)w′ + p w″`. -/
noncomputable def aA₁ (c y x : ℝ) : ℂ :=
  (2 * (x : ℂ) + 2 * Complex.I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)) * (wF₁ x : ℂ)
    + ((pP x : ℝ) : ℂ) * (wF₂ x : ℂ)

/-- The second atom `A₂ = −((2x + 2icy p)Q′ + pQ″)w − 2pQ′w′`. -/
noncomputable def aA₂ (c y x : ℝ) : ℂ :=
  -(((2 * (x : ℂ) + 2 * Complex.I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)) * qQ₁ c y x
      + ((pP x : ℝ) : ℂ) * qQ₂ c y) * (wF x : ℂ))
    - 2 * ((pP x : ℝ) : ℂ) * qQ₁ c y x * (wF₁ x : ℂ)

/-- The third atom `A₃ = 2pQ′²w`. -/
noncomputable def aA₃ (c y x : ℝ) : ℂ := 2 * ((pP x : ℝ) : ℂ) * qQ₁ c y x ^ 2 * (wF x : ℂ)

/-- `Q₀ = Q` at `χ = c²`, i.e. at `σ = 0`. -/
noncomputable def qQ₀ (c y x : ℝ) : ℂ := qQ c (c ^ 2) y x

/-- The `k`-th coefficient `R⁽ᵏ⁾ = A₁/Q₀^{k+1} + (k+1)A₂/Q₀^{k+2} + C(k+2,2)A₃/Q₀^{k+3}` of `R` in powers of `σ²`. -/
noncomputable def rK (c y : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  aA₁ c y x / qQ₀ c y x ^ (k + 1) + ((k + 1).choose 1 : ℂ) * aA₂ c y x / qQ₀ c y x ^ (k + 2)
    + ((k + 2).choose 2 : ℂ) * aA₃ c y x / qQ₀ c y x ^ (k + 3)

/-- `R = A₁/Q + A₂/Q² + A₃/Q³` wherever `Q ≠ 0`. -/
theorem rR_eq {c χ y x : ℝ} (hQ : qQ c χ y x ≠ 0) :
    rR wF wF₁ wF₂ c χ y x
      = aA₁ c y x / qQ c χ y x + aA₂ c y x / qQ c χ y x ^ 2 + aA₃ c y x / qQ c χ y x ^ 3 := by
  unfold rR gW₁ gW₂ aA₁ aA₂ aA₃
  field_simp
  ring

/-- `Q = Q₀ − σ²`. -/
theorem qQ_eq (c χ y x : ℝ) : qQ c χ y x = qQ₀ c y x - ((c ^ 2 - χ : ℝ) : ℂ) := by
  unfold qQ₀ qQ; push_cast; ring

/-- `|Q₀| ≥ (5/4)c²(y² − 1)` for `x ≥ 3/2`. -/
theorem norm_qQ₀_ge {c y x : ℝ} (hx : 3 / 2 ≤ x) (hy : 1 ≤ y) :
    c ^ 2 * (5 / 4 * (y ^ 2 - 1)) ≤ ‖qQ₀ c y x‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [qQ₀, qQ_re]
  have h1 : 5 / 4 ≤ x ^ 2 - 1 := by nlinarith
  have h2 : 0 ≤ y ^ 2 - 1 := by nlinarith
  have h3 : 0 ≤ c ^ 2 * (y ^ 2 - 1) := by positivity
  nlinarith

/-- The ratio `ρ = 1/((5/4)(y² − 1))` of the geometric expansion. -/
noncomputable def rho (y : ℝ) : ℝ := 4 / (5 * (y ^ 2 - 1))

/-- For `y ≥ 3/2`, `0 < ρ ≤ 16/25`. -/
theorem rho_pos_le {y : ℝ} (hy : 3 / 2 ≤ y) : 0 < rho y ∧ rho y ≤ 16 / 25 := by
  have h : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  unfold rho
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

/-- `c² ≤ ρ|Q₀|` for `x, y ≥ 3/2`. -/
theorem sq_le_rho_mul {c y x : ℝ} (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y) : c ^ 2 ≤ rho y * ‖qQ₀ c y x‖ := by
  have h : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hQ := norm_qQ₀_ge (c := c) hx (by linarith : (1 : ℝ) ≤ y)
  have hr : 0 < rho y := (rho_pos_le hy).1
  calc c ^ 2 = rho y * (c ^ 2 * (5 / 4 * (y ^ 2 - 1))) := by unfold rho; field_simp
    _ ≤ rho y * ‖qQ₀ c y x‖ := mul_le_mul_of_nonneg_left hQ hr.le

/-- **The expansion of `R` in powers of `σ² = c² − χ`**: `R = Σ_k σ^{2k} R⁽ᵏ⁾` for `x, y ≥ 3/2`, `0 ≤ χ ≤ c²`. -/
theorem hasSum_rR {c χ y x : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hx : 3 / 2 ≤ x)
    (hy : 3 / 2 ≤ y) :
    HasSum (fun k : ℕ => ((c ^ 2 - χ : ℝ) : ℂ) ^ k * rK c y k x) (rR wF wF₁ wF₂ c χ y x) := by
  set Q₀ := qQ₀ c y x with hQ₀
  set s : ℂ := ((c ^ 2 - χ : ℝ) : ℂ) with hs
  have hρ := rho_pos_le hy
  have hcQ := sq_le_rho_mul (c := c) hx hy
  have hc2 : 0 < c ^ 2 := by positivity
  have hQpos : 0 < ‖Q₀‖ := by
    by_contra h
    have : ‖Q₀‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [this, mul_zero] at hcQ; linarith
  have hQ0 : Q₀ ≠ 0 := norm_pos_iff.mp hQpos
  have hsn : ‖s‖ ≤ c ^ 2 := by
    rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  set r := s / Q₀ with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, norm_div, div_lt_one hQpos]
    calc ‖s‖ ≤ c ^ 2 := hsn
      _ ≤ rho y * ‖Q₀‖ := hcQ
      _ < 1 * ‖Q₀‖ := by gcongr; linarith
      _ = ‖Q₀‖ := one_mul _
  have hQ : qQ c χ y x = Q₀ * (1 - r) := by
    rw [qQ_eq, ← hQ₀, ← hs, hr]; field_simp
  have h1r : (1 : ℂ) - r ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hr1; exact lt_irrefl _ hr1
  have hQne : qQ c χ y x ≠ 0 := by rw [hQ]; exact mul_ne_zero hQ0 h1r
  have h0 := (hasSum_choose_mul_geometric_of_norm_lt_one 0 hr1).mul_left (aA₁ c y x / Q₀)
  have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr1).mul_left (aA₂ c y x / Q₀ ^ 2)
  have h2 := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hr1).mul_left (aA₃ c y x / Q₀ ^ 3)
  have hsum := (h0.add h1).add h2
  have hfun : (fun k : ℕ => s ^ k * rK c y k x) = fun b : ℕ =>
      aA₁ c y x / Q₀ * (((b + 0).choose 0 : ℕ) * r ^ b) + aA₂ c y x / Q₀ ^ 2 * (((b + 1).choose 1 : ℕ) * r ^ b)
        + aA₃ c y x / Q₀ ^ 3 * (((b + 2).choose 2 : ℕ) * r ^ b) := by
    funext k
    simp only [rK, hr, div_pow, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, ← hQ₀]
    field_simp
    ring
  have hval : rR wF wF₁ wF₂ c χ y x = aA₁ c y x / Q₀ * (1 / (1 - r) ^ (0 + 1))
      + aA₂ c y x / Q₀ ^ 2 * (1 / (1 - r) ^ (1 + 1)) + aA₃ c y x / Q₀ ^ 3 * (1 / (1 - r) ^ (2 + 1)) := by
    rw [rR_eq hQne, hQ]; field_simp; ring
  rw [hfun, hval]; exact hsum

/-! ### The profiles `|A_j|/|Q₀|ʲ` -/

/-- The first profile `|A₁|/|Q₀|`. -/
noncomputable def prof₁ (c y x : ℝ) : ℝ := ‖aA₁ c y x‖ / ‖qQ₀ c y x‖

/-- The second profile `|A₂|/|Q₀|²`. -/
noncomputable def prof₂ (c y x : ℝ) : ℝ := ‖aA₂ c y x‖ / ‖qQ₀ c y x‖ ^ 2

/-- The third profile `|A₃|/|Q₀|³`. -/
noncomputable def prof₃ (c y x : ℝ) : ℝ := ‖aA₃ c y x‖ / ‖qQ₀ c y x‖ ^ 3

/-- The `k`-th weighted profile `ρᵏ(|A₁|/|Q₀| + (k+1)|A₂|/|Q₀|² + C(k+2,2)|A₃|/|Q₀|³)`. -/
noncomputable def profK (c y : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  rho y ^ k * (prof₁ c y x + ((k + 1).choose 1 : ℝ) * prof₂ c y x + ((k + 2).choose 2 : ℝ) * prof₃ c y x)

/-- **The coefficient bound**: `|R⁽ᵏ⁾| |t|ᵏ ≤ ρᵏ(|A₁|/|Q₀| + (k+1)|A₂|/|Q₀|² + C(k+2,2)|A₃|/|Q₀|³)` for
`|t| ≤ c²` and `x, y ≥ 3/2`. -/
theorem norm_rK_mul_le {c y x t : ℝ} (k : ℕ) (hc : 0 < c) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y)
    (ht : |t| ≤ c ^ 2) : ‖rK c y k x‖ * |t| ^ k ≤ profK c y k x := by
  have hcQ := sq_le_rho_mul (c := c) hx hy
  have hρ := rho_pos_le hy
  set q := ‖qQ₀ c y x‖ with hq
  have hc2 : 0 < c ^ 2 := by positivity
  have hq0 : 0 < q := by
    by_contra h
    have : q = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [this, mul_zero] at hcQ; linarith
  have hR : ‖rK c y k x‖ ≤ (prof₁ c y x + ((k + 1).choose 1 : ℝ) * prof₂ c y x
      + ((k + 2).choose 2 : ℝ) * prof₃ c y x) / q ^ k := by
    unfold rK
    refine (norm_add₃_le).trans (le_of_eq ?_)
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, prof₁, prof₂, prof₃, ← hq]
    field_simp
    ring
  have ht' : |t| ^ k ≤ rho y ^ k * q ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg t) (ht.trans hcQ) k
  have hP : 0 ≤ prof₁ c y x + ((k + 1).choose 1 : ℝ) * prof₂ c y x + ((k + 2).choose 2 : ℝ) * prof₃ c y x := by
    unfold prof₁ prof₂ prof₃; positivity
  calc ‖rK c y k x‖ * |t| ^ k
      ≤ (prof₁ c y x + ((k + 1).choose 1 : ℝ) * prof₂ c y x + ((k + 2).choose 2 : ℝ) * prof₃ c y x) / q ^ k
        * (rho y ^ k * q ^ k) := mul_le_mul hR ht' (by positivity) (by positivity)
    _ = profK c y k x := by unfold profK; field_simp

/-- The second derivative of the ramp is measurable. -/
theorem measurable_wF₂ : Measurable wF₂ := by
  unfold wF₂; exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

/-- The atoms and `Q₀` are measurable. -/
theorem measurable_atoms (c y : ℝ) :
    Measurable (aA₁ c y) ∧ Measurable (aA₂ c y) ∧ Measurable (aA₃ c y) ∧ Measurable (qQ₀ c y) := by
  have h2 := measurable_wF₂
  have h0 := continuous_wF.1.measurable
  have h1 := continuous_wF.2.measurable
  have hQ₁ := (continuous_qQ c (c ^ 2) y).2.measurable
  refine ⟨?_, ?_, ?_, (continuous_qQ c (c ^ 2) y).1.measurable⟩
  · unfold aA₁ pP; fun_prop
  · unfold aA₂ pP qQ₂; fun_prop
  · unfold aA₃ pP; fun_prop

/-- The profiles are measurable. -/
theorem measurable_prof (c y : ℝ) :
    Measurable (prof₁ c y) ∧ Measurable (prof₂ c y) ∧ Measurable (prof₃ c y) := by
  obtain ⟨h1, h2, h3, hQ⟩ := measurable_atoms c y
  refine ⟨?_, ?_, ?_⟩
  · unfold prof₁; fun_prop
  · unfold prof₂; fun_prop
  · unfold prof₃; fun_prop

/-- The ramp is in `[0, 1]`, `|w′| ≤ π` and `|w″| ≤ 2π²`. -/
theorem wF_bounds (x : ℝ) : 0 ≤ wF x ∧ wF x ≤ 1 ∧ |wF₁ x| ≤ π ∧ |wF₂ x| ≤ 2 * π ^ 2 := by
  refine ⟨by unfold wF; positivity, ?_, ?_, ?_⟩
  · unfold wF; rw [sq_le_one_iff_abs_le_one]; exact abs_sin_le_one _
  · unfold wF₁; rw [abs_mul, abs_of_pos pi_pos]
    exact mul_le_of_le_one_right pi_pos.le (abs_sin_le_one _)
  · unfold wF₂; split_ifs
    · rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
    · simp; positivity

/-- `|2x + 2icy p| ≤ (2 + 2cy)x²` for `x ≥ 1`. -/
theorem norm_alpha_le {c y x : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) (hx : 1 ≤ x) :
    ‖2 * (x : ℂ) + 2 * Complex.I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)‖ ≤ (2 + 2 * (c * y)) * x ^ 2 := by
  have hp0 : 0 ≤ pP x := by unfold pP; nlinarith
  have hp : pP x ≤ x ^ 2 := by unfold pP; linarith
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two,
    abs_of_nonneg hp0, mul_one, abs_of_nonneg hc, abs_of_nonneg hy, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
  have hcy : 0 ≤ c * y := mul_nonneg hc hy
  nlinarith

/-- `|Q₀| ≥ (5/9)c²(y² − 1)x²` for `x ≥ 3/2`, `y ≥ 1`. -/
theorem norm_qQ₀_ge_sq {c y x : ℝ} (hx : 3 / 2 ≤ x) (hy : 1 ≤ y) :
    5 / 9 * c ^ 2 * (y ^ 2 - 1) * x ^ 2 ≤ ‖qQ₀ c y x‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [qQ₀, qQ_re]
  have h1 : 5 / 9 * x ^ 2 ≤ x ^ 2 - 1 := by nlinarith
  have h2 : 0 ≤ y ^ 2 - 1 := by nlinarith
  have h3 : 0 ≤ c ^ 2 * (y ^ 2 - 1) := by positivity
  nlinarith

/-- `|A₁|/|Q₀| ≤ C/x` on `(3/2, ∞)`; `A₁` vanishes on `(2, ∞)`. -/
theorem prof₁_le {c y : ℝ} (hc : 0 < c) (hy : 3 / 2 ≤ y) : ∃ C, ∀ x, 3 / 2 < x → prof₁ c y x ≤ C / x := by
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  set L := c ^ 2 * (5 / 4 * (y ^ 2 - 1))
  have hL : 0 < L := by positivity
  set M := (2 + 2 * (c * y)) * 4 * π + 4 * (2 * π ^ 2)
  refine ⟨2 * M / L, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rcases le_or_gt x 2 with hx2 | hx2
  · have hQ := norm_qQ₀_ge (c := c) hx.le (by linarith : (1 : ℝ) ≤ y)
    obtain ⟨-, -, hw₁, hw₂⟩ := wF_bounds x
    have hα := norm_alpha_le hc.le (by linarith : (0 : ℝ) ≤ y) (by linarith : (1 : ℝ) ≤ x)
    have hp0 : 0 ≤ pP x := by unfold pP; nlinarith
    have hp : pP x ≤ 4 := by unfold pP; nlinarith
    have hx4 : x ^ 2 ≤ 4 := by nlinarith
    have hA : ‖aA₁ c y x‖ ≤ M := by
      unfold aA₁
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0]
      have h1 : ‖2 * (x : ℂ) + 2 * Complex.I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)‖ * |wF₁ x|
          ≤ (2 + 2 * (c * y)) * 4 * π := by
        have hcy : 0 ≤ 2 + 2 * (c * y) := by nlinarith
        calc _ ≤ ((2 + 2 * (c * y)) * x ^ 2) * π := mul_le_mul hα hw₁ (abs_nonneg _) (by positivity)
          _ ≤ (2 + 2 * (c * y)) * 4 * π := by gcongr
      have h2 : pP x * |wF₂ x| ≤ 4 * (2 * π ^ 2) := mul_le_mul hp hw₂ (abs_nonneg _) (by norm_num)
      linarith
    unfold prof₁
    calc ‖aA₁ c y x‖ / ‖qQ₀ c y x‖ ≤ M / L := div_le_div₀ (by positivity) hA hL hQ
      _ = M / L * x / x := by field_simp
      _ ≤ M / L * 2 / x := by have : 0 ≤ M / L := by positivity
                              gcongr
      _ = 2 * M / L / x := by ring
  · have h := (wF_of_two_le hx2.le).2
    have h' : wF₂ x = 0 := by unfold wF₂; rw [ite_eq_right (not_le.mpr hx2)]
    have : aA₁ c y x = 0 := by unfold aA₁; rw [h, h']; simp
    unfold prof₁; rw [this, norm_zero, zero_div]; positivity

/-- `|A₂|/|Q₀|² ≤ C/x` on `(3/2, ∞)`. -/
theorem prof₂_le {c y : ℝ} (hc : 0 < c) (hy : 3 / 2 ≤ y) : ∃ C, ∀ x, 3 / 2 < x → prof₂ c y x ≤ C / x := by
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hcy : 0 ≤ c * y := by nlinarith
  set k := 5 / 9 * c ^ 2 * (y ^ 2 - 1)
  have hk : 0 < k := by positivity
  set E := 2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y
  set F := 2 * c ^ 2 * (y ^ 2 - 1)
  set A := 2 + 2 * (c * y)
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have hA0 : 0 ≤ A := by positivity
  set M := A * E + F + 2 * π * E
  refine ⟨M / k ^ 2, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hQ := norm_qQ₀_ge_sq (c := c) hx.le (by linarith : (1 : ℝ) ≤ y)
  obtain ⟨hw0, hw1, hw₁, -⟩ := wF_bounds x
  have hα := norm_alpha_le hc.le (by linarith : (0 : ℝ) ≤ y) hx1
  have hq1 := norm_qQ₁_le hc hx1 (by linarith : (1 : ℝ) ≤ y)
  have hq2 : ‖qQ₂ c y‖ = F := by
    unfold qQ₂; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp0 : 0 ≤ pP x := by unfold pP; nlinarith
  have hp : pP x ≤ x ^ 2 := by unfold pP; linarith
  have hx23 : x ^ 2 ≤ x ^ 3 := by nlinarith
  set a := ‖2 * (x : ℂ) + 2 * Complex.I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)‖
  set q1 := ‖qQ₁ c y x‖
  have hT1 : (a * q1 + pP x * F) * wF x ≤ (A * E + F) * x ^ 3 := by
    have h1 : a * q1 ≤ A * x ^ 2 * (E * x) := mul_le_mul hα hq1 (norm_nonneg _) (by positivity)
    have h2 : pP x * F ≤ x ^ 3 * F := mul_le_mul_of_nonneg_right (hp.trans hx23) hF
    calc (a * q1 + pP x * F) * wF x ≤ (a * q1 + pP x * F) * 1 :=
          mul_le_mul_of_nonneg_left hw1 (by positivity)
      _ ≤ A * x ^ 2 * (E * x) + x ^ 3 * F := by linarith
      _ = (A * E + F) * x ^ 3 := by ring
  have hT2 : 2 * pP x * q1 * |wF₁ x| ≤ 2 * π * E * x ^ 3 := by
    have h1 : pP x * q1 ≤ x ^ 2 * (E * x) := mul_le_mul hp hq1 (norm_nonneg _) (by positivity)
    calc 2 * pP x * q1 * |wF₁ x| = 2 * (pP x * q1) * |wF₁ x| := by ring
      _ ≤ 2 * (x ^ 2 * (E * x)) * π := by gcongr
      _ = 2 * π * E * x ^ 3 := by ring
  have hA2 : ‖aA₂ c y x‖ ≤ M * x ^ 3 := by
    unfold aA₂
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0,
      abs_of_nonneg hw0, Complex.norm_two]
    have h3 : ‖(2 * (x : ℂ) + 2 * Complex.I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)) * qQ₁ c y x
        + ((pP x : ℝ) : ℂ) * qQ₂ c y‖ ≤ a * q1 + pP x * F := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hq2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    have h4 := mul_le_mul_of_nonneg_right h3 hw0
    have : M * x ^ 3 = (A * E + F) * x ^ 3 + 2 * π * E * x ^ 3 := by ring
    linarith
  have hkx : 0 < k * x ^ 2 := by positivity
  unfold prof₂
  calc ‖aA₂ c y x‖ / ‖qQ₀ c y x‖ ^ 2 ≤ M * x ^ 3 / (k * x ^ 2) ^ 2 :=
        div_le_div₀ (by positivity) hA2 (by positivity) (pow_le_pow_left₀ hkx.le hQ 2)
    _ = M / k ^ 2 / x := by field_simp

/-- `|A₃|/|Q₀|³ ≤ C/x` on `(3/2, ∞)`. -/
theorem prof₃_le {c y : ℝ} (hc : 0 < c) (hy : 3 / 2 ≤ y) : ∃ C, ∀ x, 3 / 2 < x → prof₃ c y x ≤ C / x := by
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  set k := 5 / 9 * c ^ 2 * (y ^ 2 - 1)
  have hk : 0 < k := by positivity
  set E := 2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y
  have hE : 0 ≤ E := by have : 0 ≤ c * y := by nlinarith
                        positivity
  refine ⟨2 * E ^ 2 / k ^ 3, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hQ := norm_qQ₀_ge_sq (c := c) hx.le (by linarith : (1 : ℝ) ≤ y)
  obtain ⟨hw0, hw1, -, -⟩ := wF_bounds x
  have hq1 := norm_qQ₁_le hc hx1 (by linarith : (1 : ℝ) ≤ y)
  have hp0 : 0 ≤ pP x := by unfold pP; nlinarith
  have hp : pP x ≤ x ^ 2 := by unfold pP; linarith
  have hA3 : ‖aA₃ c y x‖ ≤ 2 * E ^ 2 * x ^ 4 := by
    unfold aA₃
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hp0, abs_of_nonneg hw0, Complex.norm_two]
    have h1 : ‖qQ₁ c y x‖ ^ 2 ≤ (E * x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq1 2
    calc 2 * pP x * ‖qQ₁ c y x‖ ^ 2 * wF x ≤ 2 * x ^ 2 * (E * x) ^ 2 * 1 := by gcongr
      _ = 2 * E ^ 2 * x ^ 4 := by ring
  have hkx : 0 < k * x ^ 2 := by positivity
  unfold prof₃
  calc ‖aA₃ c y x‖ / ‖qQ₀ c y x‖ ^ 3 ≤ 2 * E ^ 2 * x ^ 4 / (k * x ^ 2) ^ 3 :=
        div_le_div₀ (by positivity) hA3 (by positivity) (pow_le_pow_left₀ hkx.le hQ 3)
    _ = 2 * E ^ 2 / k ^ 3 / x / x := by field_simp
    _ ≤ 2 * E ^ 2 / k ^ 3 / x / 1 := by gcongr
    _ = 2 * E ^ 2 / k ^ 3 / x := by rw [div_one]

/-! ### `L²(3/2, ∞)` norms of the profiles -/

/-- A measurable `f` with `|f x| ≤ C/x` on `(3/2, ∞)` lies in `L²(3/2, ∞)`. -/
theorem memLp_of_le_inv {f : ℝ → ℝ} {C : ℝ} (hf : Measurable f) (h : ∀ x, 3 / 2 < x → |f x| ≤ C / x) :
    MemLp f 2 (volume.restrict (Ioi (3 / 2))) := by
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 3 / 2)).const_mul (C ^ 2)) (hf.pow_const 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.rpow_neg hx0.le, Real.rpow_two, ← sq_abs]
  calc |f x| ^ 2 ≤ (C / x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h x hx) 2
    _ = C ^ 2 * (x ^ 2)⁻¹ := by field_simp

/-- The three profiles lie in `L²(3/2, ∞)`. -/
theorem memLp_prof {c y : ℝ} (hc : 0 < c) (hy : 3 / 2 ≤ y) :
    MemLp (prof₁ c y) 2 (volume.restrict (Ioi (3 / 2))) ∧ MemLp (prof₂ c y) 2 (volume.restrict (Ioi (3 / 2)))
      ∧ MemLp (prof₃ c y) 2 (volume.restrict (Ioi (3 / 2))) := by
  obtain ⟨m1, m2, m3⟩ := measurable_prof c y
  obtain ⟨C₁, h1⟩ := prof₁_le hc hy
  obtain ⟨C₂, h2⟩ := prof₂_le hc hy
  obtain ⟨C₃, h3⟩ := prof₃_le hc hy
  refine ⟨memLp_of_le_inv (C := C₁) m1 fun x hx => ?_, memLp_of_le_inv (C := C₂) m2 fun x hx => ?_,
    memLp_of_le_inv (C := C₃) m3 fun x hx => ?_⟩
  · rw [abs_of_nonneg (by unfold prof₁; positivity)]; exact h1 x hx
  · rw [abs_of_nonneg (by unfold prof₂; positivity)]; exact h2 x hx
  · rw [abs_of_nonneg (by unfold prof₃; positivity)]; exact h3 x hx

/-- **Cauchy–Schwarz**: `∫ f|u| ≤ √(∫ f²) √(∫ u²)` for `f ≥ 0` and `f, u ∈ L²`. -/
theorem integral_mul_abs_le {μ : Measure ℝ} {f u : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemLp f 2 μ)
    (hu : MemLp u 2 μ) : ∫ x, f x * |u x| ∂μ ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, u x ^ 2 ∂μ) := by
  have hua : MemLp (fun x => |u x|) 2 μ := hu.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall fun x => abs_nonneg (u x))
    (by rw [ENNReal.ofReal_ofNat]; exact hf) (by rw [ENNReal.ofReal_ofNat]; exact hua)
  simp only [Real.rpow_two, sq_abs] at h
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- The `L²(3/2, ∞)` norm `N(f) = (∫_{3/2}^∞ f²)^{1/2}`. -/
noncomputable def nN (f : ℝ → ℝ) : ℝ := √(∫ x in Ioi (3 / 2 : ℝ), f x ^ 2)

/-- The pointwise far-far profile `η(y) = N₁/(1 − ρ) + N₂/(1 − ρ)² + N₃/(1 − ρ)³`. -/
noncomputable def etaProfile (c y : ℝ) : ℝ :=
  nN (prof₁ c y) / (1 - rho y) + nN (prof₂ c y) / (1 - rho y) ^ 2 + nN (prof₃ c y) / (1 - rho y) ^ 3

/-- `|u| · profK` is integrable on `(3/2, ∞)` for `u ∈ L²`, with integral
`ρᵏ(∫|u|prof₁ + (k+1)∫|u|prof₂ + C(k+2,2)∫|u|prof₃)`. -/
theorem integral_mul_profK {c y : ℝ} (hc : 0 < c) (hy : 3 / 2 ≤ y) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioi (3 / 2)))) (k : ℕ) :
    IntegrableOn (fun x => |u x| * profK c y k x) (Ioi (3 / 2))
      ∧ ∫ x in Ioi (3 / 2 : ℝ), |u x| * profK c y k x
        = rho y ^ k * ((∫ x in Ioi (3 / 2 : ℝ), |u x| * prof₁ c y x)
          + ((k + 1).choose 1 : ℝ) * (∫ x in Ioi (3 / 2 : ℝ), |u x| * prof₂ c y x)
          + ((k + 2).choose 2 : ℝ) * ∫ x in Ioi (3 / 2 : ℝ), |u x| * prof₃ c y x) := by
  obtain ⟨m1, m2, m3⟩ := memLp_prof hc hy
  have i1 : Integrable (fun x => |u x| * prof₁ c y x) (volume.restrict (Ioi (3 / 2))) := hu.abs.integrable_mul m1
  have i2 : Integrable (fun x => |u x| * prof₂ c y x) (volume.restrict (Ioi (3 / 2))) := hu.abs.integrable_mul m2
  have i3 : Integrable (fun x => |u x| * prof₃ c y x) (volume.restrict (Ioi (3 / 2))) := hu.abs.integrable_mul m3
  have e : (fun x => |u x| * profK c y k x) = fun x => rho y ^ k * ((|u x| * prof₁ c y x
      + ((k + 1).choose 1 : ℝ) * (|u x| * prof₂ c y x)) + ((k + 2).choose 2 : ℝ) * (|u x| * prof₃ c y x)) := by
    funext x; unfold profK; ring
  have i12 : Integrable (fun x => |u x| * prof₁ c y x + ((k + 1).choose 1 : ℝ) * (|u x| * prof₂ c y x))
      (volume.restrict (Ioi (3 / 2))) := i1.add (i2.const_mul _)
  refine ⟨?_, ?_⟩
  · rw [e]; exact (i12.add (i3.const_mul _)).const_mul _
  · rw [e, integral_const_mul, integral_add i12 (i3.const_mul _), integral_add i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul]

/-- `∫_{3/2}^∞ |u| · profK ≤ ρᵏ(N₁ + (k+1)N₂ + C(k+2,2)N₃) ‖u‖₂`. -/
theorem integral_mul_profK_le {c y : ℝ} (hc : 0 < c) (hy : 3 / 2 ≤ y) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioi (3 / 2)))) (k : ℕ) :
    ∫ x in Ioi (3 / 2 : ℝ), |u x| * profK c y k x
      ≤ rho y ^ k * (nN (prof₁ c y) + ((k + 1).choose 1 : ℝ) * nN (prof₂ c y)
          + ((k + 2).choose 2 : ℝ) * nN (prof₃ c y)) * √(∫ x in Ioi (3 / 2 : ℝ), u x ^ 2) := by
  obtain ⟨m1, m2, m3⟩ := memLp_prof hc hy
  rw [(integral_mul_profK hc hy hu k).2]
  have hρ := (rho_pos_le hy).1
  have cs : ∀ f : ℝ → ℝ, (∀ x, 0 ≤ f x) → MemLp f 2 (volume.restrict (Ioi (3 / 2))) →
      ∫ x in Ioi (3 / 2 : ℝ), |u x| * f x ≤ nN f * √(∫ x in Ioi (3 / 2 : ℝ), u x ^ 2) := by
    intro f hf0 hf
    have h := integral_mul_abs_le hf0 hf hu
    simp only [mul_comm (|u _|)] at h ⊢
    exact h
  have c1 := cs _ (fun x => by unfold prof₁; positivity) m1
  have c2 := cs _ (fun x => by unfold prof₂; positivity) m2
  have c3 := cs _ (fun x => by unfold prof₃; positivity) m3
  have hC1 : (0 : ℝ) ≤ ((k + 1).choose 1 : ℝ) := by positivity
  have hC2 : (0 : ℝ) ≤ ((k + 2).choose 2 : ℝ) := by positivity
  have := add_le_add (add_le_add c1 (mul_le_mul_of_nonneg_left c2 hC1)) (mul_le_mul_of_nonneg_left c3 hC2)
  calc _ ≤ rho y ^ k * (nN (prof₁ c y) * √(∫ x in Ioi (3 / 2 : ℝ), u x ^ 2)
        + ((k + 1).choose 1 : ℝ) * (nN (prof₂ c y) * √(∫ x in Ioi (3 / 2 : ℝ), u x ^ 2))
        + ((k + 2).choose 2 : ℝ) * (nN (prof₃ c y) * √(∫ x in Ioi (3 / 2 : ℝ), u x ^ 2))) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- The three geometric series in `ρ`: `Σρᵏ = 1/(1 − ρ)`, `Σ(k+1)ρᵏ = 1/(1 − ρ)²`, `ΣC(k+2,2)ρᵏ = 1/(1 − ρ)³`. -/
theorem hasSum_rho {y : ℝ} (hy : 3 / 2 ≤ y) :
    HasSum (fun k : ℕ => rho y ^ k) (1 / (1 - rho y))
      ∧ HasSum (fun k : ℕ => ((k + 1).choose 1 : ℝ) * rho y ^ k) (1 / (1 - rho y) ^ 2)
      ∧ HasSum (fun k : ℕ => ((k + 2).choose 2 : ℝ) * rho y ^ k) (1 / (1 - rho y) ^ 3) := by
  have hρ := rho_pos_le hy
  have h1 : ‖rho y‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hρ.1]; linarith [hρ.2]
  refine ⟨?_, hasSum_choose_mul_geometric_of_norm_lt_one 1 h1, hasSum_choose_mul_geometric_of_norm_lt_one 2 h1⟩
  simpa using hasSum_choose_mul_geometric_of_norm_lt_one 0 h1

/-- `R⁽ᵏ⁾` is measurable. -/
theorem measurable_rK (c y : ℝ) (k : ℕ) : Measurable (rK c y k) := by
  obtain ⟨h1, h2, h3, hQ⟩ := measurable_atoms c y
  unfold rK; fun_prop

/-- A rung lies in `L²(3/2, ∞)`. -/
theorem memLp_psi_far {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) : MemLp (psi c g) 2 (volume.restrict (Ioi (3 / 2))) :=
  (Cvs.Prolate.RungExactOrthogonality.memLp_psi hg hg₁ hg₂c hang hc).mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi (by norm_num)) le_rfl)

/-- `|e ψ R⁽ᵏ⁾| ≤ |ψ| · profK/|t|ᵏ`, in the form `|t|ᵏ |e ψ R⁽ᵏ⁾| ≤ |ψ| · profK`. -/
theorem norm_eψrK_le {c y x t : ℝ} (k : ℕ) (hc : 0 < c) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y) (ht : |t| ≤ c ^ 2)
    (v : ℝ) : |t| ^ k * ‖eF c y x * (v : ℂ) * rK c y k x‖ ≤ |v| * profK c y k x := by
  rw [norm_mul, norm_mul, (continuous_eF c y).2, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |t| ^ k * (|v| * ‖rK c y k x‖) = |v| * (‖rK c y k x‖ * |t| ^ k) := by ring
    _ ≤ |v| * profK c y k x := mul_le_mul_of_nonneg_left (norm_rK_mul_le k hc hx hy ht) (abs_nonneg _)

/-- **The per-rung expansion**: `∫_{3/2}^∞ eψR = Σ_k σ^{2k} ∫_{3/2}^∞ eψR⁽ᵏ⁾`, the series converging absolutely. -/
theorem hasSum_integral_rung {g g₁ g₂ : ℝ → ℝ} {c χ y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hy : 3 / 2 ≤ y) :
    HasSum (fun k : ℕ => ((c ^ 2 - χ : ℝ) : ℂ) ^ k * ∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c g x : ℂ) * rK c y k x)
      (∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x) := by
  obtain ⟨-, -, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  have hψ2 := memLp_psi_far hg hg₁ hg₂c hang hc
  set s : ℂ := ((c ^ 2 - χ : ℝ) : ℂ) with hs_def
  have hs : |c ^ 2 - χ| ≤ c ^ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  set F : ℕ → ℝ → ℂ := fun k x => s ^ k * (eF c y x * (psi c g x : ℂ) * rK c y k x) with hF
  have hFb : ∀ k, ∀ x ∈ Ioi (3 / 2 : ℝ), ‖F k x‖ ≤ |psi c g x| * profK c y k x := by
    intro k x hx
    have h := norm_eψrK_le k hc (le_of_lt hx) hy hs (psi c g x)
    simp only [F, norm_mul, norm_pow, hs_def, Complex.norm_real, Real.norm_eq_abs] at h ⊢
    calc |c ^ 2 - χ| ^ k * (‖eF c y x‖ * |psi c g x| * ‖rK c y k x‖) = _ := by ring
      _ ≤ _ := h
  have hFm : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (Ioi (3 / 2))) := fun k => by
    have h1 := (continuous_eF c y).1.measurable
    have h2 := hψc.measurable
    have h3 := measurable_rK c y k
    have : Measurable (F k) := by simp only [F]; fun_prop
    exact this.aestronglyMeasurable
  have hFi : ∀ k, Integrable (F k) (volume.restrict (Ioi (3 / 2))) := fun k =>
    Integrable.mono' (integral_mul_profK hc hy hψ2 k).1 (hFm k)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hFb k)))
  have hFs : Summable (fun k => ∫ x in Ioi (3 / 2 : ℝ), ‖F k x‖) := by
    obtain ⟨g0, g1, g2⟩ := hasSum_rho hy
    set J₁ := ∫ x in Ioi (3 / 2 : ℝ), |psi c g x| * prof₁ c y x
    set J₂ := ∫ x in Ioi (3 / 2 : ℝ), |psi c g x| * prof₂ c y x
    set J₃ := ∫ x in Ioi (3 / 2 : ℝ), |psi c g x| * prof₃ c y x
    have hsum : Summable (fun k : ℕ => rho y ^ k * J₁ + ((k + 1).choose 1 : ℝ) * rho y ^ k * J₂
        + ((k + 2).choose 2 : ℝ) * rho y ^ k * J₃) :=
      ((g0.summable.mul_right J₁).add (g1.summable.mul_right J₂)).add (g2.summable.mul_right J₃)
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) (fun k => ?_) hsum
    calc ∫ x in Ioi (3 / 2 : ℝ), ‖F k x‖ ≤ ∫ x in Ioi (3 / 2 : ℝ), |psi c g x| * profK c y k x :=
          setIntegral_mono_on (hFi k).norm (integral_mul_profK hc hy hψ2 k).1 measurableSet_Ioi (hFb k)
      _ = _ := by rw [(integral_mul_profK hc hy hψ2 k).2]; ring
  have key := hasSum_integral_of_summable_integral_norm hFi hFs
  have e1 : (fun k => ∫ x in Ioi (3 / 2 : ℝ), F k x)
      = fun k : ℕ => s ^ k * ∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c g x : ℂ) * rK c y k x := by
    funext k; simp only [F]; rw [integral_const_mul]
  have e2 : ∫ x in Ioi (3 / 2 : ℝ), ∑' k, F k x
      = ∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have h := (hasSum_rR hc hχ0 hχc (le_of_lt hx) hy).mul_left (eF c y x * (psi c g x : ℂ))
    have hfun : (fun k => F k x) = fun k : ℕ => eF c y x * (psi c g x : ℂ) * (s ^ k * rK c y k x) := by
      funext k; simp only [F]; ring
    rw [hfun]; exact h.tsum_eq
  rw [e1, e2] at key
  exact key

/-! ### The bound on `I(y)` for the span -/

/-- **The pointwise far-far bound**: for rungs with distinct `χᵢ ∈ [0, c²]` and `y ≥ 3/2`,
`|Σᵢ aᵢ ∫_{3/2}^∞ eψᵢRᵢ| ≤ η(y) (∫_{Ioi 1} Φ²)^{1/2}`, `Φ = Σᵢ aᵢψᵢ`. -/
theorem norm_farI_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {y : ℝ} (hy : 3 / 2 ≤ y) :
    ‖∑ i, (a i : ℂ) * ∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c (g i) x : ℂ) * rR wF wF₁ wF₂ c (χ i) y x‖
      ≤ etaProfile c y * √(∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2) := by
  classical
  set P := ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 with hP
  have hc2 : 0 < c ^ 2 := by positivity
  set J : ι → ℕ → ℂ := fun i k => ∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c (g i) x : ℂ) * rK c y k x
  have hS : HasSum (fun k : ℕ => ∑ i, (a i : ℂ) * (((c ^ 2 - χ i : ℝ) : ℂ) ^ k * J i k))
      (∑ i, (a i : ℂ) * ∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c (g i) x : ℂ) * rR wF wF₁ wF₂ c (χ i) y x) :=
    hasSum_sum fun i _ => (hasSum_integral_rung (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχc i) hy).mul_left _
  set N₁ := nN (prof₁ c y)
  set N₂ := nN (prof₂ c y)
  set N₃ := nN (prof₃ c y)
  -- the bound for each `k`
  have hk : ∀ k : ℕ, ‖∑ i, (a i : ℂ) * (((c ^ 2 - χ i : ℝ) : ℂ) ^ k * J i k)‖
      ≤ rho y ^ k * (N₁ + ((k + 1).choose 1 : ℝ) * N₂ + ((k + 2).choose 2 : ℝ) * N₃) * √P := by
    intro k
    set b : ι → ℝ := fun i => a i * ((c ^ 2 - χ i) / c ^ 2) ^ k with hb
    set v : ℝ → ℝ := fun x => ∑ i, b i * psi c (g i) x with hv
    have hψ2 := fun i => memLp_psi_far (hg i) (hg₁ i) (hg₂c i) (hang i) hc
    have hv2 : MemLp v 2 (volume.restrict (Ioi (3 / 2))) :=
      memLp_finsetSum _ fun i _ => (hψ2 i).const_mul (b i)
    have hcs : |c ^ 2| ≤ c ^ 2 := (abs_of_pos hc2).le
    have hint : ∀ i, Integrable (fun x => eF c y x * (psi c (g i) x : ℂ) * rK c y k x)
        (volume.restrict (Ioi (3 / 2))) := by
      intro i
      obtain ⟨-, -, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
      have hm : Measurable (fun x => eF c y x * (psi c (g i) x : ℂ) * rK c y k x) := by
        have h1 := (continuous_eF c y).1.measurable
        have h2 := hψc.measurable
        have h3 := measurable_rK c y k
        fun_prop
      refine Integrable.mono' ((integral_mul_profK hc hy (hψ2 i) k).1.div_const ((c ^ 2) ^ k))
        hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_))
      have h := norm_eψrK_le k hc (le_of_lt hx) hy hcs (psi c (g i) x)
      rw [abs_of_pos hc2] at h
      rw [le_div_iff₀ (by positivity)]; linarith
    -- the combination is one integral against `v`
    have hcomb : ∑ i, (a i : ℂ) * (((c ^ 2 - χ i : ℝ) : ℂ) ^ k * J i k)
        = ∫ x in Ioi (3 / 2 : ℝ), (((c ^ 2) ^ k : ℝ) : ℂ) * (eF c y x * (v x : ℂ) * rK c y k x) := by
      have e : ∀ x, (((c ^ 2) ^ k : ℝ) : ℂ) * (eF c y x * (v x : ℂ) * rK c y k x)
          = ∑ i, ((((c ^ 2) ^ k * b i : ℝ)) : ℂ) * (eF c y x * (psi c (g i) x : ℂ) * rK c y k x) := by
        intro x
        simp only [hv, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [e]
      rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, ← mul_assoc]
      congr 1
      have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
      simp only [hb]
      push_cast
      rw [div_pow]
      field_simp
    have hnorm : ‖∑ i, (a i : ℂ) * (((c ^ 2 - χ i : ℝ) : ℂ) ^ k * J i k)‖
        ≤ ∫ x in Ioi (3 / 2 : ℝ), |v x| * profK c y k x := by
      rw [hcomb]
      refine norm_integral_le_of_norm_le (integral_mul_profK hc hy hv2 k).1
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_))
      have h := norm_eψrK_le k hc (le_of_lt hx) hy hcs (v x)
      rw [abs_of_pos hc2] at h
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact h
    -- `∫_{3/2}^∞ v² ≤ P`
    have hvP : ∫ x in Ioi (3 / 2 : ℝ), v x ^ 2 ≤ P := by
      have hv1 : MemLp v 2 (volume.restrict (Ioi 1)) := memLp_finsetSum _ fun i _ =>
        (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (b i)
      have hvi : IntegrableOn (fun x => v x ^ 2) (Ioi 1) :=
        (memLp_two_iff_integrable_sq hv1.aestronglyMeasurable).mp hv1
      calc ∫ x in Ioi (3 / 2 : ℝ), v x ^ 2 ≤ ∫ x in Ioi 1, v x ^ 2 :=
            setIntegral_mono_set hvi (Eventually.of_forall fun x => sq_nonneg _)
              (Eventually.of_forall (Ioi_subset_Ioi (by norm_num)))
        _ = ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 :=
            Cvs.Prolate.RungExactOrthogonality.integral_span_sq b hg hg₁ hg₂c hang hc hχ
        _ ≤ ∑ i, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_
              (integral_nonneg fun _ => sq_nonneg _)
            have h0 : 0 ≤ (c ^ 2 - χ i) / c ^ 2 := div_nonneg (by linarith [hχc i]) hc2.le
            have h1 : (c ^ 2 - χ i) / c ^ 2 ≤ 1 := by rw [div_le_one hc2]; linarith [hχ0 i]
            have h2 : (((c ^ 2 - χ i) / c ^ 2) ^ k) ^ 2 ≤ 1 := pow_le_one₀ (by positivity)
              (pow_le_one₀ h0 h1)
            simp only [hb, mul_pow]
            nlinarith [sq_nonneg (a i)]
        _ = P := (Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ).symm
    refine hnorm.trans ((integral_mul_profK_le hc hy hv2 k).trans ?_)
    have hρ := (rho_pos_le hy).1
    have hN : 0 ≤ N₁ + ((k + 1).choose 1 : ℝ) * N₂ + ((k + 2).choose 2 : ℝ) * N₃ := by
      simp only [N₁, N₂, N₃, nN]; positivity
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvP) (by positivity)
  -- sum over `k`
  obtain ⟨g0, g1, g2⟩ := hasSum_rho hy
  have hG := (((g0.mul_right N₁).add (g1.mul_right N₂)).add (g2.mul_right N₃)).mul_right √P
  have ef : (fun k : ℕ => (rho y ^ k * N₁ + ((k + 1).choose 1 : ℝ) * rho y ^ k * N₂
      + ((k + 2).choose 2 : ℝ) * rho y ^ k * N₃) * √P)
      = fun k : ℕ => rho y ^ k * (N₁ + ((k + 1).choose 1 : ℝ) * N₂ + ((k + 2).choose 2 : ℝ) * N₃) * √P := by
    funext k; ring
  have ev : (1 / (1 - rho y) * N₁ + 1 / (1 - rho y) ^ 2 * N₂ + 1 / (1 - rho y) ^ 3 * N₃) * √P
      = etaProfile c y * √P := by
    unfold etaProfile; ring
  rw [ef, ev] at hG
  exact hS.norm_le_of_bounded hG hk

/-! ### The cosine transform of `wΦ` -/

/-- The ramp vanishes on `(−∞, 3/2]`. -/
theorem wF_eq_zero_of_le {x : ℝ} (hx : x ≤ 3 / 2) : wF x = 0 := by
  have h : clampW x = 3 / 2 := by unfold clampW; exact max_eq_left (min_le_of_left_le hx)
  unfold wF; rw [h]; simp

/-- `L²` convergence from convergence of `∫ ‖f n‖²` to `0`. -/
theorem tendsto_eLpNorm_two {μ : Measure ℝ} {f : ℕ → ℝ → ℂ} (hf : ∀ n, MemLp (f n) 2 μ)
    (h : Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (f n) 2 μ = ENNReal.ofReal ((∫ x, ‖f n x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := fun n => by
    rw [(hf n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [e]
  have h' : Tendsto (fun n => (∫ x, ‖f n x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
    have := h.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    rwa [Real.zero_rpow (by norm_num)] at this
  rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal h'

open Cvs.Upstream.CosineTransformHalfLine in
/-- **The cosine transform of `wΦ` is the far integral**: for rungs with `χᵢ ∈ [0, c²]`, a.e. on `(3/2, ∞)`,
`calK(wΦ)(y) = √(2c/π) Re Σᵢ aᵢ ∫_{3/2}^∞ eψᵢRᵢ`, via the truncations `1_{(3/2, n]} wΦ` and their `L²` limit. -/
theorem calK_far_ae_eq {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) :
    ∀ᵐ y ∂(volume.restrict (Ioi (3 / 2 : ℝ))),
      calK c (fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y
        = ((√(2 * c / π) * (∑ i, (a i : ℂ) * ∫ x in Ioi (3 / 2 : ℝ),
            eF c y x * (psi c (g i) x : ℂ) * rR wF wF₁ wF₂ c (χ i) y x).re : ℝ) : ℂ) := by
  classical
  set Φ : ℝ → ℝ := fun x => ∑ i, a i * psi c (g i) x with hΦ
  set hR : ℝ → ℝ := fun x => wF x * Φ x with hhR
  set I : ℝ → ℂ := fun y => ∑ i, (a i : ℂ) * ∫ x in Ioi (3 / 2 : ℝ),
    eF c y x * (psi c (g i) x : ℂ) * rR wF wF₁ wF₂ c (χ i) y x with hI
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous Φ := continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hRc : Continuous hR := continuous_wF.1.mul hΦc
  -- `wΦ ∈ L²(ℝ)`
  have hΦ1 : MemLp Φ 2 (volume.restrict (Ioi 1)) := memLp_finsetSum _ fun i _ =>
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hR2 : MemLp hR 2 volume := by
    have hind : MemLp ((Ioi (1 : ℝ)).indicator Φ) 2 volume :=
      (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hΦ1
    refine hind.of_le hRc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx]
      obtain ⟨h0, h1, -, -⟩ := wF_bounds x
      simp only [hhR, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1
    · have : wF x = 0 := wF_eq_zero_of_le (by linarith [(not_lt.mp hx : x ≤ 1)])
      simp [hhR, this]
  set μ0 := volume.restrict (Ioi (0 : ℝ))
  set h : ℕ → ℝ → ℝ := fun n => (Ioc (3 / 2 : ℝ) n).indicator hR with hh
  have hh2 : ∀ n, MemLp (h n) 2 μ0 := fun n => (hR2.indicator measurableSet_Ioc.nullMeasurableSet).restrict _
  have hhi : ∀ n, IntegrableOn (h n) (Ioi 0) := fun n =>
    ((integrable_indicator_iff measurableSet_Ioc).2
      (hRc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).integrableOn
  set H : ℝ → ℂ := fun x => ((hR x : ℝ) : ℂ) with hH
  set Hn : ℕ → ℝ → ℂ := fun n x => ((h n x : ℝ) : ℂ) with hHn
  have hH2 : MemLp H 2 μ0 := (hR2.restrict _).ofReal
  have hHn2 : ∀ n, MemLp (Hn n) 2 μ0 := fun n => (hh2 n).ofReal
  -- the truncations: the integral formula
  have hb : ∀ n, calK c (Hn n) =ᵐ[volume]
      fun y => ((√(2 * c / π) * ∫ x in Ioi 0, h n x * Real.cos (c * x * y) : ℝ) : ℂ) := fun n =>
    calK_ofReal_eq_integral hc (hh2 n) (hhi n)
  -- the truncations converge in `L²`
  have hD : ∀ n, calK c (Hn n) - calK c H =ᵐ[μ0] calK c (Hn n + (-1 : ℂ) • H) := fun n => by
    have h1 := calK_add hc (memLp_ev (hHn2 n)) (memLp_ev (hH2.const_smul (-1 : ℂ)))
    have h2 := calK_smul hc (-1 : ℂ) (memLp_ev hH2)
    refine ae_restrict_of_ae ?_
    filter_upwards [h1, h2] with y e1 e2
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hlimInt : Tendsto (fun n : ℕ => ∫ x, ‖(Hn n + (-1 : ℂ) • H) x‖ ^ 2 ∂μ0) atTop (𝓝 0) := by
    have hbd : Integrable (fun x => ‖H x‖ ^ 2) μ0 :=
      (memLp_two_iff_integrable_sq_norm hH2.aestronglyMeasurable).mp hH2
    have := tendsto_integral_of_dominated_convergence (μ := μ0) (fun x => ‖H x‖ ^ 2)
      (F := fun n x => ‖(Hn n + (-1 : ℂ) • H) x‖ ^ 2) (f := fun _ => 0)
      (fun n => ((((hHn2 n).add (hH2.const_smul (-1 : ℂ))).aestronglyMeasurable.norm).pow 2)) hbd
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simpa using this
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hHn, hh, hH]
      by_cases hx : x ∈ Ioc (3 / 2 : ℝ) n
      · rw [indicator_of_mem hx]; simp
      · rw [indicator_of_notMem hx]; simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      have hxn : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast hn)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hHn, hh, hH]
      by_cases hx : 3 / 2 < x
      · have hmem : x ∈ Ioc (3 / 2 : ℝ) n := ⟨hx, hxn⟩
        rw [indicator_of_mem hmem]; simp
      · rw [indicator_of_notMem fun (hm : x ∈ Ioc (3 / 2 : ℝ) n) => hx hm.1]
        have : wF x = 0 := wF_eq_zero_of_le (not_lt.mp hx)
        simp [hhR, this]
  have hL2 : Tendsto (fun n : ℕ => eLpNorm (calK c (Hn n) - calK c H) 2 μ0) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (calK c (Hn n) - calK c H) 2 μ0 = eLpNorm (calK c (Hn n + (-1 : ℂ) • H)) 2 μ0 :=
      fun n => eLpNorm_congr_ae (hD n)
    simp_rw [e]
    refine tendsto_eLpNorm_two (fun n => memLp_calK hc ((hHn2 n).add (hH2.const_smul (-1 : ℂ)))) ?_
    refine hlimInt.congr fun n => ?_
    exact (norm_calK hc ((hHn2 n).add (hH2.const_smul (-1 : ℂ)))).symm
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero
    hL2).exists_seq_tendsto_ae
  -- the improper integrals converge to `I y`
  have hIt : ∀ y, 3 / 2 ≤ y → Tendsto (fun T => ∫ x in (3 / 2 : ℝ)..T, (wF x : ℂ) * (Φ x : ℂ) * eF c y x)
      atTop (𝓝 (I y)) := by
    intro y hy
    have ht := tendsto_finsetSum Finset.univ fun i _ =>
      ((ibp_far (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) hy).2).const_mul (a i : ℂ)
    refine ht.congr fun T => ?_
    have hii : ∀ i, IntervalIntegrable (fun x => (a i : ℂ) * ((wF x : ℂ) * (psi c (g i) x : ℂ) * eF c y x))
        volume (3 / 2) T := fun i =>
      (continuous_const.mul (((Complex.continuous_ofReal.comp continuous_wF.1).mul
        (Complex.continuous_ofReal.comp (hψc i))).mul (continuous_eF c y).1)).intervalIntegrable _ _
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum fun i _ => hii i]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hΦ, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the truncated cosine integrals are real parts
  have hre : ∀ y, ∀ n : ℕ, 2 ≤ n → ∫ x in Ioi 0, h n x * Real.cos (c * x * y)
      = (∫ x in (3 / 2 : ℝ)..n, (wF x : ℂ) * (Φ x : ℂ) * eF c y x).re := by
    intro y n hn
    have hn' : (3 / 2 : ℝ) ≤ n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hint : IntervalIntegrable (fun x => (wF x : ℂ) * (Φ x : ℂ) * eF c y x) volume (3 / 2) n :=
      (((Complex.continuous_ofReal.comp continuous_wF.1).mul (Complex.continuous_ofReal.comp hΦc)).mul
        (continuous_eF c y).1).intervalIntegrable _ _
    rw [← RCLike.re_to_complex, ← intervalIntegral.intervalIntegral_re hint, intervalIntegral.integral_of_le hn']
    have e1 : (fun x => h n x * Real.cos (c * x * y))
        = (Ioc (3 / 2 : ℝ) n).indicator (fun x => hR x * Real.cos (c * x * y)) := by
      funext x
      by_cases hx : x ∈ Ioc (3 / 2 : ℝ) n
      · simp only [hh, indicator_of_mem hx]
      · simp only [hh, indicator_of_notMem hx, zero_mul]
    rw [e1, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [eF, hhR, RCLike.re_to_complex]
    rw [show ((wF x : ℂ) * (Φ x : ℂ)) = ((wF x * Φ x : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
    ring_nf
  -- conclude
  have hb' : ∀ᵐ y ∂volume, ∀ n, calK c (Hn n) y
      = ((√(2 * c / π) * ∫ x in Ioi 0, h n x * Real.cos (c * x * y) : ℝ) : ℂ) := ae_all_iff.2 hb
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 3 / 2)) hae,
    ae_restrict_of_ae hb'] with y hy hlim hcal
  have hy' : 3 / 2 ≤ y := le_of_lt hy
  have h2 : Tendsto (fun i => calK c (Hn (ns i)) y) atTop
      (𝓝 ((√(2 * c / π) * (I y).re : ℝ) : ℂ)) := by
    have hlim' : Tendsto (fun i => ((√(2 * c / π) *
        (∫ x in (3 / 2 : ℝ)..(ns i : ℝ), (wF x : ℂ) * (Φ x : ℂ) * eF c y x).re : ℝ) : ℂ)) atTop
        (𝓝 ((√(2 * c / π) * (I y).re : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (((Complex.continuous_re.continuousAt.tendsto.comp
          ((hIt y hy').comp (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop)))).const_mul _)
    refine hlim'.congr' ?_
    filter_upwards [hns.tendsto_atTop.eventually (eventually_ge_atTop 2)] with i hi
    rw [hcal (ns i), hre y (ns i) hi]
  exact tendsto_nhds_unique hlim h2

/-! ### The far-far bound -/

/-- The profile `η` is nonnegative for `y ≥ 3/2`. -/
theorem etaProfile_nonneg {c y : ℝ} (hy : 3 / 2 ≤ y) : 0 ≤ etaProfile c y := by
  have h := rho_pos_le hy
  have h1 : 0 < 1 - rho y := by linarith [h.2]
  unfold etaProfile nN; positivity

open Cvs.Upstream.CosineTransformHalfLine in
/-- **The far-far bound**: for rungs `ψᵢ = psi c gᵢ` with distinct `χᵢ ∈ [0, c²]`, `Φ = Σᵢ aᵢψᵢ`, the ramp `w` of
Cvs.L2a.FarIntegrationByParts and `K = 1_{(1,∞)} calK 1_{(1,∞)}`, `‖wK(wΦ)‖²_{L²(1,∞)} ≤ (C_η/c) ∫_{Ioi 1} Φ²` for any majorant `B ≥ η` on
`(3/2, ∞)` with `(2c/π)∫_{3/2}^∞ w²B² ≤ C_η/c`. -/
theorem farFar_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {Bm : ℝ → ℝ} {Cη : ℝ} (hBm : ∀ y, 3 / 2 < y → etaProfile c y ≤ Bm y)
    (hBi : IntegrableOn (fun y => wF y ^ 2 * Bm y ^ 2) (Ioi (3 / 2)))
    (hBint : 2 * c / π * (∫ y in Ioi (3 / 2 : ℝ), wF y ^ 2 * Bm y ^ 2) ≤ Cη / c) :
    ∫ y in Ioi 1, ‖(wF y : ℂ)
        * calK c ((Ioi 1).indicator fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ Cη / c * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  set P := ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 with hPdef
  have hP : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  have hind : ((Ioi 1).indicator fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ))
      = fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, wF_eq_zero_of_le (by linarith [(not_lt.mp hx : x ≤ 1)])]; simp
  rw [hind, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 3 / 2)) fun y hy => ?_]
  · have hbd : ∀ᵐ y ∂(volume.restrict (Ioi (3 / 2 : ℝ))),
        ‖(wF y : ℂ) * calK c (fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
          ≤ 2 * c / π * P * (wF y ^ 2 * Bm y ^ 2) := by
      filter_upwards [calK_far_ae_eq a hg hg₁ hg₂c hang hc hχ0, ae_restrict_mem measurableSet_Ioi]
        with y hy hy'
      have hy1 : 3 / 2 ≤ y := le_of_lt hy'
      rw [hy]
      set J := ∑ i, (a i : ℂ) * ∫ x in Ioi (3 / 2 : ℝ),
        eF c y x * (psi c (g i) x : ℂ) * rR wF wF₁ wF₂ c (χ i) y x
      have hJ := norm_farI_le a hg hg₁ hg₂c hang hc hχ hχ0 hχc hy1
      have hη := etaProfile_nonneg (c := c) hy1
      have hre : |J.re| ≤ Bm y * √P :=
        (Complex.abs_re_le_norm J).trans (hJ.trans
          (mul_le_mul_of_nonneg_right (hBm y hy') (Real.sqrt_nonneg _)))
      have hre2 : J.re ^ 2 ≤ Bm y ^ 2 * P := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hre 2
        rwa [sq_abs, mul_pow, Real.sq_sqrt hP] at h
      have hc' : 0 ≤ 2 * c / π := by positivity
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs,
        abs_mul, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hc']
      have hw : 0 ≤ wF y ^ 2 := sq_nonneg _
      calc wF y ^ 2 * (2 * c / π * J.re ^ 2) ≤ wF y ^ 2 * (2 * c / π * (Bm y ^ 2 * P)) := by gcongr
        _ = 2 * c / π * P * (wF y ^ 2 * Bm y ^ 2) := by ring
    calc ∫ y in Ioi (3 / 2 : ℝ),
          ‖(wF y : ℂ) * calK c (fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
        ≤ ∫ y in Ioi (3 / 2 : ℝ), 2 * c / π * P * (wF y ^ 2 * Bm y ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) (hBi.const_mul _) hbd
      _ = 2 * c / π * (∫ y in Ioi (3 / 2 : ℝ), wF y ^ 2 * Bm y ^ 2) * P := by
          rw [integral_const_mul]; ring
      _ ≤ Cη / c * P := mul_le_mul_of_nonneg_right hBint hP
  · have : wF y = 0 := wF_eq_zero_of_le (not_lt.mp hy.2)
    simp [this]

end Cvs.L2a.FarFarBound
