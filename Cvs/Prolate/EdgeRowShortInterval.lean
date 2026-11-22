import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge row on `[1, b]`, `1 ≤ b ≤ 2`

One integration by parts of `ψ(nθ) = −(U(nθ))′/(n q(nθ))`, `U = (ξ² − 1)ψ′`, against `ψ(θ)` on `[1, b]`: for `n ≥ 2`,
`q ≥ κc²ξ²` on `ξ ≥ 2`, `|ψ′(ξ)| ≤ D/ξ` there, `|ψ| ≤ A` on `[1, b]` and `∫_1^b|ψ′| ≤ A₁`:
`|∫_1^b ψ(θ)ψ(nθ)| ≤ D(6A/κ + 2A₁/κ + 2A/κ²)/(c²n²)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.EdgeRowShortInterval

/-- **The edge row.** -/
theorem abs_integral_edge_le {ψ v v' : ℝ → ℝ} {c χ n b A A₁ D κ : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ)
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hn : 2 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (hc : 0 < c) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hq : ∀ ξ, 2 ≤ ξ → κ * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ)
    (hA : ∀ θ ∈ Icc (1 : ℝ) b, |ψ θ| ≤ A) (hA₁ : ∫ θ in (1 : ℝ)..b, |v θ| ≤ A₁)
    (hD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    |∫ θ in (1 : ℝ)..b, ψ θ * ψ (n * θ)| ≤ D * (6 * A / κ + 2 * A₁ / κ + 2 * A / κ ^ 2) / (c ^ 2 * n ^ 2) := by
  have hn0 : 0 < n := by linarith
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  have hvcont : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv ξ).continuousAt
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 1 ⟨le_rfl, hb1⟩)
  have hD0 : 0 ≤ D := by
    have h := hD 2 le_rfl
    have : 0 ≤ D / 2 := le_trans (abs_nonneg _) h
    linarith
  set q : ℝ → ℝ := fun ξ => c ^ 2 * ξ ^ 2 - χ with hqd
  set U : ℝ → ℝ := fun ξ => (ξ ^ 2 - 1) * v ξ with hUd
  have hUd' : ∀ ξ, HasDerivAt U (-(q ξ * ψ ξ)) ξ := fun ξ => by
    have hp : HasDerivAt (fun ξ : ℝ => ξ ^ 2 - 1) (2 * ξ) ξ := by
      simpa using (hasDerivAt_pow 2 ξ).sub_const 1
    refine (hp.mul (hv ξ)).congr_deriv ?_
    simp only [hqd]; linarith [hode ξ]
  have hI : ∀ θ ∈ Icc (1 : ℝ) b, 2 ≤ n * θ := fun θ hθ => by nlinarith [hθ.1]
  have hqpos : ∀ θ ∈ Icc (1 : ℝ) b, κ * c ^ 2 * (n * θ) ^ 2 ≤ q (n * θ) := fun θ hθ => hq _ (hI θ hθ)
  have hqn0 : ∀ θ ∈ Icc (1 : ℝ) b, 0 < q (n * θ) := fun θ hθ =>
    lt_of_lt_of_le (by have := hI θ hθ; positivity) (hqpos θ hθ)
  -- the product `H = ψ(θ)U(nθ)/(n q(nθ))`
  set H : ℝ → ℝ := fun θ => ψ θ * U (n * θ) / (n * q (n * θ)) with hHd
  set H' : ℝ → ℝ := fun θ => v θ * U (n * θ) / (n * q (n * θ)) - ψ θ * ψ (n * θ)
      - ψ θ * U (n * θ) * (2 * c ^ 2 * n * θ) / (q (n * θ)) ^ 2 with hH'd
  have hHd' : ∀ θ ∈ uIcc (1 : ℝ) b, HasDerivAt H (H' θ) θ := fun θ hθ => by
    rw [uIcc_of_le hb1] at hθ
    have hq0 := (hqn0 θ hθ).ne'
    have hlin : HasDerivAt (fun θ => n * θ) n θ := by simpa using (hasDerivAt_id θ).const_mul n
    have hUn := (hUd' (n * θ)).comp θ hlin
    have hqn : HasDerivAt (fun θ => q (n * θ)) (2 * c ^ 2 * n ^ 2 * θ) θ := by
      have : HasDerivAt q (2 * c ^ 2 * (n * θ)) (n * θ) := by
        have h := ((hasDerivAt_pow 2 (n * θ)).const_mul (c ^ 2)).sub_const χ
        refine h.congr_deriv ?_
        push_cast; ring
      refine (this.comp θ hlin).congr_deriv ?_; ring
    have hden : HasDerivAt (fun θ => n * q (n * θ)) (n * (2 * c ^ 2 * n ^ 2 * θ)) θ := hqn.const_mul n
    have := ((hψ θ).mul hUn).div hden (mul_ne_zero hn0.ne' hq0)
    refine this.congr_deriv ?_
    simp only [hH'd, Pi.mul_apply, Function.comp_apply]
    field_simp
    ring
  have hcontH' : ContinuousOn H' (uIcc (1 : ℝ) b) := by
    rw [uIcc_of_le hb1]
    have cU : Continuous U := ((continuous_id.pow 2).sub continuous_const).mul hvcont
    have cq : Continuous q := (continuous_const.mul (continuous_id.pow 2)).sub continuous_const
    have cn : Continuous fun θ : ℝ => n * θ := continuous_const.mul continuous_id
    simp only [hH'd]
    refine ((ContinuousOn.div ((hvcont.mul (cU.comp cn)).continuousOn) ((continuous_const.mul (cq.comp cn)).continuousOn)
      fun θ hθ => mul_ne_zero hn0.ne' (hqn0 θ hθ).ne').sub ((hψc.mul (hψc.comp cn)).continuousOn)).sub
      (ContinuousOn.div (((hψc.mul (cU.comp cn)).mul (continuous_const.mul continuous_id)).continuousOn)
        (((cq.comp cn).pow 2).continuousOn) fun θ hθ => pow_ne_zero 2 (hqn0 θ hθ).ne')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hHd' hcontH'.intervalIntegrable
  -- the pieces of `H'` and their bounds
  have cU : Continuous U := ((continuous_id.pow 2).sub continuous_const).mul hvcont
  have cq : Continuous q := (continuous_const.mul (continuous_id.pow 2)).sub continuous_const
  have cn : Continuous fun θ : ℝ => n * θ := continuous_const.mul continuous_id
  set P1 : ℝ → ℝ := fun θ => v θ * U (n * θ) / (n * q (n * θ)) with hP1
  set P3 : ℝ → ℝ := fun θ => ψ θ * U (n * θ) * (2 * c ^ 2 * n * θ) / (q (n * θ)) ^ 2 with hP3
  have hI12 : uIcc (1 : ℝ) b = Icc 1 b := uIcc_of_le hb1
  have c1 : ContinuousOn P1 (uIcc (1 : ℝ) b) := by
    rw [hI12]
    exact ContinuousOn.div ((hvcont.mul (cU.comp cn)).continuousOn) ((continuous_const.mul (cq.comp cn)).continuousOn)
      fun θ hθ => mul_ne_zero hn0.ne' (hqn0 θ hθ).ne'
  have c3 : ContinuousOn P3 (uIcc (1 : ℝ) b) := by
    rw [hI12]
    exact ContinuousOn.div (((hψc.mul (cU.comp cn)).mul (continuous_const.mul continuous_id)).continuousOn)
      (((cq.comp cn).pow 2).continuousOn) fun θ hθ => pow_ne_zero 2 (hqn0 θ hθ).ne'
  have c2 : Continuous fun θ => ψ θ * ψ (n * θ) := hψc.mul (hψc.comp cn)
  have hsplit : ∫ θ in (1 : ℝ)..b, H' θ
      = (∫ θ in (1 : ℝ)..b, P1 θ) - (∫ θ in (1 : ℝ)..b, ψ θ * ψ (n * θ)) - ∫ θ in (1 : ℝ)..b, P3 θ := by
    simp only [hH'd]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub]
    · exact c1.intervalIntegrable
    · exact c2.intervalIntegrable _ _
    · exact c1.intervalIntegrable.sub (c2.intervalIntegrable _ _)
    · exact c3.intervalIntegrable
  -- `|U(nθ)| ≤ 2Dn` and `q(nθ) ≥ κc²n²` on `[1, 2]`
  have hUb : ∀ θ ∈ Icc (1 : ℝ) b, |U (n * θ)| ≤ D * (n * θ) := fun θ hθ => by
    have h2 := hI θ hθ
    have hξ0 : 0 < n * θ := by linarith
    simp only [hUd]
    rw [abs_mul, abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ (n * θ) ^ 2 - 1)]
    calc ((n * θ) ^ 2 - 1) * |v (n * θ)| ≤ (n * θ) ^ 2 * (D / (n * θ)) :=
          mul_le_mul (by linarith) (hD _ h2) (abs_nonneg _) (by positivity)
      _ = D * (n * θ) := by field_simp
  have hqb : ∀ θ ∈ Icc (1 : ℝ) b, κ * c ^ 2 * n ^ 2 * θ ^ 2 ≤ q (n * θ) := fun θ hθ => by
    have := hqpos θ hθ; nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hK : 0 < κ * c ^ 2 * n ^ 2 := by positivity
  -- the boundary
  have hHb : ∀ θ ∈ Icc (1 : ℝ) b, |H θ| ≤ 2 * A * D / (κ * c ^ 2 * n ^ 2) := fun θ hθ => by
    have hθ1 : 1 ≤ θ := hθ.1
    have hθ0 : 0 < θ := by linarith
    have hq := hqb θ hθ
    have hq0 := hqn0 θ hθ
    simp only [hHd]
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hn0 hq0)]
    have h1 : |ψ θ| * |U (n * θ)| ≤ A * (D * (n * θ)) :=
      mul_le_mul (hA θ hθ) (hUb θ hθ) (abs_nonneg _) hA0
    have hden : n * (κ * c ^ 2 * n ^ 2 * θ ^ 2) ≤ n * q (n * θ) := mul_le_mul_of_nonneg_left hq hn0.le
    calc |ψ θ| * |U (n * θ)| / (n * q (n * θ)) ≤ A * (D * (n * θ)) / (n * (κ * c ^ 2 * n ^ 2 * θ ^ 2)) :=
          div_le_div₀ (by positivity) h1 (by positivity) hden
      _ = A * D / (κ * c ^ 2 * n ^ 2) / θ := by field_simp
      _ ≤ A * D / (κ * c ^ 2 * n ^ 2) := div_le_self (by positivity) hθ1
      _ ≤ 2 * A * D / (κ * c ^ 2 * n ^ 2) := by
          exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hA0 hD0]) (by positivity)
  -- the first piece
  have hP1b : ∀ θ ∈ Icc (1 : ℝ) b, |P1 θ| ≤ 2 * D / (κ * c ^ 2 * n ^ 2) * |v θ| := fun θ hθ => by
    have hθ1 : 1 ≤ θ := hθ.1
    have hθ0 : 0 < θ := by linarith
    have hq := hqb θ hθ
    have hq0 := hqn0 θ hθ
    simp only [hP1]
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hn0 hq0)]
    have h1 : |v θ| * |U (n * θ)| ≤ |v θ| * (D * (n * θ)) := mul_le_mul_of_nonneg_left (hUb θ hθ) (abs_nonneg _)
    have hden : n * (κ * c ^ 2 * n ^ 2 * θ ^ 2) ≤ n * q (n * θ) := mul_le_mul_of_nonneg_left hq hn0.le
    calc |v θ| * |U (n * θ)| / (n * q (n * θ)) ≤ |v θ| * (D * (n * θ)) / (n * (κ * c ^ 2 * n ^ 2 * θ ^ 2)) :=
          div_le_div₀ (by positivity) h1 (by positivity) hden
      _ = D / (κ * c ^ 2 * n ^ 2) * |v θ| / θ := by field_simp
      _ ≤ D / (κ * c ^ 2 * n ^ 2) * |v θ| := div_le_self (by positivity) hθ1
      _ ≤ 2 * D / (κ * c ^ 2 * n ^ 2) * |v θ| := by
          have : D / (κ * c ^ 2 * n ^ 2) ≤ 2 * D / (κ * c ^ 2 * n ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  -- the third piece
  have hP3b : ∀ θ ∈ Icc (1 : ℝ) b, |P3 θ| ≤ 2 * A * D / (κ ^ 2 * c ^ 2 * n ^ 2) := fun θ hθ => by
    have hθ1 : 1 ≤ θ := hθ.1
    have hq := hqb θ hθ
    have hq0 := hqn0 θ hθ
    simp only [hP3]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (pow_pos hq0 2), abs_of_pos (by positivity : (0 : ℝ) < 2 * c ^ 2 * n * θ),
      div_le_div_iff₀ (pow_pos hq0 2) (by positivity)]
    have h1 : |ψ θ| * |U (n * θ)| * (2 * c ^ 2 * n * θ) ≤ A * (D * (n * θ)) * (2 * c ^ 2 * n * θ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hA θ hθ) (hUb θ hθ) (abs_nonneg _) hA0) (by positivity)
    have hq2 : (κ * c ^ 2 * n ^ 2 * θ ^ 2) ^ 2 ≤ q (n * θ) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
    have hθ2 : 1 ≤ θ ^ 2 := by nlinarith
    have e : A * (D * (n * θ)) * (2 * c ^ 2 * n * θ) * (κ ^ 2 * c ^ 2 * n ^ 2)
        = 2 * A * D * ((κ * c ^ 2 * n ^ 2 * θ ^ 2) ^ 2) / θ ^ 2 := by field_simp
    have h2 : A * (D * (n * θ)) * (2 * c ^ 2 * n * θ) * (κ ^ 2 * c ^ 2 * n ^ 2) ≤ 2 * A * D * q (n * θ) ^ 2 := by
      rw [e]
      calc 2 * A * D * ((κ * c ^ 2 * n ^ 2 * θ ^ 2) ^ 2) / θ ^ 2 ≤ 2 * A * D * ((κ * c ^ 2 * n ^ 2 * θ ^ 2) ^ 2) :=
            div_le_self (by positivity) hθ2
        _ ≤ 2 * A * D * q (n * θ) ^ 2 := mul_le_mul_of_nonneg_left hq2 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ κ ^ 2 * c ^ 2 * n ^ 2)]
  -- integrate
  have hP1i : |∫ θ in (1 : ℝ)..b, P1 θ| ≤ 2 * D / (κ * c ^ 2 * n ^ 2) * A₁ := by
    calc |∫ θ in (1 : ℝ)..b, P1 θ| ≤ ∫ θ in (1 : ℝ)..b, |P1 θ| :=
          intervalIntegral.abs_integral_le_integral_abs hb1
      _ ≤ ∫ θ in (1 : ℝ)..b, 2 * D / (κ * c ^ 2 * n ^ 2) * |v θ| := by
          apply intervalIntegral.integral_mono_on hb1 c1.abs.intervalIntegrable
            ((hvcont.abs.intervalIntegrable _ _).const_mul _)
          exact hP1b
      _ = 2 * D / (κ * c ^ 2 * n ^ 2) * ∫ θ in (1 : ℝ)..b, |v θ| := intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * D / (κ * c ^ 2 * n ^ 2) * A₁ := mul_le_mul_of_nonneg_left hA₁ (by positivity)
  have hP3i : |∫ θ in (1 : ℝ)..b, P3 θ| ≤ 2 * A * D / (κ ^ 2 * c ^ 2 * n ^ 2) := by
    calc |∫ θ in (1 : ℝ)..b, P3 θ| ≤ ∫ θ in (1 : ℝ)..b, |P3 θ| :=
          intervalIntegral.abs_integral_le_integral_abs hb1
      _ ≤ ∫ θ in (1 : ℝ)..b, 2 * A * D / (κ ^ 2 * c ^ 2 * n ^ 2) := by
          apply intervalIntegral.integral_mono_on hb1 c3.abs.intervalIntegrable intervalIntegrable_const
          exact hP3b
      _ ≤ 2 * A * D / (κ ^ 2 * c ^ 2 * n ^ 2) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          have h0 : 0 ≤ 2 * A * D / (κ ^ 2 * c ^ 2 * n ^ 2) := by positivity
          nlinarith
  have hH1 := hHb 1 ⟨le_rfl, hb1⟩
  have hH2 := hHb b ⟨hb1, le_rfl⟩
  have hmain : ∫ θ in (1 : ℝ)..b, ψ θ * ψ (n * θ)
      = (∫ θ in (1 : ℝ)..b, P1 θ) - (∫ θ in (1 : ℝ)..b, P3 θ) - (H b - H 1) := by
    have h := hFTC
    rw [hsplit] at h
    linarith
  rw [hmain]
  have hκ2 : κ ^ 2 ≤ κ := by nlinarith
  have e1 : 2 * A * D / (κ * c ^ 2 * n ^ 2) = D * (2 * A / κ) / (c ^ 2 * n ^ 2) := by field_simp
  have e2 : 2 * D / (κ * c ^ 2 * n ^ 2) * A₁ = D * (2 * A₁ / κ) / (c ^ 2 * n ^ 2) := by field_simp
  have e3 : 2 * A * D / (κ ^ 2 * c ^ 2 * n ^ 2) = D * (2 * A / κ ^ 2) / (c ^ 2 * n ^ 2) := by field_simp
  have e4 : D * (6 * A / κ + 2 * A₁ / κ + 2 * A / κ ^ 2) / (c ^ 2 * n ^ 2)
      = 3 * (D * (2 * A / κ) / (c ^ 2 * n ^ 2)) + D * (2 * A₁ / κ) / (c ^ 2 * n ^ 2)
        + D * (2 * A / κ ^ 2) / (c ^ 2 * n ^ 2) := by field_simp; ring
  rw [e4]
  rw [e1] at hH1 hH2
  rw [e2] at hP1i
  rw [e3] at hP3i
  have h0 : 0 ≤ D * (2 * A / κ) / (c ^ 2 * n ^ 2) := by positivity
  calc |(∫ θ in (1 : ℝ)..b, P1 θ) - (∫ θ in (1 : ℝ)..b, P3 θ) - (H b - H 1)|
      ≤ |∫ θ in (1 : ℝ)..b, P1 θ| + |∫ θ in (1 : ℝ)..b, P3 θ| + (|H b| + |H 1|) := by
        have a1 := abs_sub ((∫ θ in (1 : ℝ)..b, P1 θ) - (∫ θ in (1 : ℝ)..b, P3 θ)) (H b - H 1)
        have a2 := abs_sub (∫ θ in (1 : ℝ)..b, P1 θ) (∫ θ in (1 : ℝ)..b, P3 θ)
        have a3 := abs_sub (H b) (H 1)
        linarith
    _ ≤ _ := by linarith

end Cvs.Prolate.EdgeRowShortInterval
