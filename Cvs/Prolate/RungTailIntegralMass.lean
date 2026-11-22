import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail integral of a rung against its mass

For `c ≥ 80`, `0 ≤ χ < c²`, `y ≥ 6/5`: `(u/q)' = −ψ − 2c²ξu/q²` (Cvs.Prolate.Gram.RungGramFloorAtInfinity), `|u| ≤ cξ√(6M)` (Cvs.Prolate.Envelope.RungCountEnvelope, Cvs.Prolate.ProlateWindowMassIdentity, Cvs.Prolate.RungConnectionIdentity)
and the primitive `−ξ/(ξ² − 1)` of `(ξ² + 1)/(ξ² − 1)²` give `|∫_y^∞ ψ| ≤ 3√6·√M·y/(c(y² − 1))`, `M = ∫₁^∞ ψ²`.
On a span `Φ = Σ bᵢψᵢ` with `P = Σ bᵢ²Mᵢ`: `|∫_y^∞ Φ| ≤ 3√(6J)·y/(c(y² − 1))·√P`, and with the edge strip
`(1, 6/5]` and `Σ_{m≥2} 1/(m² − 1) = 3/4`, `|Π₊(Φ)| ≤ C_π√P`, `C_π = 5^{−1/2} + (3√(6J)/c)(30/11 + 3/4)`.
-/

namespace Cvs.Prolate.RungTailIntegralMass

open Real Set Filter Topology MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FullTailPoleChannel

/-- Cauchy–Schwarz on an interval: `(∫_a^b f)² ≤ (b − a)∫_a^b f²`. -/
theorem sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hL : 0 < b - a := sub_pos.mpr hlt
  set I := ∫ x in a..b, f x with hI
  set m := I / (b - a) with hm
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b := (hf.pow 2).intervalIntegrable_of_Icc hab
  have h0 : 0 ≤ ∫ x in a..b, (f x - m) ^ 2 := intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have e : ∫ x in a..b, (f x - m) ^ 2 = (∫ x in a..b, f x ^ 2) - 2 * m * I + m ^ 2 * (b - a) := by
    have : (fun x => (f x - m) ^ 2) = fun x => (f x ^ 2 - 2 * m * f x) + m ^ 2 := by funext x; ring
    rw [this, intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hfi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have hmI : I = m * (b - a) := by rw [hm]; field_simp
  rw [hmI] at h0 ⊢
  nlinarith [mul_nonneg hL.le h0]

/-- `Σ_{m<N} 1/((m + 2)² − 1) = 3/4 − (1/(N + 1) + 1/(N + 2))/2`. -/
theorem sum_range_inv_sq_sub_one (N : ℕ) :
    ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2 - 1)
      = 3 / 4 - (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 2)) / 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h3 : ((N : ℝ) + 2) ^ 2 - 1 = ((N : ℝ) + 1) * ((N : ℝ) + 3) := by ring
    rw [h3]
    field_simp
    ring

/-- `Σ_{m<N} 1/((m + 2)² − 1) ≤ 3/4`. -/
theorem sum_range_inv_sq_sub_one_le (N : ℕ) :
    ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2 - 1) ≤ 3 / 4 := by
  rw [sum_range_inv_sq_sub_one]
  have : 0 ≤ (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 2)) / 2 := by positivity
  linarith

/-- `−ξ/(ξ² − 1)` is a primitive of `(ξ² + 1)/(ξ² − 1)²` on `ξ > 1`. -/
theorem hasDerivAt_neg_div {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (fun ξ : ℝ => -(ξ / (ξ ^ 2 - 1))) ((ξ ^ 2 + 1) / (ξ ^ 2 - 1) ^ 2) ξ := by
  have hp : ξ ^ 2 - 1 ≠ 0 := by nlinarith
  have h := ((hasDerivAt_id' ξ).div ((hasDerivAt_pow 2 ξ).sub_const 1) hp).neg
  refine h.congr_deriv ?_
  field_simp
  ring

section rung

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- The mass on `[1, X]` is at most the mass on `(1, ∞)`. -/
theorem integral_sq_le_mass (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    ∫ t in (1 : ℝ)..X, psi c g t ^ 2 ≤ ∫ t in Ioi 1, psi c g t ^ 2 := by
  have hint : IntegrableOn (fun t => psi c g t ^ 2) (Ioi 1) :=
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi hg hg₁ hg₂c hang hc).integrable_sq
  rw [intervalIntegral.integral_of_le hX]
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun t => sq_nonneg (psi c g t))
    (Filter.Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)

/-- **`|u| ≤ cξ√(6M)`** on `[6/5, ∞)`, `M = ∫₁^∞ ψ²`, for `c ≥ 80`, `0 ≤ χ < c²`. -/
theorem abs_rungU_le_mass (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) {ξ : ℝ} (hξ : 6 / 5 ≤ ξ) :
    |rungU c g ξ| ≤ c * ξ * √(6 * ∫ t in Ioi 1, psi c g t ^ 2) := by
  have hX : (2 : ℝ) ≤ max ξ 2 := le_max_right _ _
  have hξX : ξ ∈ Icc (6 / 5 : ℝ) (max ξ 2) := ⟨hξ, le_max_left _ _⟩
  have hξ1 : 1 < ξ := by linarith
  have hc0 : 0 < c := by linarith
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith
  have hR2 := Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp_sq_le hg hg₁ hg₂c hang hc hχ0 hχc hX hξX
  have hMX := integral_sq_le_mass hg hg₁ hg₂c hang hc0 (by linarith : (1 : ℝ) ≤ max ξ 2)
  set M := ∫ t in Ioi 1, psi c g t ^ 2 with hMdef
  have hR : Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g ξ ≤ √(6 * M / (ξ ^ 2 - 1)) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    exact hR2.trans (div_le_div_of_nonneg_right (by linarith) hp.le)
  have hu := Cvs.Prolate.Envelope.RungCountEnvelope.abs_rungU_le_rungAmp (g := g) hξ1 hc0 hχ0 hχc
  have e : √(ξ ^ 2 - 1) * √(6 * M / (ξ ^ 2 - 1)) = √(6 * M) := by
    rw [← Real.sqrt_mul hp.le]; congr 1; field_simp
  calc |rungU c g ξ| ≤ c * ξ * √(ξ ^ 2 - 1) * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g ξ := hu
    _ ≤ c * ξ * √(ξ ^ 2 - 1) * √(6 * M / (ξ ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ = c * ξ * √(6 * M) := by rw [mul_assoc, e]

/-- **`(u/q)' = −ψ − 2c²ξu/q²`** on `ξ > 1`, written for `−u/q`. -/
theorem hasDerivAt_neg_rungU_div (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (fun ξ => -(rungU c g ξ / qP c χ ξ))
      (psi c g ξ + 2 * c ^ 2 * ξ * rungU c g ξ / qP c χ ξ ^ 2) ξ := by
  have hq := qP_pos hξ (by positivity) hχc
  have hu := (rung_system hg hg₁ hg₂c hang).2.1 ξ
  have hqd : HasDerivAt (qP c χ) (2 * c ^ 2 * ξ) ξ := by
    have h := ((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ
    exact h.congr_deriv (by ring)
  refine (hu.div hqd hq.ne').neg.congr_deriv ?_
  field_simp
  ring

/-- **The tail integral on `[y, Y]`**: `|∫_y^Y ψ| ≤ 3√(6M)·y/(c(y² − 1))` for `6/5 ≤ y ≤ Y`. -/
theorem abs_integral_psi_le_mass (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) {y Y : ℝ} (hy : 6 / 5 ≤ y) (hyY : y ≤ Y) :
    |∫ ξ in y..Y, psi c g ξ| ≤ 3 * √(6 * ∫ t in Ioi 1, psi c g t ^ 2) * y / (c * (y ^ 2 - 1)) := by
  set S := √(6 * ∫ t in Ioi 1, psi c g t ^ 2) with hSdef
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hy1 : 1 < y := by linarith
  have hI : uIcc y Y = Icc y Y := uIcc_of_le hyY
  have hmem : ∀ ξ ∈ uIcc y Y, 1 < ξ := fun ξ hξ => lt_of_lt_of_le hy1 (hI ▸ hξ).1
  obtain ⟨-, -, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  -- the remainder `R = 2c²ξu/q²`
  set R : ℝ → ℝ := fun ξ => 2 * c ^ 2 * ξ * rungU c g ξ / qP c χ ξ ^ 2 with hRdef
  have hRc : ContinuousOn R (uIcc y Y) := by
    refine ((continuous_const.mul continuous_id).mul huc).continuousOn.div (hqc.pow 2).continuousOn ?_
    intro ξ hξ; exact pow_ne_zero 2 (qP_pos (hmem ξ hξ) hc2 hχc).ne'
  have hRi : IntervalIntegrable R volume y Y := hRc.intervalIntegrable
  have hψi : IntervalIntegrable (psi c g) volume y Y := hψc.intervalIntegrable _ _
  -- the exact identity `∫ψ = u(y)/q(y) − u(Y)/q(Y) − ∫R`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ξ hξ => hasDerivAt_neg_rungU_div hg hg₁ hg₂c hang hc0 hχc (hmem ξ hξ)) (hψi.add hRi)
  rw [intervalIntegral.integral_add hψi hRi] at hFTC
  have hid : ∫ ξ in y..Y, psi c g ξ
      = rungU c g y / qP c χ y - rungU c g Y / qP c χ Y - ∫ ξ in y..Y, R ξ := by linarith
  -- pointwise bounds
  have hquot : ∀ ξ, 6 / 5 ≤ ξ → |rungU c g ξ / qP c χ ξ| ≤ S * ξ / (c * (ξ ^ 2 - 1)) := by
    intro ξ hξ
    have hξ1 : 1 < ξ := by linarith
    have hp : 0 < ξ ^ 2 - 1 := by nlinarith
    have hq := qP_pos hξ1 hc2 hχc
    have hql : c ^ 2 * (ξ ^ 2 - 1) ≤ qP c χ ξ := by unfold qP; nlinarith
    have hu := abs_rungU_le_mass hg hg₁ hg₂c hang hc hχ0 hχc hξ
    rw [abs_div, abs_of_pos hq]
    calc |rungU c g ξ| / qP c χ ξ ≤ c * ξ * S / (c ^ 2 * (ξ ^ 2 - 1)) :=
          div_le_div₀ (by positivity) hu (by positivity) hql
      _ = S * ξ / (c * (ξ ^ 2 - 1)) := by field_simp
  have hRb : ∀ ξ ∈ Icc y Y, |R ξ| ≤ 2 * S / c * ((ξ ^ 2 + 1) / (ξ ^ 2 - 1) ^ 2) := by
    intro ξ hξ
    have hξ6 : 6 / 5 ≤ ξ := hy.trans hξ.1
    have hξ1 : 1 < ξ := by linarith
    have hp : 0 < ξ ^ 2 - 1 := by nlinarith
    have hq := qP_pos hξ1 hc2 hχc
    have hql : c ^ 2 * (ξ ^ 2 - 1) ≤ qP c χ ξ := by unfold qP; nlinarith
    have hu := abs_rungU_le_mass hg hg₁ hg₂c hang hc hχ0 hχc hξ6
    have hq2 : (c ^ 2 * (ξ ^ 2 - 1)) ^ 2 ≤ qP c χ ξ ^ 2 := pow_le_pow_left₀ (by positivity) hql 2
    have hnum : |2 * c ^ 2 * ξ * rungU c g ξ| ≤ 2 * c ^ 2 * ξ * (c * ξ * S) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * c ^ 2 * ξ)]
      exact mul_le_mul_of_nonneg_left hu (by positivity)
    simp only [hRdef]
    rw [abs_div, abs_of_pos (by positivity : 0 < qP c χ ξ ^ 2)]
    calc |2 * c ^ 2 * ξ * rungU c g ξ| / qP c χ ξ ^ 2
        ≤ 2 * c ^ 2 * ξ * (c * ξ * S) / (c ^ 2 * (ξ ^ 2 - 1)) ^ 2 :=
          div_le_div₀ (by positivity) hnum (by positivity) hq2
      _ = 2 * S / c * (ξ ^ 2 / (ξ ^ 2 - 1) ^ 2) := by field_simp
      _ ≤ 2 * S / c * ((ξ ^ 2 + 1) / (ξ ^ 2 - 1) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  -- the integral of the majorant
  have hGc : ContinuousOn (fun ξ : ℝ => (ξ ^ 2 + 1) / (ξ ^ 2 - 1) ^ 2) (uIcc y Y) := by
    refine (by fun_prop : Continuous fun ξ : ℝ => ξ ^ 2 + 1).continuousOn.div
      (by fun_prop : Continuous fun ξ : ℝ => (ξ ^ 2 - 1) ^ 2).continuousOn ?_
    intro ξ hξ; have := hmem ξ hξ; exact pow_ne_zero 2 (by nlinarith)
  have hG := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ hξ => hasDerivAt_neg_div (hmem ξ hξ))
    hGc.intervalIntegrable
  have hRint : |∫ ξ in y..Y, R ξ| ≤ 2 * S / c * (y / (y ^ 2 - 1) - Y / (Y ^ 2 - 1)) := by
    calc |∫ ξ in y..Y, R ξ| ≤ ∫ ξ in y..Y, |R ξ| := intervalIntegral.abs_integral_le_integral_abs hyY
      _ ≤ ∫ ξ in y..Y, 2 * S / c * ((ξ ^ 2 + 1) / (ξ ^ 2 - 1) ^ 2) := by
          refine intervalIntegral.integral_mono_on hyY hRi.abs ((hGc.intervalIntegrable).const_mul _) hRb
      _ = 2 * S / c * (y / (y ^ 2 - 1) - Y / (Y ^ 2 - 1)) := by
          rw [intervalIntegral.integral_const_mul, hG]; ring
  have hY6 : 6 / 5 ≤ Y := hy.trans hyY
  have hYp : 0 < Y ^ 2 - 1 := by nlinarith
  have hyp : 0 < y ^ 2 - 1 := by nlinarith
  have h1 := hquot y hy
  have h2 := hquot Y hY6
  rw [hid]
  have hYnn : 0 ≤ S * Y / (c * (Y ^ 2 - 1)) := by positivity
  have e1 : S * y / (c * (y ^ 2 - 1)) = S / c * (y / (y ^ 2 - 1)) := by field_simp
  have e2 : S * Y / (c * (Y ^ 2 - 1)) = S / c * (Y / (Y ^ 2 - 1)) := by field_simp
  have e3 : 3 * S * y / (c * (y ^ 2 - 1)) = 3 * (S / c * (y / (y ^ 2 - 1))) := by field_simp
  rw [e1] at h1; rw [e2] at h2 hYnn; rw [e3]
  calc |rungU c g y / qP c χ y - rungU c g Y / qP c χ Y - ∫ ξ in y..Y, R ξ|
      ≤ |rungU c g y / qP c χ y| + |rungU c g Y / qP c χ Y| + |∫ ξ in y..Y, R ξ| :=
        (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ S / c * (y / (y ^ 2 - 1)) + S / c * (Y / (Y ^ 2 - 1))
          + 2 * S / c * (y / (y ^ 2 - 1) - Y / (Y ^ 2 - 1)) := add_le_add (add_le_add h1 h2) hRint
    _ = 3 * (S / c * (y / (y ^ 2 - 1))) - S / c * (Y / (Y ^ 2 - 1)) := by ring
    _ ≤ 3 * (S / c * (y / (y ^ 2 - 1))) := by linarith

/-- **TI**: `|∫_y^∞ ψ| ≤ 3√6·√M·y/(c(y² − 1))` for `y ≥ 6/5`, `M = ∫₁^∞ ψ²`, `c ≥ 80`, `0 ≤ χ < c²`. -/
theorem abs_tailInt_le_mass (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) {y : ℝ} (hy : 6 / 5 ≤ y) :
    |tailInt (psi c g) y| ≤ 3 * √6 * √(∫ t in Ioi 1, psi c g t ^ 2) * y / (c * (y ^ 2 - 1)) := by
  have e : 3 * √6 * √(∫ t in Ioi 1, psi c g t ^ 2) = 3 * √(6 * ∫ t in Ioi 1, psi c g t ^ 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]; ring
  rw [e]
  exact le_of_tendsto (tendsto_tailInt hg hg₁ hg₂c (by linarith) (by linarith : (1 : ℝ) ≤ y)).abs
    ((eventually_ge_atTop y).mono fun _ hY => abs_integral_psi_le_mass hg hg₁ hg₂c hang hc hχ0 hχc hy hY)

end rung

section span

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- The span's tail integral converges to the combination of the rungs' tail integrals. -/
theorem tendsto_tailInt_span (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc : 0 < c) {t : ℝ} (ht : 1 ≤ t) :
    Tendsto (fun Y : ℝ => ∫ ξ in t..Y, ∑ i, b i * psi c (g i) ξ) atTop
      (𝓝 (∑ i, b i * tailInt (psi c (g i)) t)) := by
  have hψ : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).continuous
  have e : (fun Y : ℝ => ∫ ξ in t..Y, ∑ i, b i * psi c (g i) ξ)
      = fun Y => ∑ i, b i * ∫ ξ in t..Y, psi c (g i) ξ := by
    funext Y
    rw [intervalIntegral.integral_finsetSum fun i _ => ((hψ i).intervalIntegrable _ _).const_mul _]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  rw [e]
  exact tendsto_finsetSum _ fun i _ => (tendsto_tailInt (hg i) (hg₁ i) (hg₂c i) hc ht).const_mul _

/-- `I_Φ(t) = Σ bᵢ I_{ψᵢ}(t)` for `t ≥ 1`. -/
theorem tailInt_span (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc : 0 < c) {t : ℝ} (ht : 1 ≤ t) :
    tailInt (fun ξ => ∑ i, b i * psi c (g i) ξ) t = ∑ i, b i * tailInt (psi c (g i)) t :=
  (tendsto_tailInt_span b hg hg₁ hg₂c hc ht).limUnder_eq

/-- **TI on the span**: `|∫_y^∞ Φ| ≤ 3√(6J)·y/(c(y² − 1))·√P` for `y ≥ 6/5`, `P = Σ bᵢ²∫₁^∞ ψᵢ²`. -/
theorem abs_tailInt_span_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {y : ℝ} (hy : 6 / 5 ≤ y) :
    |tailInt (fun ξ => ∑ i, b i * psi c (g i) ξ) y|
      ≤ 3 * √(6 * (Fintype.card ι : ℝ)) * y / (c * (y ^ 2 - 1))
        * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  set M : ι → ℝ := fun i => ∫ t in Ioi 1, psi c (g i) t ^ 2 with hMdef
  have hM : ∀ i, 0 ≤ M i := fun i => setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hc0 : 0 < c := by linarith
  have hy1 : 1 < y := by linarith
  have hyp : 0 < y ^ 2 - 1 := by nlinarith
  set B := 3 * √6 * y / (c * (y ^ 2 - 1)) with hBdef
  have hB : 0 ≤ B := by positivity
  rw [tailInt_span b hg hg₁ hg₂c hc0 hy1.le]
  have hi : ∀ i, |b i * tailInt (psi c (g i)) y| ≤ B * (|b i| * √(M i)) := fun i => by
    rw [abs_mul]
    have h := abs_tailInt_le_mass (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχc i) hy
    calc |b i| * |tailInt (psi c (g i)) y| ≤ |b i| * (3 * √6 * √(M i) * y / (c * (y ^ 2 - 1))) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = B * (|b i| * √(M i)) := by rw [hBdef]; ring
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) (fun i => |b i| * √(M i))
  have e1 : ∑ _i : ι, (1 : ℝ) ^ 2 = (Fintype.card ι : ℝ) := by simp
  have e2 : ∑ i, (|b i| * √(M i)) ^ 2 = ∑ i, b i ^ 2 * M i := Finset.sum_congr rfl fun i _ => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hM i)]
  rw [e1, e2] at hCS
  simp only [one_mul] at hCS
  have e3 : 3 * √(6 * (Fintype.card ι : ℝ)) * y / (c * (y ^ 2 - 1)) = B * √(Fintype.card ι : ℝ) := by
    rw [hBdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]; ring
  rw [e3]
  calc |∑ i, b i * tailInt (psi c (g i)) y| ≤ ∑ i, |b i * tailInt (psi c (g i)) y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * (|b i| * √(M i)) := Finset.sum_le_sum fun i _ => hi i
    _ = B * ∑ i, |b i| * √(M i) := by rw [Finset.mul_sum]
    _ ≤ B * (√(Fintype.card ι : ℝ) * √(∑ i, b i ^ 2 * M i)) := mul_le_mul_of_nonneg_left hCS hB
    _ = B * √(Fintype.card ι : ℝ) * √(∑ i, b i ^ 2 * M i) := by ring

/-- **The edge strip**: `|∫₁^{6/5} Φ| ≤ 5^{−1/2}·√P` for rungs with pairwise distinct `χᵢ`. -/
theorem abs_integral_edge_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) :
    |∫ ξ in (1 : ℝ)..6 / 5, ∑ i, b i * psi c (g i) ξ|
      ≤ 1 / √5 * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ with hΦdef
  have hψ : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).continuous
  have hΦc : Continuous Φ := continuous_finsetSum _ fun i _ => continuous_const.mul (hψ i)
  have hsq := sq_integral_le (by norm_num : (1 : ℝ) ≤ 6 / 5) hΦc.continuousOn
  have hmem : MemLp Φ 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (b i)
  have hint : IntegrableOn (fun t => Φ t ^ 2) (Ioi 1) := hmem.integrable_sq
  have hle : ∫ t in (1 : ℝ)..6 / 5, Φ t ^ 2 ≤ ∫ t in Ioi 1, Φ t ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun t => sq_nonneg (Φ t))
      (Filter.Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)
  have hP := Cvs.Prolate.RungExactOrthogonality.integral_span_sq b hg hg₁ hg₂c hang hc hχ
  have hP' : ∫ t in Ioi 1, Φ t ^ 2 = ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 := hP
  rw [← hP']
  set P := ∫ t in Ioi 1, Φ t ^ 2 with hPdef
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have h2 : (∫ ξ in (1 : ℝ)..6 / 5, Φ ξ) ^ 2 ≤ P / 5 := by
    calc _ ≤ (6 / 5 - 1) * ∫ t in (1 : ℝ)..6 / 5, Φ t ^ 2 := hsq
      _ ≤ (6 / 5 - 1) * P := mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = P / 5 := by ring
  refine (Real.abs_le_sqrt h2).trans (le_of_eq ?_)
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 5)]; ring

/-- The pole constant `C_π = 5^{−1/2} + (3√(6J)/c)(30/11 + 3/4)`. -/
noncomputable def piConst (J c : ℝ) : ℝ := 1 / √5 + 3 * √(6 * J) / c * (30 / 11 + 3 / 4)

/-- **`|Π₊(Φ)| ≤ C_π√P`** for a span of rungs with `c ≥ 80` and pairwise distinct `χᵢ ∈ [0, c²)`. -/
theorem abs_piPlus_span_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ) :
    |piPlus (fun ξ => ∑ i, b i * psi c (g i) ξ)|
      ≤ piConst (Fintype.card ι) c * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ with hΦdef
  set P := ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 with hPdef
  set J : ℝ := (Fintype.card ι : ℝ) with hJdef
  have hc0 : 0 < c := by linarith
  set K := 3 * √(6 * J) / c * √P with hKdef
  have hK : 0 ≤ K := by positivity
  set f : ℕ → ℝ := fun m => tailInt Φ ((m : ℝ) + 1) / ((m : ℝ) + 1) with hfdef
  -- the terms `m ≥ 1`
  have hterm : ∀ m : ℕ, |f (m + 1)| ≤ K * (1 / (((m : ℝ) + 2) ^ 2 - 1)) := by
    intro m
    have hy : (6 / 5 : ℝ) ≤ (m : ℝ) + 2 := by have := m.cast_nonneg (α := ℝ); linarith
    have hy0 : (0 : ℝ) < (m : ℝ) + 2 := by linarith
    have hyp : (0 : ℝ) < ((m : ℝ) + 2) ^ 2 - 1 := by nlinarith
    have h := abs_tailInt_span_le b hg hg₁ hg₂c hang hc hχ0 hχc hy
    have ec : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
    simp only [hfdef, ec]
    rw [abs_div, abs_of_pos hy0, div_le_iff₀ hy0]
    calc |tailInt Φ ((m : ℝ) + 2)|
        ≤ 3 * √(6 * J) * ((m : ℝ) + 2) / (c * (((m : ℝ) + 2) ^ 2 - 1)) * √P := h
      _ = K * (1 / (((m : ℝ) + 2) ^ 2 - 1)) * ((m : ℝ) + 2) := by rw [hKdef]; field_simp
  have hpart : ∀ N, ∑ m ∈ Finset.range N, |f (m + 1)| ≤ K * (3 / 4) := fun N =>
    calc ∑ m ∈ Finset.range N, |f (m + 1)| ≤ ∑ m ∈ Finset.range N, K * (1 / (((m : ℝ) + 2) ^ 2 - 1)) :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = K * ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2 - 1) := by rw [Finset.mul_sum]
      _ ≤ K * (3 / 4) := mul_le_mul_of_nonneg_left (sum_range_inv_sq_sub_one_le N) hK
  have hsabs : Summable fun m => |f (m + 1)| := summable_of_sum_range_le (fun _ => abs_nonneg _) hpart
  have hsnorm : Summable fun m => ‖f (m + 1)‖ := by simpa [Real.norm_eq_abs] using hsabs
  have hs : Summable fun m => f (m + 1) := hsnorm.of_norm
  have hsplit : piPlus Φ = f 0 + ∑' m, f (m + 1) := tsum_eq_zero_add' hs
  have htail : |∑' m, f (m + 1)| ≤ K * (3 / 4) := by
    have h1 : ‖∑' m, f (m + 1)‖ ≤ ∑' m, ‖f (m + 1)‖ := norm_tsum_le_tsum_norm hsnorm
    have h2 : ∑' m, ‖f (m + 1)‖ ≤ K * (3 / 4) := by
      simp only [Real.norm_eq_abs]
      exact Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) hpart
    simpa [Real.norm_eq_abs] using h1.trans h2
  -- the term `m = 0`: the edge strip and TI at `6/5`
  have hf0 : f 0 = (∫ ξ in (1 : ℝ)..6 / 5, Φ ξ) + tailInt Φ (6 / 5) := by
    simp only [hfdef, Nat.cast_zero, zero_add, div_one]
    rw [tailInt_span b hg hg₁ hg₂c hc0 le_rfl, tailInt_span b hg hg₁ hg₂c hc0 (by norm_num)]
    have hψ : ∀ i, Continuous (psi c (g i)) := fun i =>
      (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).continuous
    rw [intervalIntegral.integral_finsetSum fun i _ => ((hψ i).intervalIntegrable _ _).const_mul _,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul,
      ← tailInt_sub (hg i) (hg₁ i) (hg₂c i) hc0 le_rfl (by norm_num : (1 : ℝ) ≤ 6 / 5)]
    ring
  have hedge := abs_integral_edge_le b hg hg₁ hg₂c hang hc0 hχ
  have hTI := abs_tailInt_span_le b hg hg₁ hg₂c hang hc hχ0 hχc (le_refl (6 / 5 : ℝ))
  have e65 : 3 * √(6 * J) * (6 / 5) / (c * ((6 / 5) ^ 2 - 1)) * √P = K * (30 / 11) := by
    rw [hKdef]; field_simp; ring
  rw [← hΦdef, ← hPdef] at hedge
  rw [← hΦdef, ← hPdef, ← hJdef] at hTI
  rw [e65] at hTI
  rw [hsplit, hf0]
  have hfin : piConst J c * √P = 1 / √5 * √P + K * (30 / 11) + K * (3 / 4) := by
    rw [piConst, hKdef]; ring
  rw [hfin]
  calc |(∫ ξ in (1 : ℝ)..6 / 5, Φ ξ) + tailInt Φ (6 / 5) + ∑' m, f (m + 1)|
      ≤ |∫ ξ in (1 : ℝ)..6 / 5, Φ ξ| + |tailInt Φ (6 / 5)| + |∑' m, f (m + 1)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ 1 / √5 * √P + K * (30 / 11) + K * (3 / 4) := add_le_add (add_le_add hedge hTI) htail

end span

end Cvs.Prolate.RungTailIntegralMass
