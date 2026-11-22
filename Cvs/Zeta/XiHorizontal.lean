import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiConj

/-!
# The horizontal sides vanish in the limit

`Cvs.Zeta.RectXi` gives the zero sum at finite height.
-/

open Complex Real Set

namespace Cvs.Zeta

/-- The horizontal side of the rung-7 rectangle runs from `Re = −1` to `Re = 2`, and
`exists_norm_logDeriv_riemannXi_le_log_sq` covers it at radius `r = 12`: a point of the
segment is at distance `|x − 2| ≤ 3 = r/4` from the centre `2 + iT'`. -/
theorem mem_horizontal_ball {x T' : ℝ} (hx : x ∈ Set.uIcc (-1 : ℝ) 2) :
    ‖((x : ℂ) + T' * I) - (2 + (T' : ℂ) * I)‖ ≤ (12 : ℝ) / 4 := by
  have hxc : ((x : ℂ) + T' * I) - (2 + (T' : ℂ) * I) = ((x - 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hxc, Complex.norm_real, Real.norm_eq_abs]
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
  rw [abs_le]
  constructor <;> [linarith [hx.1]; linarith [hx.2]]

/-- **The horizontal contribution, bounded.** At a zero-free height `T' ∈ [T, T+1]`, the integral
of `(ξ'/ξ)·φ` along the segment `Re ∈ [−1, 2]` is at most `3 · K log²|T| · M`, where `M`
bounds `φ` on the segment. -/
theorem norm_horizontal_integral_le {T T' K M : ℝ} {φ : ℂ → ℂ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, ‖z - (2 + (T' : ℂ) * I)‖ ≤ (12 : ℝ) / 4 → z.im = T' →
      riemannZeta z ≠ 0 → ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T|) ^ 2)
    (hφ : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ‖φ ((x : ℂ) + T' * I)‖ ≤ M)
    (hζ : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta ((x : ℂ) + T' * I) ≠ 0) :
    ‖∫ x in (-1 : ℝ)..2,
        logDeriv riemannXi ((x : ℂ) + T' * I) * φ ((x : ℂ) + T' * I)‖
      ≤ 3 * (K * (1 + Real.log |T|) ^ 2 * M) := by
  have hpt : ∀ x ∈ Set.uIoc (-1 : ℝ) 2,
      ‖logDeriv riemannXi ((x : ℂ) + T' * I) * φ ((x : ℂ) + T' * I)‖
        ≤ K * (1 + Real.log |T|) ^ 2 * M := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-1 : ℝ) 2 := Set.uIoc_subset_uIcc hx
    have him : (((x : ℂ) + T' * I)).im = T' := by simp
    have h1 := hbound ((x : ℂ) + T' * I) (mem_horizontal_ball hx') him (hζ x hx')
    rw [norm_mul]
    exact mul_le_mul h1 (hφ x hx') (norm_nonneg _) (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  calc ‖∫ x in (-1 : ℝ)..2,
        logDeriv riemannXi ((x : ℂ) + T' * I) * φ ((x : ℂ) + T' * I)‖
      ≤ K * (1 + Real.log |T|) ^ 2 * M * |(2 : ℝ) - (-1)| := this
    _ = 3 * (K * (1 + Real.log |T|) ^ 2 * M) := by norm_num; ring

/-! ### The horizontal contribution vanishes -/

/-- `(1 + log T)² / T² → 0`, the form in which the horizontal weight is actually used. -/
theorem tendsto_one_add_log_sq_div_self_sq : Filter.Tendsto
    (fun T : ℝ => (1 + Real.log T) ^ 2 / T ^ 2) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun T : ℝ => (1 : ℝ) / T) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have h2 : Filter.Tendsto (fun T : ℝ => Real.log T / T) Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h3 : Filter.Tendsto (fun T : ℝ => (1 + Real.log T) / T) Filter.atTop (nhds 0) := by
    simpa [add_div] using h1.add h2
  simpa [div_pow] using h3.pow 2

/-- **The bottom edge, by reflection.** `Cvs.Zeta.XiConj.norm_logDeriv_riemannXi_reflect` gives
`‖ξ'/ξ(x − iT')‖ = ‖ξ'/ξ(x + iT')‖`, so the bound proved at `+T'` transfers with no second
zero-free height, no second Landau estimate, and no `ζ ≠ 0` hypothesis on the lower segment. -/
theorem norm_horizontal_integral_le_neg {T T' K M : ℝ} {φ : ℂ → ℂ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, ‖z - (2 + (T' : ℂ) * I)‖ ≤ (12 : ℝ) / 4 → z.im = T' →
      riemannZeta z ≠ 0 → ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T|) ^ 2)
    (hφ : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ‖φ ((x : ℂ) - T' * I)‖ ≤ M)
    (hζ : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta ((x : ℂ) + T' * I) ≠ 0) :
    ‖∫ x in (-1 : ℝ)..2,
        logDeriv riemannXi ((x : ℂ) - T' * I) * φ ((x : ℂ) - T' * I)‖
      ≤ 3 * (K * (1 + Real.log |T|) ^ 2 * M) := by
  have hpt : ∀ x ∈ Set.uIoc (-1 : ℝ) 2,
      ‖logDeriv riemannXi ((x : ℂ) - T' * I) * φ ((x : ℂ) - T' * I)‖
        ≤ K * (1 + Real.log |T|) ^ 2 * M := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-1 : ℝ) 2 := Set.uIoc_subset_uIcc hx
    have him : (((x : ℂ) + T' * I)).im = T' := by simp
    have h1 := hbound ((x : ℂ) + T' * I) (mem_horizontal_ball hx') him (hζ x hx')
    rw [norm_mul, norm_logDeriv_riemannXi_reflect]
    exact mul_le_mul h1 (hφ x hx') (norm_nonneg _) (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  calc ‖∫ x in (-1 : ℝ)..2,
        logDeriv riemannXi ((x : ℂ) - T' * I) * φ ((x : ℂ) - T' * I)‖
      ≤ K * (1 + Real.log |T|) ^ 2 * M * |(2 : ℝ) - (-1)| := h
    _ = 3 * (K * (1 + Real.log |T|) ^ 2 * M) := by norm_num; ring

end Cvs.Zeta
