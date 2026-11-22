import Mathlib
import Cvs.Zeta.RectWinding
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiContourStep
import Cvs.Zeta.XiHorizontal
import Cvs.Zeta.XiJointHeight

/-!
# The horizontal sides contribute nothing in the limit

`Cvs.Zeta.XiContourStep` bounds the gap between the zero sum and the two vertical integrals by
`6K(1+log|T|)²M`, with `M` bounding the test function on the horizontal edges.
-/

open Complex

namespace Cvs.Zeta

/-- `(1 + log T)² / T³ → 0` — the contour error, once the test function supplies cubic
decay.  One factor of `T` more than the horizontal estimate strictly needs; it comes free
from `φ`. -/
theorem tendsto_one_add_log_sq_div_cube : Filter.Tendsto
    (fun T : ℝ => (1 + Real.log T) ^ 2 / T ^ 3) Filter.atTop (nhds 0) := by
  have h1 := tendsto_one_add_log_sq_div_self_sq
  have h2 : Filter.Tendsto (fun T : ℝ => (1 : ℝ) / T) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have := h1.mul h2
  simp only [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  field_simp

/-- **The zero sum differs from the two vertical integrals by something that vanishes.** ‖
i·(right) − i·(left) − 2πi·Σ_ρ m_ρ φ(ρ) ‖ ≤ C·(1 + log T)² / T³ for every `T ≥ 32`, with `C =
6KA` depending only on `φ`'s decay constant. -/
theorem exists_contour_bound {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφd : Differentiable ℂ φ)
    (hφ : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖φ z‖ ≤ A / (1 + |z.im|) ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 32 ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧ T' ≤ T + 1 ∧
        (∀ ρ ∈ S, riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        ‖I * (∫ y in (-T')..T',
              logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I) * φ ((2 : ℂ) + (y : ℂ) * I))
            - I * (∫ y in (-T')..T',
              logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I) * φ ((-1 : ℂ) + (y : ℂ) * I))
            - 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ‖
          ≤ C * ((1 + Real.log T) ^ 2 / T ^ 3) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_joint_height 12 (by norm_num) (by norm_num) 25 (by norm_num) (by norm_num) hφd
  refine ⟨6 * K * A, by positivity, fun T hT => ?_⟩
  obtain ⟨T', S, m, hT1, hT2, hS0, hSin, hScap, hSmult, hζseg, hbound, heq⟩ := hK T (by norm_num; linarith)
  refine ⟨T', S, m, hT1, hT2, hS0, hSin, hScap, hSmult, ?_⟩
  have hTpos : (0 : ℝ) < T := by linarith
  have hT'pos : (0 : ℝ) < T' := by linarith
  have hstrip : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, -1 ≤ x ∧ x ≤ 2 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
    exact hx
  have hMdef : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ‖φ ((x : ℂ) + T' * I)‖ ≤ A / (1 + T') ^ 3 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hstrip x hx
    have h := hφ ((x : ℂ) + T' * I) (by simpa using hx1) (by simpa using hx2)
    have him : (((x : ℂ) + T' * I)).im = T' := by simp
    rwa [him, abs_of_pos hT'pos] at h
  have hMdef' : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ‖φ ((x : ℂ) - T' * I)‖ ≤ A / (1 + T') ^ 3 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hstrip x hx
    have h := hφ ((x : ℂ) - T' * I) (by simpa using hx1) (by simpa using hx2)
    have him : (((x : ℂ) - T' * I)).im = -T' := by simp
    rwa [him, abs_neg, abs_of_pos hT'pos] at h
  have hstep := norm_verticals_sub_zero_sum_le (T := T) (T' := T') (K := K)
    (M := A / (1 + T') ^ 3) (φ := φ) (S := S) (m := m) hK0 hbound hζseg
    hMdef hMdef' heq
  refine hstep.trans ?_
  rw [abs_of_pos hTpos]
  have hcube : T ^ 3 ≤ (1 + T') ^ 3 := by
    have : T ≤ 1 + T' := by linarith
    exact pow_le_pow_left₀ (by linarith) this 3
  have hdiv : A / (1 + T') ^ 3 ≤ A / T ^ 3 :=
    div_le_div_of_nonneg_left hA (by positivity) hcube
  have hlogsq : (0 : ℝ) ≤ (1 + Real.log T) ^ 2 := sq_nonneg _
  have hKlog : (0 : ℝ) ≤ 6 * (K * (1 + Real.log T) ^ 2) := by positivity
  calc 6 * (K * (1 + Real.log T) ^ 2 * (A / (1 + T') ^ 3))
      = 6 * (K * (1 + Real.log T) ^ 2) * (A / (1 + T') ^ 3) := by ring
    _ ≤ 6 * (K * (1 + Real.log T) ^ 2) * (A / T ^ 3) :=
        mul_le_mul_of_nonneg_left hdiv hKlog
    _ = 6 * K * A * ((1 + Real.log T) ^ 2 / T ^ 3) := by ring

end Cvs.Zeta
