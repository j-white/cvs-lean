import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ZetaGrowth
import Cvs.Zeta.ZetaInterior
import Cvs.Zeta.ZetaStrip

/-!
# Rung 7: polynomial growth of `ζ` across the critical strip

Phragmén–Lindelöf converts the two edge bounds of `Cvs.Zeta.ZetaStrip` into a bound across the
whole strip `-1/2 ≤ Re s ≤ 3/2`, using the interior growth bound of `Cvs.Zeta.ZetaInterior` as
its hypothesis.
-/

open Complex Real Filter Asymptotics Set

namespace Cvs.Zeta

/-- `ζ₁ s = (s-1) ζ s` away from `s = 1`. -/
theorem riemannZeta₁_eq_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

/-- On `Re s ≥ -1/2` the shifted point `s + 3` is bounded below in the way the
denominator of the auxiliary function needs. -/
theorem norm_add_three_sq_ge {s : ℂ} (h : -(1 / 2 : ℝ) ≤ s.re) :
    (1 + |s.im|) ^ 2 / 2 ≤ ‖s + 3‖ ^ 2 := by
  have hre : (s + 3).re = s.re + 3 := by simp
  have him : (s + 3).im = s.im := by simp
  have hn : ‖s + 3‖ ^ 2 = (s.re + 3) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]; ring
  rw [hn]
  have h1 : (5 / 2 : ℝ) ≤ s.re + 3 := by linarith
  have h2 : (25 / 4 : ℝ) ≤ (s.re + 3) ^ 2 := by nlinarith
  have h3 : s.im ^ 2 = |s.im| ^ 2 := (sq_abs _).symm
  nlinarith [abs_nonneg s.im]

/-- The auxiliary function `ζ₁(s)/(s+3)²`: entire numerator, and the denominator never
vanishes anywhere near the strip. -/
noncomputable def zetaAux (s : ℂ) : ℂ := riemannZeta₁ s / (s + 3) ^ 2

theorem differentiableAt_zetaAux {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ zetaAux z := by
  have hne : z + 3 ≠ 0 := by
    intro h
    have : (z + 3).re = 0 := by rw [h]; simp
    simp at this; linarith
  exact DifferentiableAt.fun_div (differentiable_riemannZeta₁ z)
    ((differentiableAt_id.add_const 3).fun_pow 2) (pow_ne_zero 2 hne)

theorem diffContOnCl_zetaAux :
    DiffContOnCl ℂ zetaAux (Complex.re ⁻¹' Ioo (-(1 / 2) : ℝ) (3 / 2)) := by
  have hsub : closure (Complex.re ⁻¹' Ioo (-(1 / 2) : ℝ) (3 / 2))
      ⊆ Complex.re ⁻¹' Icc (-(1 / 2) : ℝ) (3 / 2) := by
    refine subset_trans (Continuous.closure_preimage_subset Complex.continuous_re _) ?_
    rw [closure_Ioo (by norm_num : (-(1 / 2) : ℝ) ≠ 3 / 2)]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (differentiableAt_zetaAux (by have := hz.1; simp at this ⊢; linarith)).differentiableWithinAt
  · have h := hsub hz
    exact (differentiableAt_zetaAux
      (by have := h.1; simp at this ⊢; linarith)).continuousAt.continuousWithinAt

/-- `‖ζ₁ s‖ = ‖s-1‖ ‖ζ s‖`, and the `(s+3)²` lower bound, packaged for both edges. -/
theorem norm_zetaAux_le {s : ℂ} (hs : s ≠ 1) (hre : -(1 / 2 : ℝ) ≤ s.re) {D : ℝ}
    (hD : ‖riemannZeta s‖ ≤ D * (1 + |s.im|)) (hD0 : 0 ≤ D)
    (hup : ‖s - 1‖ ≤ 3 * (1 + |s.im|)) :
    ‖zetaAux s‖ ≤ 6 * D := by
  have hden := norm_add_three_sq_ge hre
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hpos : (0 : ℝ) < (1 + |s.im|) ^ 2 / 2 := by positivity
  have hnum : ‖riemannZeta₁ s‖ ≤ 3 * (1 + |s.im|) * (D * (1 + |s.im|)) := by
    rw [riemannZeta₁_eq_mul hs, norm_mul]
    exact mul_le_mul hup hD (norm_nonneg _) (by positivity)
  rw [zetaAux, norm_div, norm_pow, div_le_iff₀ (lt_of_lt_of_le hpos hden)]
  calc ‖riemannZeta₁ s‖ ≤ 3 * (1 + |s.im|) * (D * (1 + |s.im|)) := hnum
    _ = 6 * D * ((1 + |s.im|) ^ 2 / 2) := by ring
    _ ≤ 6 * D * ‖s + 3‖ ^ 2 := by nlinarith

/-- `‖s - 1‖ ≤ 3(1 + |Im s|)` on the strip. -/
theorem norm_sub_one_le {s : ℂ} (h1 : -(1 / 2 : ℝ) ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖s - 1‖ ≤ 3 * (1 + |s.im|) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (s - 1).re = s.re - 1 := by simp
  have him : (s - 1).im = s.im := by simp
  rw [hre, him]
  have : |s.re - 1| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [abs_nonneg s.im]

/-- Both edges of the strip `[-1/2, 3/2]` give a constant bound on `zetaAux`. -/
theorem exists_edge_bound :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ s : ℂ, s.re = -(1 / 2 : ℝ) → ‖zetaAux s‖ ≤ C)
      ∧ ∀ s : ℂ, s.re = 3 / 2 → ‖zetaAux s‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_riemannZeta_left_edge 1 le_rfl
  set Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3 / 2 : ℝ) : ℂ) n‖ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨6 * max (2 * C₁) Z, by positivity, ?_, ?_⟩
  · intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs; linarith
    have hform : s = (1 / 2 : ℂ) - (1 : ℕ) + (s.im : ℝ) * I := by
      refine Complex.ext ?_ ?_
      · simp [hs]
        norm_num
      · simp
    have hz : ‖riemannZeta s‖ ≤ 2 * C₁ * (1 + |s.im|) := by
      have := hC₁ s.im
      rw [← hform] at this
      simp only [Nat.cast_one, pow_one] at this
      nlinarith [abs_nonneg s.im, this]
    refine le_trans (norm_zetaAux_le hs1 (by rw [hs]) hz (by positivity)
      (norm_sub_one_le (by rw [hs]) (by rw [hs]; norm_num))) ?_
    have : 2 * C₁ ≤ max (2 * C₁) Z := le_max_left _ _
    linarith
  · intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs; linarith
    have hz : ‖riemannZeta s‖ ≤ Z * (1 + |s.im|) := by
      have h := norm_riemannZeta_le_of_re_le (σ₀ := 3 / 2) (by norm_num) (le_of_eq hs.symm)
      nlinarith [abs_nonneg s.im, h, hZ0]
    refine le_trans (norm_zetaAux_le hs1 (by rw [hs]; norm_num) hz hZ0
      (norm_sub_one_le (by rw [hs]; norm_num) (by rw [hs]))) ?_
    have : Z ≤ max (2 * C₁) Z := le_max_right _ _
    linarith

/-- The growth hypothesis Phragmén–Lindelöf asks for.  The interior bound
`‖ζ‖ ≤ C e^{π|t|/2}` is exponential, and `exp (B exp (c|t|))` is doubly exponential, so
this holds with room to spare — `c = 1` against the threshold `π/2`. -/
theorem zetaAux_growth :
    ∃ c < π / (3 / 2 - -(1 / 2 : ℝ)), ∃ B : ℝ,
      zetaAux =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
          𝓟 (Complex.re ⁻¹' Ioo (-(1 / 2) : ℝ) (3 / 2))]
        fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨Ci, hCi0, hCi⟩ :=
    exists_norm_riemannZeta_le_exp (a := -(1 / 2 : ℝ)) (b := 3 / 2) (by norm_num)
  refine ⟨1, by rw [show (3 / 2 - -(1 / 2 : ℝ)) = 2 by ring]; nlinarith [Real.pi_gt_three],
    π / 2, ?_⟩
  refine Asymptotics.IsBigO.of_bound (6 * Ci) ?_
  have h1 : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop, (1 : ℝ) ≤ |z.im| :=
    Filter.Eventually.comap (Filter.eventually_ge_atTop (1 : ℝ)) _
  have h2 : ∀ᶠ z : ℂ in 𝓟 (Complex.re ⁻¹' Ioo (-(1 / 2) : ℝ) (3 / 2)),
      z.re ∈ Ioo (-(1 / 2) : ℝ) (3 / 2) := Filter.eventually_principal.mpr fun _ hz => hz
  filter_upwards [h1.filter_mono inf_le_left, h2.filter_mono inf_le_right] with z hz1 hz2
  have hu : (0 : ℝ) ≤ |z.im| := abs_nonneg _
  have hzne : z ≠ 1 := by
    intro h; rw [h] at hz1; simp at hz1; linarith
  set D : ℝ := Ci * Real.exp (π * |z.im| / 2) with hD
  have hD0 : 0 ≤ D := by positivity
  have hzeta : ‖riemannZeta z‖ ≤ D * (1 + |z.im|) := by
    have := hCi z hz2.1.le hz2.2.le hz1
    nlinarith [hD0]
  have hmain := norm_zetaAux_le hzne hz2.1.le hzeta hD0
    (norm_sub_one_le hz2.1.le hz2.2.le)
  -- `exp (π|t|/2) ≤ exp ((π/2) exp |t|)` because `u ≤ exp u`
  have hstep : Real.exp (π * |z.im| / 2) ≤ Real.exp (π / 2 * Real.exp (1 * |z.im|)) := by
    refine Real.exp_le_exp.mpr ?_
    have hue : |z.im| ≤ Real.exp |z.im| := by
      linarith [Real.add_one_le_exp |z.im|]
    rw [one_mul]
    nlinarith [Real.pi_pos]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖zetaAux z‖ ≤ 6 * D := hmain
    _ ≤ 6 * Ci * Real.exp (π / 2 * Real.exp (1 * |z.im|)) := by
        rw [hD]; nlinarith [hstep, hCi0]

/-- **Polynomial growth of `ζ` across the strip `-1/2 ≤ Re s ≤ 3/2`** — rung 7. -/
theorem exists_norm_riemannZeta₁_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖riemannZeta₁ s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  obtain ⟨Ce, hCe0, hleft, hright⟩ := exists_edge_bound
  refine ⟨21 * Ce, by positivity, fun s h1 h2 => ?_⟩
  have hpl : ‖zetaAux s‖ ≤ Ce :=
    PhragmenLindelof.vertical_strip diffContOnCl_zetaAux zetaAux_growth hleft hright h1 h2
  have hne : s + 3 ≠ 0 := by
    intro h
    have : (s + 3).re = 0 := by rw [h]; simp
    simp at this; linarith
  have hzeta : riemannZeta₁ s = zetaAux s * (s + 3) ^ 2 := by
    rw [zetaAux, div_mul_cancel₀ _ (pow_ne_zero 2 hne)]
  have hup : ‖s + 3‖ ≤ 9 / 2 * (1 + |s.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : (s + 3).re = s.re + 3 := by simp
    have him : (s + 3).im = s.im := by simp
    rw [hre, him]
    have : |s.re + 3| ≤ 9 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith [abs_nonneg s.im]
  rw [hzeta, norm_mul, norm_pow]
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hsq : ‖s + 3‖ ^ 2 ≤ 81 / 4 * (1 + |s.im|) ^ 2 := by
    nlinarith [norm_nonneg (s + 3), hup]
  nlinarith [hpl, hsq, norm_nonneg (zetaAux s), sq_nonneg (1 + |s.im|)]

/-- **Rung 7**, stated for `ζ` itself.  Away from the pole (`1 ≤ |Im s|` suffices) the
`(s-1)` factor is harmless and the same polynomial bound holds for `ζ`. -/
theorem exists_norm_riemannZeta_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta₁_le_sq
  refine ⟨C, hC0, fun s h1 h2 h3 => ?_⟩
  have hs1 : s ≠ 1 := by intro h; rw [h] at h3; simp at h3; linarith
  have hlow : (1 : ℝ) ≤ ‖s - 1‖ := by
    refine le_trans h3 ?_
    have := Complex.abs_im_le_norm (s - 1)
    simpa using this
  have hz : ‖riemannZeta₁ s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by
    rw [riemannZeta₁_eq_mul hs1, norm_mul]
  have := hC s h1 h2
  rw [hz] at this
  nlinarith [norm_nonneg (riemannZeta s), this, hlow]

/-- **`ζ` is polynomially bounded on the whole half-plane `Re s ≥ -1/2`** (off the real axis). -/
theorem exists_norm_riemannZeta_le_sq_of_re_ge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_le_sq
  set Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3 / 2 : ℝ) : ℂ) n‖ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨max C Z, le_trans hC0 (le_max_left _ _), fun s h1 h3 => ?_⟩
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hsq : (1 : ℝ) ≤ (1 + |s.im|) ^ 2 := by nlinarith
  rcases le_or_gt s.re (3 / 2) with h2 | h2
  · refine le_trans (hC s h1 h2 h3) ?_
    have := le_max_left C Z
    nlinarith [sq_nonneg (1 + |s.im|)]
  · have hz : ‖riemannZeta s‖ ≤ Z :=
      norm_riemannZeta_le_of_re_le (σ₀ := 3 / 2) (by norm_num) h2.le
    refine le_trans hz ?_
    have := le_max_right C Z
    nlinarith [hsq, hZ0]

end Cvs.Zeta
