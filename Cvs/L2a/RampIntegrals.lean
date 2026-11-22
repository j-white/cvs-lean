import Mathlib
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ramp's x-integrals and the `nN` calculus

The six x-profiles `xw/p`, `x²w/p²`, `w/p`, `xw′/p`, `w′/p`, `w/p²` of `FarIntegrationByParts`'s ramp lie in `L²(3/2, ∞)`; `FarFarBound`'s `nN` is
monotone, homogeneous and subadditive; `∫ w′² = π²/4`, `∫ w″² = π⁴`, and `∫ (2xw′/p + w″)² = 6‖xw′/p‖² + 2‖w′/p‖² + π⁴`.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound

namespace Cvs.L2a.RampIntegrals

/-! ### The six x-profiles -/

/-- The x-profile `xw/p` (`FarIntegrationByParts`'s ramp `wF`; `ProlateEnergyOutsideInterval`'s `pP x = x² − 1`). -/
def xP₂ (x : ℝ) : ℝ := x * wF x / pP x

/-- The x-profile `x²w/p²`. -/
def xP₃ (x : ℝ) : ℝ := x ^ 2 * wF x / pP x ^ 2

/-- The x-profile `w/p`. -/
def xP₄ (x : ℝ) : ℝ := wF x / pP x

/-- The x-profile `xw′/p`. -/
def xP₅ (x : ℝ) : ℝ := x * wF₁ x / pP x

/-- The x-profile `w′/p`. -/
def xP₆ (x : ℝ) : ℝ := wF₁ x / pP x

/-- The x-profile `w/p²`. -/
def xP₇ (x : ℝ) : ℝ := wF x / pP x ^ 2

/-- `p x ≥ (5/9) x²` for `x ≥ 3/2`. -/
theorem pP_ge {x : ℝ} (hx : 3 / 2 ≤ x) : 5 / 9 * x ^ 2 ≤ pP x := by
  unfold pP; nlinarith

/-- The six x-profiles lie in `L²(3/2, ∞)`. -/
theorem memLp_xP :
    MemLp xP₂ 2 (volume.restrict (Ioi (3 / 2))) ∧ MemLp xP₃ 2 (volume.restrict (Ioi (3 / 2)))
      ∧ MemLp xP₄ 2 (volume.restrict (Ioi (3 / 2))) ∧ MemLp xP₅ 2 (volume.restrict (Ioi (3 / 2)))
      ∧ MemLp xP₆ 2 (volume.restrict (Ioi (3 / 2))) ∧ MemLp xP₇ 2 (volume.restrict (Ioi (3 / 2))) := by
  have h0 := continuous_wF.1.measurable
  have h1 := continuous_wF.2.measurable
  have key : ∀ x, 3 / 2 < x → 0 < x ∧ 0 < pP x ∧ 5 / 9 * x ^ 2 ≤ pP x ∧ 1 ≤ x := fun x hx =>
    ⟨by linarith, pP_pos (by linarith), pP_ge hx.le, by linarith⟩
  refine ⟨memLp_of_le_inv (C := 9 / 5) (by unfold xP₂ pP; fun_prop) fun x hx => ?_,
    memLp_of_le_inv (C := 81 / 25) (by unfold xP₃ pP; fun_prop) fun x hx => ?_,
    memLp_of_le_inv (C := 9 / 5) (by unfold xP₄ pP; fun_prop) fun x hx => ?_,
    memLp_of_le_inv (C := 9 / 5 * π) (by unfold xP₅ pP; fun_prop) fun x hx => ?_,
    memLp_of_le_inv (C := 9 / 5 * π) (by unfold xP₆ pP; fun_prop) fun x hx => ?_,
    memLp_of_le_inv (C := 81 / 25) (by unfold xP₇ pP; fun_prop) fun x hx => ?_⟩ <;>
  obtain ⟨hx0, hp, hp5, hx1⟩ := key x hx
  · obtain ⟨hw0, hw1, -, -⟩ := wF_bounds x
    unfold xP₂; rw [abs_of_nonneg (by positivity), div_le_div_iff₀ hp hx0]
    nlinarith [mul_le_mul_of_nonneg_left hw1 (le_of_lt (mul_pos hx0 hx0))]
  · obtain ⟨hw0, hw1, -, -⟩ := wF_bounds x
    unfold xP₃; rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hx0]
    have h2 : (5 / 9 * x ^ 2) ^ 2 ≤ pP x ^ 2 := pow_le_pow_left₀ (by positivity) hp5 2
    have hx3 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hw1 (le_of_lt (pow_pos hx0 3))]
  · obtain ⟨hw0, hw1, -, -⟩ := wF_bounds x
    unfold xP₄; rw [abs_of_nonneg (by positivity), div_le_div_iff₀ hp hx0]
    nlinarith [mul_le_mul_of_nonneg_left hw1 hx0.le]
  · obtain ⟨-, -, hw1, -⟩ := wF_bounds x
    unfold xP₅; rw [abs_div, abs_of_pos hp, abs_mul, abs_of_pos hx0, div_le_div_iff₀ hp hx0]
    nlinarith [mul_le_mul_of_nonneg_left hw1 (le_of_lt (mul_pos hx0 hx0)),
      mul_le_mul_of_nonneg_left hp5 pi_pos.le]
  · obtain ⟨-, -, hw1, -⟩ := wF_bounds x
    unfold xP₆; rw [abs_div, abs_of_pos hp, div_le_div_iff₀ hp hx0]
    nlinarith [mul_le_mul_of_nonneg_left hw1 hx0.le, mul_le_mul_of_nonneg_left hp5 pi_pos.le,
      mul_le_mul_of_nonneg_left (by nlinarith : x ≤ x ^ 2) pi_pos.le]
  · obtain ⟨hw0, hw1, -, -⟩ := wF_bounds x
    unfold xP₇; rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hx0]
    have h2 : (5 / 9 * x ^ 2) ^ 2 ≤ pP x ^ 2 := pow_le_pow_left₀ (by positivity) hp5 2
    have hx3 : x ≤ x ^ 4 := by nlinarith [pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 4)]
    nlinarith [mul_le_mul_of_nonneg_left hw1 hx0.le]

/-! ### The `nN` calculus -/

/-- `nN f ^ 2 = ∫_{3/2}^∞ f²`. -/
theorem nN_sq (f : ℝ → ℝ) : nN f ^ 2 = ∫ x in Ioi (3 / 2 : ℝ), f x ^ 2 := by
  unfold nN; exact Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)

/-- `nN |f| = nN f`. -/
theorem nN_abs (f : ℝ → ℝ) : nN (fun x => |f x|) = nN f := by
  unfold nN; simp only [sq_abs]

/-- `nN (a·f) = a·nN f` for `a ≥ 0`. -/
theorem nN_const_mul {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) : nN (fun x => a * f x) = a * nN f := by
  unfold nN
  simp only [mul_pow, integral_const_mul]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Domination: `|f| ≤ g` on `(3/2, ∞)` with `g ∈ L²` gives `nN f ≤ nN g`. -/
theorem nN_mono {f g : ℝ → ℝ} (h : ∀ x, 3 / 2 < x → |f x| ≤ g x)
    (hg : MemLp g 2 (volume.restrict (Ioi (3 / 2)))) : nN f ≤ nN g := by
  unfold nN
  refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
    ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg) ?_)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
  show f x ^ 2 ≤ g x ^ 2
  rw [← sq_abs (f x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h x hx) 2

/-- Minkowski for `nN` on nonnegative square-integrable functions. -/
theorem nN_add_le {f g : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f 2 (volume.restrict (Ioi (3 / 2)))) (hg : MemLp g 2 (volume.restrict (Ioi (3 / 2)))) :
    nN (fun x => f x + g x) ≤ nN f + nN g := by
  set μ := volume.restrict (Ioi (3 / 2 : ℝ))
  have hf2 : Integrable (fun x => f x ^ 2) μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hg2 : Integrable (fun x => g x ^ 2) μ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun x => f x * g x) μ := by
    refine Integrable.mono' ((hf2.add hg2).div_const 2) (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hg0 x))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f x - g x)]
  have hCS : ∫ x, f x * g x ∂μ ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
    have h := integral_mul_abs_le hf0 hf hg
    refine le_trans (le_of_eq ?_) h
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show f x * g x = f x * |g x|; rw [abs_of_nonneg (hg0 x)])
  have hexp : ∫ x, (f x + g x) ^ 2 ∂μ
      = (∫ x, f x ^ 2 ∂μ) + 2 * (∫ x, f x * g x ∂μ) + ∫ x, g x ^ 2 ∂μ := by
    have e1 : ∫ x, (f x + g x) ^ 2 ∂μ = ∫ x, ((f x ^ 2 + 2 * (f x * g x)) + g x ^ 2) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have h12 : Integrable (fun x => f x ^ 2 + 2 * (f x * g x)) μ := hf2.add (hfg.const_mul 2)
    rw [e1, integral_add h12 hg2, integral_add hf2 (hfg.const_mul 2), integral_const_mul]
  have hA := integral_nonneg (μ := μ) (f := fun x => f x ^ 2) fun x => sq_nonneg (f x)
  have hB := integral_nonneg (μ := μ) (f := fun x => g x ^ 2) fun x => sq_nonneg (g x)
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  unfold nN
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  refine Real.sqrt_le_sqrt ?_
  change ∫ x, (f x + g x) ^ 2 ∂μ ≤ (√(∫ x, f x ^ 2 ∂μ) + √(∫ x, g x ^ 2 ∂μ)) ^ 2
  rw [hexp]
  nlinarith

/-! ### The ramp on `[3/2, 2]` -/

/-- An integrand vanishing on `(2, ∞)` integrates over `(3/2, ∞)` as over `[3/2, 2]`. -/
theorem setIntegral_Ioi_eq_interval {f : ℝ → ℝ} (hf : ∀ x, 2 < x → f x = 0) :
    ∫ x in Ioi (3 / 2 : ℝ), f x = ∫ x in (3 / 2 : ℝ)..2, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self fun x hx => ?_
  simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hx
  exact hf x (hx.2 hx.1)

/-- On `[3/2, 2]` the ramp's derivative is `π sin(2πx − 3π)` and its second derivative `2π² cos(2πx − 3π)`. -/
theorem wF_eq_on_Icc {x : ℝ} (hx : x ∈ Icc (3 / 2 : ℝ) 2) :
    wF₁ x = π * Real.sin (2 * π * x - 3 * π) ∧ wF₂ x = 2 * π ^ 2 * Real.cos (2 * π * x - 3 * π) := by
  have hcl : clampW x = x := by unfold clampW; rw [min_eq_left hx.2, max_eq_right hx.1]
  unfold wF₁ wF₂
  rw [hcl, ite_eq_left hx.2, show 2 * π * (x - 3 / 2) = 2 * π * x - 3 * π by ring]
  exact ⟨rfl, rfl⟩

/-- `∫_{3/2}^∞ w′² = π²/4`. -/
theorem integral_wF₁_sq : ∫ x in Ioi (3 / 2 : ℝ), wF₁ x ^ 2 = π ^ 2 / 4 := by
  rw [setIntegral_Ioi_eq_interval fun x hx => by rw [(wF_of_two_le hx.le).2]; ring]
  rw [intervalIntegral.integral_congr (g := fun x => π ^ 2 * Real.sin (2 * π * x - 3 * π) ^ 2)
    (fun x hx => by rw [(wF_eq_on_Icc (by rwa [uIcc_of_le (by norm_num)] at hx)).1]; ring)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_sub (fun x => Real.sin x ^ 2) (by positivity : (2 * π) ≠ 0) (3 * π)]
  rw [show 2 * π * (3 / 2) - 3 * π = 0 by ring, show 2 * π * 2 - 3 * π = π by ring, integral_sin_sq]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi, smul_eq_mul]
  field_simp
  ring

/-- `∫_{3/2}^∞ w″² = π⁴`. -/
theorem integral_wF₂_sq : ∫ x in Ioi (3 / 2 : ℝ), wF₂ x ^ 2 = π ^ 4 := by
  rw [setIntegral_Ioi_eq_interval fun x hx => by unfold wF₂; rw [ite_eq_right (not_le.mpr hx)]; ring]
  rw [intervalIntegral.integral_congr (g := fun x => 4 * π ^ 4 * Real.cos (2 * π * x - 3 * π) ^ 2)
    (fun x hx => by rw [(wF_eq_on_Icc (by rwa [uIcc_of_le (by norm_num)] at hx)).2]; ring)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_sub (fun x => Real.cos x ^ 2) (by positivity : (2 * π) ≠ 0) (3 * π)]
  rw [show 2 * π * (3 / 2) - 3 * π = 0 by ring, show 2 * π * 2 - 3 * π = π by ring, integral_cos_sq]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi, smul_eq_mul]
  field_simp
  ring

/-- The one-IBP identity `∫_{3/2}^∞ (2xw′/p + w″)² = 6‖xw′/p‖² + 2‖w′/p‖² + π⁴`
(`−(2x/p)′ = 2(x²+1)/p²`, `w′(3/2) = w′(2) = 0`). -/
theorem integral_ibp_sq :
    ∫ x in Ioi (3 / 2 : ℝ), (2 * x * wF₁ x / pP x + wF₂ x) ^ 2 = 6 * nN xP₅ ^ 2 + 2 * nN xP₆ ^ 2 + π ^ 4 := by
  -- the explicit ramp derivatives on `[3/2, 2]`
  set s : ℝ → ℝ := fun x => π * Real.sin (2 * π * x - 3 * π) with hs
  set c : ℝ → ℝ := fun x => 2 * π ^ 2 * Real.cos (2 * π * x - 3 * π) with hc
  have hI : uIcc (3 / 2 : ℝ) 2 = Icc (3 / 2) 2 := uIcc_of_le (by norm_num)
  have hp : ∀ x ∈ uIcc (3 / 2 : ℝ) 2, pP x ≠ 0 := fun x hx => by
    rw [hI] at hx; exact (pP_pos (by linarith [hx.1])).ne'
  have hpc : ContinuousOn pP (uIcc (3 / 2 : ℝ) 2) := by unfold pP; fun_prop
  -- reduce the three `(3/2, ∞)` integrals to `[3/2, 2]` with the explicit derivatives
  rw [nN_sq, nN_sq]
  rw [setIntegral_Ioi_eq_interval fun x hx => by
      rw [(wF_of_two_le hx.le).2]; unfold wF₂; rw [ite_eq_right (not_le.mpr hx)]; ring,
    setIntegral_Ioi_eq_interval fun x hx => by unfold xP₅; rw [(wF_of_two_le hx.le).2]; ring,
    setIntegral_Ioi_eq_interval fun x hx => by unfold xP₆; rw [(wF_of_two_le hx.le).2]; ring]
  rw [intervalIntegral.integral_congr (g := fun x => (2 * x * s x / pP x + c x) ^ 2) (fun x hx => by
      rw [hI] at hx; obtain ⟨h1, h2⟩ := wF_eq_on_Icc hx; simp only [h1, h2, hs, hc]),
    intervalIntegral.integral_congr (f := fun x => xP₅ x ^ 2) (g := fun x => (x * s x / pP x) ^ 2) (fun x hx => by
      rw [hI] at hx; obtain ⟨h1, -⟩ := wF_eq_on_Icc hx; simp only [xP₅, h1, hs]),
    intervalIntegral.integral_congr (f := fun x => xP₆ x ^ 2) (g := fun x => (s x / pP x) ^ 2) (fun x hx => by
      rw [hI] at hx; obtain ⟨h1, -⟩ := wF_eq_on_Icc hx; simp only [xP₆, h1, hs])]
  -- `∫ c² = π⁴`
  have hc2 : ∫ x in (3 / 2 : ℝ)..2, c x ^ 2 = π ^ 4 := by
    have := integral_wF₂_sq
    rw [setIntegral_Ioi_eq_interval fun x hx => by unfold wF₂; rw [ite_eq_right (not_le.mpr hx)]; ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hI] at hx; obtain ⟨-, h2⟩ := wF_eq_on_Icc hx; simp only [h2, hc]
  -- integration by parts: `u = 2x/p`, `v = s²`, `u′ = −2(x²+1)/p²`, `v′ = 2 s c`
  have hs_c : Continuous s := by simp only [hs]; fun_prop
  have hc_c : Continuous c := by simp only [hc]; fun_prop
  have hu : ∀ x ∈ uIcc (3 / 2 : ℝ) 2, HasDerivAt (fun x => 2 * x / pP x) (-2 * (x ^ 2 + 1) / pP x ^ 2) x := by
    intro x hx
    have hpd : HasDerivAt pP (2 * x) x := by
      have := ((hasDerivAt_pow 2 x).sub_const 1)
      refine this.congr_deriv ?_
      simp
    have := ((hasDerivAt_id x).const_mul 2).div hpd (hp x hx)
    refine this.congr_deriv ?_
    have := hp x hx
    field_simp
    unfold pP; simp only [id_eq]; ring
  have hv : ∀ x ∈ uIcc (3 / 2 : ℝ) 2, HasDerivAt (fun x => s x ^ 2) (2 * s x * c x) x := by
    intro x _
    have := ((((hasDerivAt_id x).const_mul (2 * π)).sub_const (3 * π)).sin.const_mul π).pow 2
    refine this.congr_deriv ?_
    simp only [hs, hc, id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hu' : IntervalIntegrable (fun x => -2 * (x ^ 2 + 1) / pP x ^ 2) volume (3 / 2) 2 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.div₀ (by fun_prop) (hpc.pow 2) fun x hx => pow_ne_zero 2 (hp x hx)
  have hv' : IntervalIntegrable (fun x => 2 * s x * c x) volume (3 / 2) 2 :=
    (by fun_prop : Continuous fun x => 2 * s x * c x).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hs0 : s (3 / 2) = 0 := by simp only [hs]; rw [show 2 * π * (3 / 2 : ℝ) - 3 * π = 0 by ring]; simp
  have hs2 : s 2 = 0 := by simp only [hs]; rw [show 2 * π * (2 : ℝ) - 3 * π = π by ring]; simp
  rw [hs0, hs2] at hibp
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, zero_sub] at hibp
  -- the integrands on `[3/2, 2]` are all continuous, so the integrals split
  have hA : IntervalIntegrable (fun x => (x * s x / pP x) ^ 2) volume (3 / 2) 2 :=
    ContinuousOn.intervalIntegrable ((ContinuousOn.div₀ (by fun_prop) hpc hp).pow 2)
  have hB : IntervalIntegrable (fun x => (s x / pP x) ^ 2) volume (3 / 2) 2 :=
    ContinuousOn.intervalIntegrable ((ContinuousOn.div₀ (by fun_prop) hpc hp).pow 2)
  have hC : IntervalIntegrable (fun x => c x ^ 2) volume (3 / 2) 2 :=
    (by fun_prop : Continuous fun x => c x ^ 2).intervalIntegrable _ _
  have hD : IntervalIntegrable (fun x => 2 * x / pP x * (2 * s x * c x)) volume (3 / 2) 2 :=
    ContinuousOn.intervalIntegrable ((ContinuousOn.div₀ (by fun_prop) hpc hp).mul (by fun_prop))
  have hE : IntervalIntegrable (fun x => -2 * (x ^ 2 + 1) / pP x ^ 2 * s x ^ 2) volume (3 / 2) 2 :=
    hu'.mul_continuousOn (by fun_prop)
  -- expand the square and assemble
  have hexp : ∫ x in (3 / 2 : ℝ)..2, (2 * x * s x / pP x + c x) ^ 2
      = ∫ x in (3 / 2 : ℝ)..2, ((6 * (x * s x / pP x) ^ 2 + 2 * (s x / pP x) ^ 2 + c x ^ 2)
          + (2 * x / pP x * (2 * s x * c x) + -2 * (x ^ 2 + 1) / pP x ^ 2 * s x ^ 2)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have := hp x hx
    field_simp
    ring
  rw [hexp, intervalIntegral.integral_add ((hA.const_mul 6).add (hB.const_mul 2) |>.add hC) (hD.add hE),
    intervalIntegral.integral_add (hD) hE, intervalIntegral.integral_add ((hA.const_mul 6).add (hB.const_mul 2)) hC,
    intervalIntegral.integral_add (hA.const_mul 6) (hB.const_mul 2), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hc2, hibp]
  ring

/-- `2xw′/p + w″` lies in `L²(3/2, ∞)`. -/
theorem memLp_ibp :
    MemLp (fun x => 2 * x * wF₁ x / pP x + wF₂ x) 2 (volume.restrict (Ioi (3 / 2))) := by
  have h1 := continuous_wF.2.measurable
  have h2 := measurable_wF₂
  refine memLp_of_le_inv (C := 2 * (16 / 5 * π + 2 * π ^ 2)) (by unfold pP; fun_prop) fun x hx => ?_
  have hx0 : 0 < x := by linarith
  have hp : 0 < pP x := pP_pos (by linarith)
  rcases le_or_gt x 2 with hx2 | hx2
  · obtain ⟨-, -, hw1, hw2⟩ := wF_bounds x
    have hp54 : 5 / 4 ≤ pP x := by unfold pP; nlinarith
    have hK : |2 * x * wF₁ x / pP x + wF₂ x| ≤ 16 / 5 * π + 2 * π ^ 2 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ hw2)
      rw [abs_div, abs_of_pos hp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * x), div_le_iff₀ hp]
      nlinarith [mul_le_mul_of_nonneg_left hw1 (by positivity : (0 : ℝ) ≤ 2 * x), pi_pos]
    refine hK.trans ?_
    rw [le_div_iff₀ hx0]
    nlinarith [pi_pos]
  · rw [(wF_of_two_le hx2.le).2]
    unfold wF₂; rw [ite_eq_right (not_le.mpr hx2)]
    simp only [mul_zero, zero_div, add_zero, abs_zero]
    positivity

end Cvs.L2a.RampIntegrals

end
