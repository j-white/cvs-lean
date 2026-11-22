import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.Zeta.Digamma.DigammaProductDerivative
import Cvs.Zeta.TrigammaSeries

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Lévy density and digamma series at a general abscissa `σ`

`densityS σ u = e^{−σu}/(1 − e^{−u})` sums the poles `σ + k`, and the three series
`Im ψ(σ + iy)`, `Re ψ(σ + iy) − ψ(σ)`, `Re ψ'(σ + iy)` are its term sums.
-/

namespace Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa

open Real MeasureTheory Set
open Complex (I)

/-- The Lévy density with poles at `σ + k`. -/
noncomputable def densityS (σ u : ℝ) : ℝ := Real.exp (-(σ * u)) / (1 - Real.exp (-u))

theorem hasSum_expS (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ => Real.exp (-((σ + (k : ℝ)) * u))) (densityS σ u) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : HasSum (fun k : ℕ => (Real.exp (-u)) ^ k) (1 - Real.exp (-u))⁻¹ :=
    hasSum_geometric_of_lt_one hr0 hr1
  have hcongr : ∀ k : ℕ, Real.exp (-(σ * u)) * (Real.exp (-u)) ^ k
      = Real.exp (-((σ + (k : ℝ)) * u)) := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have := hgeom.mul_left (Real.exp (-(σ * u)))
  rw [funext hcongr] at this
  rwa [densityS, div_eq_mul_inv]

theorem densityS_pos (σ : ℝ) {u : ℝ} (hu : 0 < u) : 0 < densityS σ u := by
  have h1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold densityS
  have : (0:ℝ) < 1 - Real.exp (-u) := by linarith
  positivity

/-- Above the abscissa `1/4` the density is dominated by `densityU`. -/
theorem densityS_le_densityU {σ : ℝ} (hσ : 1 / 4 ≤ σ) {u : ℝ} (hu : 0 < u) :
    densityS σ u ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
  have h1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : (0:ℝ) < 1 - Real.exp (-u) := by linarith
  unfold densityS Cvs.WeilForm.Archimedean.LevyDensity.densityU
  apply div_le_div_of_nonneg_right _ hden.le
  apply Real.exp_le_exp.mpr
  nlinarith

theorem measurable_densityS (σ : ℝ) : Measurable (densityS σ) := by
  unfold densityS
  fun_prop

/-- Integrability at abscissa `σ ≥ 1/4` follows from integrability at `1/4`. -/
theorem integrableOn_densityS_mul {σ : ℝ} (hσ : 1 / 4 ≤ σ) {g : ℝ → ℝ} (hm : Measurable g)
    (hint : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (g 0 - g (u / 2))) (Ioi 0)) :
    IntegrableOn (fun u => densityS σ u * (g 0 - g (u / 2))) (Ioi 0) := by
  have hgm : Measurable (fun u => g 0 - g (u / 2)) :=
    measurable_const.sub (hm.comp (measurable_id.div_const 2))
  refine Integrable.mono' hint.norm ((measurable_densityS σ).mul hgm).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (densityS_pos σ hu), abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu)]
  exact mul_le_mul_of_nonneg_right (densityS_le_densityU hσ hu) (abs_nonneg _)

/-- **Summation under the Lévy integral** at abscissa `σ`. -/
theorem hasSum_levyS (σ : ℝ) {g : ℝ → ℝ} (hm : Measurable g)
    (hint : IntegrableOn (fun u => densityS σ u * (g 0 - g (u / 2))) (Ioi 0)) :
    HasSum (fun k : ℕ => ∫ u in Ioi (0:ℝ), Real.exp (-((σ + (k : ℝ)) * u)) * (g 0 - g (u / 2)))
      (∫ u in Ioi (0:ℝ), densityS σ u * (g 0 - g (u / 2))) := by
  have hgm : Measurable (fun u => g 0 - g (u / 2)) :=
    measurable_const.sub (hm.comp (measurable_id.div_const 2))
  refine hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (bound := fun k u => Real.exp (-((σ + (k : ℝ)) * u)) * |g 0 - g (u / 2)|) ?_ ?_ ?_ ?_ ?_
  · intro k
    exact ((by fun_prop : Measurable fun u : ℝ => Real.exp (-((σ + (k : ℝ)) * u))).mul
      hgm).aestronglyMeasurable
  · intro k
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact ((hasSum_expS σ hu).mul_right _).summable
  · have heq : ∀ u ∈ Ioi (0:ℝ),
        ‖densityS σ u * (g 0 - g (u / 2))‖
          = ∑' k : ℕ, Real.exp (-((σ + (k : ℝ)) * u)) * |g 0 - g (u / 2)| := by
      intro u hu
      rw [((hasSum_expS σ hu).mul_right _).tsum_eq, Real.norm_eq_abs, abs_mul,
        abs_of_pos (densityS_pos σ hu)]
    exact hint.norm.congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun u hu => heq u hu))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact (hasSum_expS σ hu).mul_right _

/-- The digamma point `σ + iy`. -/
noncomputable def zs (σ y : ℝ) : ℂ := (σ : ℂ) + (y : ℂ) * I

theorem zs_re (σ y : ℝ) : (zs σ y).re = σ := by simp [zs]

theorem zs_mem {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : ℝ) :
    zs σ y ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have h := congrArg Complex.re hn
  rw [zs_re, Complex.intCast_re] at h
  have h0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) < 1 := by linarith
  have h0' : (0 : ℤ) < n := by exact_mod_cast h0
  have h1' : n < (1 : ℤ) := by exact_mod_cast h1
  omega

/-- The `k`-th term of `Im ψ(σ + iy)`. -/
noncomputable def imTermS (σ y : ℝ) (k : ℕ) : ℝ := y / ((σ + (k : ℝ)) ^ 2 + y ^ 2)

/-- The `k`-th term of `Re ψ(σ + iy) − ψ(σ)`. -/
noncomputable def deficitS (σ y : ℝ) (k : ℕ) : ℝ :=
  1 / (σ + (k : ℝ)) - (σ + (k : ℝ)) / ((σ + (k : ℝ)) ^ 2 + y ^ 2)

/-- The `k`-th term of `Re ψ'(σ + iy)`. -/
noncomputable def cutTermS (σ y : ℝ) (k : ℕ) : ℝ :=
  ((σ + (k : ℝ)) ^ 2 - y ^ 2) / ((σ + (k : ℝ)) ^ 2 + y ^ 2) ^ 2

theorem inv_shift_re (σ y : ℝ) (n : ℕ) :
    (1 / (zs σ y + (n : ℂ) + 1)).re = (σ + ((n : ℝ) + 1)) / ((σ + ((n : ℝ) + 1)) ^ 2 + y ^ 2) := by
  have hw : zs σ y + (n : ℂ) + 1 = ((σ + ((n : ℝ) + 1) : ℝ) : ℂ) + (y : ℂ) * I := by
    unfold zs; push_cast; ring
  rw [hw, one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
    add_zero, zero_add]
  ring

theorem inv_shift_im (σ y : ℝ) (n : ℕ) :
    (1 / (zs σ y + (n : ℂ) + 1)).im = -(y / ((σ + ((n : ℝ) + 1)) ^ 2 + y ^ 2)) := by
  have hw : zs σ y + (n : ℂ) + 1 = ((σ + ((n : ℝ) + 1) : ℝ) : ℂ) + (y : ℂ) * I := by
    unfold zs; push_cast; ring
  rw [hw, one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
    add_zero, zero_add]
  ring

theorem inv_zs_re (σ y : ℝ) : (1 / zs σ y).re = σ / (σ ^ 2 + y ^ 2) := by
  unfold zs
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
    add_zero, zero_add]
  ring

theorem inv_zs_im (σ y : ℝ) : (1 / zs σ y).im = -(y / (σ ^ 2 + y ^ 2)) := by
  unfold zs
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
    add_zero, zero_add]
  ring

theorem inv_natCast_add_one_im (n : ℕ) : (1 / ((n : ℂ) + 1)).im = 0 := by
  have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_im]

/-- **`Im ψ(σ + iy)` as a series.** -/
theorem hasSum_imTermS {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    HasSum (imTermS σ y) (Complex.digamma (zs σ y)).im := by
  have hre : 0 < (zs σ y).re := by rw [zs_re]; exact hσ
  have h := Complex.hasSum_im (Cvs.Digamma.hasSum_digamma hre)
  have hterm : (fun n : ℕ => (1 / ((n : ℂ) + 1) - 1 / (zs σ y + (n : ℂ) + 1)).im)
      = fun n => imTermS σ y (n + 1) := by
    funext n
    rw [Complex.sub_im, inv_natCast_add_one_im, inv_shift_im σ y n]
    unfold imTermS; push_cast; ring
  have hsum : (Complex.digamma (zs σ y) + (Real.eulerMascheroniConstant : ℂ) + 1 / zs σ y).im
      = (Complex.digamma (zs σ y)).im - ∑ i ∈ Finset.range 1, imTermS σ y i := by
    rw [Finset.sum_range_one, Complex.add_im, Complex.add_im, Complex.ofReal_im, inv_zs_im σ y]
    unfold imTermS; push_cast; ring
  rw [hterm, hsum] at h
  exact (hasSum_nat_add_iff' 1).mp h

/-- **`Re ψ(σ + iy) − ψ(σ)` as a series.** -/
theorem hasSum_deficitS {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    HasSum (deficitS σ y) ((Complex.digamma (zs σ y)).re - (Complex.digamma (σ : ℂ)).re) := by
  have hre : 0 < (zs σ y).re := by rw [zs_re]; exact hσ
  have hre0 : 0 < ((σ : ℂ)).re := by simpa using hσ
  have hz := Complex.hasSum_re (Cvs.Digamma.hasSum_digamma hre)
  have h0 := Complex.hasSum_re (Cvs.Digamma.hasSum_digamma hre0)
  have hsub := hz.sub h0
  have hterm : (fun n : ℕ => (1 / ((n : ℂ) + 1) - 1 / (zs σ y + (n : ℂ) + 1)).re
      - (1 / ((n : ℂ) + 1) - 1 / ((σ : ℂ) + (n : ℂ) + 1)).re) = fun n => deficitS σ y (n + 1) := by
    funext n
    have hz0 : (1 / ((σ : ℂ) + (n : ℂ) + 1)).re = 1 / (σ + ((n : ℝ) + 1)) := by
      have : ((σ : ℂ) + (n : ℂ) + 1) = (((σ + ((n : ℝ) + 1)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [Complex.sub_re, Complex.sub_re, inv_shift_re σ y n, hz0]
    unfold deficitS; push_cast; ring
  have hsum : (Complex.digamma (zs σ y) + (Real.eulerMascheroniConstant : ℂ) + 1 / zs σ y).re
        - (Complex.digamma (σ : ℂ) + (Real.eulerMascheroniConstant : ℂ) + 1 / (σ : ℂ)).re
      = ((Complex.digamma (zs σ y)).re - (Complex.digamma (σ : ℂ)).re)
        - ∑ i ∈ Finset.range 1, deficitS σ y i := by
    have hσ0 : (1 / (σ : ℂ)).re = 1 / σ := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [Finset.sum_range_one, Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.ofReal_re, inv_zs_re σ y, hσ0]
    unfold deficitS; push_cast; ring
  rw [hterm, hsum] at hsub
  exact (hasSum_nat_add_iff' 1).mp hsub

theorem cutTermS_eq_re {σ : ℝ} (hσ : 0 < σ) (y : ℝ) (k : ℕ) :
    cutTermS σ y k = (1 / (zs σ y + k) ^ 2).re := by
  unfold cutTermS zs
  set a : ℝ := σ + (k : ℝ) with ha
  have hz : (σ : ℂ) + (y : ℂ) * I + (k : ℂ) = ((a : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [ha]; push_cast; ring_nf
  rw [hz]
  have ha0 : 0 < a := by rw [ha]; positivity
  have hne : ((a : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hpos : (a ^ 2 + y ^ 2) ^ 2 ≠ 0 := by positivity
  have hinv : 1 / (((a : ℝ) : ℂ) + (y : ℂ) * I) ^ 2
      = (((a ^ 2 - y ^ 2) / (a ^ 2 + y ^ 2) ^ 2 : ℝ) : ℂ)
        + (((-2 * a * y) / (a ^ 2 + y ^ 2) ^ 2 : ℝ) : ℂ) * I := by
    rw [div_eq_iff (pow_ne_zero 2 hne)]
    apply Complex.ext
    · simp only [Complex.one_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, sq,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, zero_sub]
      field_simp
      ring
    · simp only [Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, sq,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, zero_sub]
      field_simp
      ring
  rw [hinv]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- **`Re ψ'(σ + iy)` as a series.** -/
theorem hasSum_cutTermS {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : ℝ) :
    HasSum (cutTermS σ y) (deriv Complex.digamma (zs σ y)).re := by
  have h := Complex.hasSum_re (Cvs.Zeta.Base.Stirling.hasSum_trigamma (zs_mem hσ0 hσ1 y))
  have hf : (fun k : ℕ => (1 / (zs σ y + k) ^ 2).re) = cutTermS σ y :=
    funext fun k => (cutTermS_eq_re hσ0 y k).symm
  rwa [hf] at h

theorem summable_imTermS {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : Summable (imTermS σ y) :=
  (hasSum_imTermS hσ y).summable

theorem summable_deficitS {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : Summable (deficitS σ y) :=
  (hasSum_deficitS hσ y).summable

theorem summable_cutTermS {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : ℝ) :
    Summable (cutTermS σ y) :=
  (hasSum_cutTermS hσ0 hσ1 y).summable

end Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa
