import Mathlib
import Cvs.Upstream.DirichletKernelDiniTest

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Poisson summation for a compactly supported profile, by Dini's test

For `g` integrable, vanishing off `[−1, 1]`, `0 < θ ≤ N₀`, the periodization `P(y) = Σ_{|n| ≤ N₀} g((n + y)/θ)` has
cosine coefficients `∫_{−½}^{½} P(y) cos(2πmy) dy = θ G(mθ)`, `G(η) = ∫ g(s) cos(2πηs) ds`; if `P` is
Lipschitz at `0` and bounded, `Σ_n g(n/θ) = lim_M θ(G(0) + 2Σ_{m=1}^M G(mθ))`.
-/

namespace Cvs.Upstream.PoissonSummationDini

open Real MeasureTheory Filter Topology

/-- The cosine transform `G(η) = ∫ g(s) cos(2πηs) ds`. -/
noncomputable def G (g : ℝ → ℝ) (η : ℝ) : ℝ := ∫ s, g s * cos (2 * π * η * s)

/-- The periodization, indexed by `k < 2N₀ + 1`, `n = k − N₀`. -/
noncomputable def per (g : ℝ → ℝ) (θ : ℝ) (N₀ : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 * N₀ + 1), g (((k : ℝ) - N₀ + y) / θ)

variable {g : ℝ → ℝ} {θ : ℝ} {N₀ : ℕ}

/-- **The cosine coefficients of the periodization.** -/
theorem coeff (hg : Integrable g) (hsupp : ∀ s, 1 < |s| → g s = 0) (hθ : 0 < θ) (hN : θ ≤ N₀) (m : ℕ) :
    ∫ y in (-(1 / 2 : ℝ))..(1 / 2), per g θ N₀ y * cos (2 * π * m * y) = θ * G g (m * θ) := by
  set f : ℝ → ℝ := fun z => g (z / θ) * cos (2 * π * m * z) with hf
  have hfi : Integrable f := by
    have h1 : Integrable (fun z => g (z / θ)) := hg.comp_div hθ.ne'
    exact h1.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  -- each term is a shifted piece of `f`
  have hterm : ∀ k ∈ Finset.range (2 * N₀ + 1),
      ∫ y in (-(1 / 2 : ℝ))..(1 / 2), g (((k : ℝ) - N₀ + y) / θ) * cos (2 * π * m * y)
        = ∫ z in ((k : ℝ) - N₀ - 1 / 2)..((k : ℝ) - N₀ + 1 / 2), f z := by
    intro k _
    have := intervalIntegral.integral_comp_add_left (a := -(1 / 2 : ℝ)) (b := 1 / 2) f ((k : ℝ) - N₀)
    rw [show (k : ℝ) - N₀ + -(1 / 2) = (k : ℝ) - N₀ - 1 / 2 by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    simp only [hf]
    have e : 2 * π * m * ((k : ℝ) - N₀ + y) = 2 * π * m * y + ((m : ℤ) * ((k : ℤ) - N₀) : ℤ) * (2 * π) := by
      push_cast; ring
    rw [e, cos_add_int_mul_two_pi]
  have hsplit : ∫ y in (-(1 / 2 : ℝ))..(1 / 2), per g θ N₀ y * cos (2 * π * m * y)
      = ∑ k ∈ Finset.range (2 * N₀ + 1), ∫ y in (-(1 / 2 : ℝ))..(1 / 2), g (((k : ℝ) - N₀ + y) / θ) * cos (2 * π * m * y) := by
    unfold per
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum]
    intro k _
    have h1 : Integrable (fun y => g (((k : ℝ) - N₀ + y) / θ)) := by
      have := (hg.comp_div hθ.ne').comp_add_left ((k : ℝ) - N₀)
      simpa using this
    exact (h1.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one _)).intervalIntegrable
  rw [hsplit, Finset.sum_congr rfl hterm]
  -- the pieces join
  have hjoin := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) - N₀ - 1 / 2)
    (n := 2 * N₀ + 1) (f := f) (μ := volume) (fun k _ => hfi.intervalIntegrable)
  have e1 : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) - N₀ - 1 / 2 = (k : ℝ) - N₀ + 1 / 2 := fun k => by push_cast; ring
  simp only [e1] at hjoin
  rw [hjoin]
  simp only [Nat.cast_zero, zero_sub]
  have e2 : ((2 * N₀ : ℕ) : ℝ) - N₀ + 1 / 2 = N₀ + 1 / 2 := by push_cast; ring
  rw [e2]
  -- extend to the line
  have hext : ∫ z in (-(N₀ : ℝ) - 1 / 2)..(N₀ + 1 / 2), f z = ∫ z, f z := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hz
    have : 1 < |z / θ| := by
      rw [abs_div, abs_of_pos hθ, one_lt_div hθ]
      rcases hz with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp only [hf, hsupp _ this, zero_mul]
  rw [hext]
  -- rescale
  have hsc := Measure.integral_comp_div (fun s => g s * cos (2 * π * (m * θ) * s)) θ
  rw [abs_of_pos hθ, smul_eq_mul] at hsc
  unfold G
  rw [← hsc]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hf]
  rw [show 2 * π * ((m : ℝ) * θ) * (z / θ) = 2 * π * m * z by field_simp]

/-- `|sin(πy)| ≥ 2|y|` on `[−½, ½]`. -/
theorem two_abs_le_abs_sin {y : ℝ} (hy : |y| ≤ 1 / 2) : 2 * |y| ≤ |sin (π * y)| := by
  have h0 : 0 ≤ π * |y| := by positivity
  have h1 : π * |y| ≤ π / 2 := by nlinarith [pi_pos]
  have := mul_le_sin h0 h1
  have e : |sin (π * y)| = sin (π * |y|) := by
    rcases le_total 0 y with h | h
    · have hy' : y ≤ 1 / 2 := (le_abs_self y).trans hy
      rw [abs_of_nonneg h, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]))]
    · have hy' : -(1 / 2) ≤ y := by have := neg_abs_le y; linarith
      rw [abs_of_nonpos h, show π * -y = -(π * y) by ring, sin_neg,
        abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [pi_pos]) (by nlinarith [pi_pos]))]
  rw [e]
  have : 2 / π * (π * |y|) = 2 * |y| := by field_simp
  linarith

/-- **Poisson summation** at a point where the periodization is Lipschitz. -/
theorem poisson (hg : Integrable g) (hgm : Measurable g) (hsupp : ∀ s, 1 < |s| → g s = 0) (hθ : 0 < θ)
    (hN : θ ≤ N₀) {B L δ : ℝ} (hB : ∀ y, |per g θ N₀ y| ≤ B) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hlip : ∀ y, |y| ≤ δ → |per g θ N₀ y - per g θ N₀ 0| ≤ L * |y|) :
    Tendsto (fun M : ℕ => θ * (G g 0 + 2 * ∑ m ∈ Finset.Icc 1 M, G g (m * θ))) atTop
      (𝓝 (∑ k ∈ Finset.range (2 * N₀ + 1), g (((k : ℝ) - N₀) / θ))) := by
  have hper0 : per g θ N₀ 0 = ∑ k ∈ Finset.range (2 * N₀ + 1), g (((k : ℝ) - N₀) / θ) := by
    unfold per; simp
  rw [← hper0]
  have hpm : Measurable (per g θ N₀) := by
    unfold per; apply Finset.measurable_sum; intro k _; exact hgm.comp (by fun_prop)
  have hon : IntegrableOn (per g θ N₀) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    Measure.integrableOn_of_bounded (M := B) (by simp) hpm.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  have hpi : IntervalIntegrable (per g θ N₀) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hon.mono_set Set.Ioc_subset_Icc_self)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  -- Dini's quotient is bounded
  have hh : IntegrableOn (fun y => (per g θ N₀ y - per g θ N₀ 0) / sin (π * y)) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    apply Measure.integrableOn_of_bounded (M := |L| / 2 + B / δ) (by simp)
      ((hpm.sub measurable_const).div (by fun_prop : Measurable fun y : ℝ => sin (π * y))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hy2 : |y| ≤ 1 / 2 := abs_le.mpr ⟨hy.1, hy.2⟩
    have hs := two_abs_le_abs_sin hy2
    simp only [Pi.div_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_div]
    have hp0 : 0 ≤ |L| / 2 := by positivity
    have hq0 : 0 ≤ B / δ := by positivity
    by_cases hy0 : y = 0
    · subst hy0; simp; linarith
    have hya : 0 < |y| := abs_pos.mpr hy0
    have hsp : 0 < |sin (π * y)| := by linarith
    rw [div_le_iff₀ hsp]
    by_cases hyd : |y| ≤ δ
    · have := hlip y hyd
      have hL : L * |y| ≤ |L| * |y| := mul_le_mul_of_nonneg_right (le_abs_self L) hya.le
      nlinarith
    · push Not at hyd
      have h1 : |per g θ N₀ y - per g θ N₀ 0| ≤ 2 * B := by
        have := abs_sub (per g θ N₀ y) (per g θ N₀ 0); linarith [hB y, hB 0]
      have h2 : 2 * δ ≤ |sin (π * y)| := by linarith
      have h3 : 2 * B ≤ B / δ * |sin (π * y)| := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; nlinarith
      nlinarith
  have hd := Cvs.Upstream.DirichletKernelDiniTest.dini hpi hh
  refine hd.congr fun M => ?_
  -- the Dirichlet means are the Poisson partial sums
  unfold Cvs.Upstream.DirichletKernelDiniTest.D
  have hcos : ∀ m : ℕ, IntervalIntegrable (fun y => per g θ N₀ y * cos (2 * π * m * y)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    fun m => hpi.mul_continuousOn (by fun_prop)
  have e : (fun y => per g θ N₀ y * (1 + 2 * ∑ m ∈ Finset.Icc 1 M, cos (2 * π * m * y)))
      = fun y => per g θ N₀ y * cos (2 * π * ((0 : ℕ) : ℝ) * y)
        + 2 * ∑ m ∈ Finset.Icc 1 M, per g θ N₀ y * cos (2 * π * m * y) := by
    funext y; rw [← Finset.mul_sum]; simp; ring
  rw [e, intervalIntegral.integral_add (hcos 0) (by
      have := IntervalIntegrable.sum (Finset.Icc 1 M) (fun m _ => hcos m)
      have h2 := this.const_mul 2
      convert h2 using 1; funext y; simp [Finset.sum_apply]),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun m _ => hcos m),
    coeff hg hsupp hθ hN 0]
  rw [Finset.sum_congr rfl (fun m _ => coeff hg hsupp hθ hN m)]
  simp only [Nat.cast_zero, zero_mul]
  rw [← Finset.mul_sum]; ring

end Cvs.Upstream.PoissonSummationDini
