import Mathlib
import Cvs.WeilForm.MellinProfileStrips
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin transform of the window image, in closed form

For `a > 0`, `G` integrable on `[a, 1]` and every `s ∈ ℂ`, `k_G = 1_{[a,1]}E_G` is Mellin-convergent and
`M[k_G](s) = a^s Σ_{1 ≤ n ≤ ⌊1/a⌋} n^{s−1} ∫_{na}^1 u^{−s}G(u) du` (`u = na/θ`). When `u^{−s}G` is integrable on
`(0, 1]` (e.g. `G` continuous on `[0, 1]` and `Re s < 1`) this is `a^s Σ n^{s−1}(Ĝ(1 − s) − ∫_0^{na} u^{−s}G)`.
-/

noncomputable section

open Real Set Filter MeasureTheory
open Cvs.Xi.EImageWindowPoisson (eimage window eimage_eq_sum_indicator)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.WeilForm.MellinProfileStrips (gM mellinR_indicator)

namespace Cvs.Xi.WindowImageMellinClosed

/-! ### One summand: the substitution `u = na/θ` -/

/-- The substitution `θ ↦ na/θ` maps `[a, 1]` onto `[na, n]`. -/
theorem image_recip {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    (fun θ => n * a / θ) '' Icc a 1 = Icc (n * a) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  ext u
  constructor
  · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
    have hθ : 0 < θ := ha.trans_le h1
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hθ]; nlinarith [mul_le_mul_of_nonneg_left h2 (mul_pos hn0 ha).le]
    · rw [div_le_iff₀ hθ]; nlinarith
  · rintro ⟨h1, h2⟩
    have hu : 0 < u := (by positivity : (0 : ℝ) < n * a).trans_le h1
    refine ⟨n * a / u, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hu]; nlinarith
    · rw [div_le_iff₀ hu]; linarith
    · field_simp

/-- The pointwise Jacobian identity: for `θ, a > 0`, `n ≥ 1` and `r = na/θ`,
`θ^{s−1}(a/θ) = a^s n^{s−1} · |−na/θ²| · r^{−s}`. -/
theorem cpow_jac {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    (θ : ℂ) ^ (s - 1) * ((a / θ : ℝ) : ℂ)
      = (a : ℂ) ^ s * (n : ℂ) ^ (s - 1) * ((|-(n * a) / θ ^ 2| : ℝ) : ℂ) * ((n * a / θ : ℝ) : ℂ) ^ (-s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : |-(n * a) / θ ^ 2| = n * a / θ ^ 2 := by
    rw [neg_div, abs_neg, abs_of_pos (by positivity)]
  have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hr : ((n * a / θ : ℝ) : ℂ) ^ (-s) = (n : ℂ) ^ (-s) * (a : ℂ) ^ (-s) * (θ : ℂ) ^ s := by
    rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity)
      (by positivity), Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn0.le ha.le,
      Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hθ.le]; exact
        (Real.pi_pos.ne)), Complex.cpow_neg (θ : ℂ) s, inv_inv]
    push_cast; ring
  have hA : (a : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hac)
  have hN : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hnc)
  rw [hr, habs, Complex.cpow_sub _ _ hθc, Complex.cpow_one, Complex.cpow_sub _ _ hnc, Complex.cpow_one,
    Complex.cpow_neg, Complex.cpow_neg]
  push_cast
  field_simp

/-- The `u`-side integrand `u^{−s}(1_{[0,1]}G)(u)`. -/
def uInt (G : ℝ → ℝ) (s : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (-s) * (((Icc (0 : ℝ) 1).indicator G u : ℝ) : ℂ)

theorem uInt_eq_indicator (G : ℝ → ℝ) (s : ℂ) :
    uInt G s = (Icc (0 : ℝ) 1).indicator (fun u : ℝ => (u : ℂ) ^ (-s) * (G u : ℂ)) := by
  funext u; by_cases h : u ∈ Icc (0 : ℝ) 1 <;> simp [uInt, h]

/-- Integrability of the `u`-side integrand on `[na, n]` from integrability of `G` on `[a, 1]`. -/
theorem integrableOn_uInt {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) {G : ℝ → ℝ}
    (hG : IntegrableOn G (Icc a 1)) (s : ℂ) : IntegrableOn (uInt G s) (Icc (n * a) n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [uInt_eq_indicator, IntegrableOn, integrable_indicator_iff measurableSet_Icc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Icc, Icc_inter_Icc, max_eq_right (by positivity),
    min_eq_left hn1]
  have hsub : Icc ((n : ℝ) * a) 1 ⊆ Icc a 1 := Icc_subset_Icc (by nlinarith) le_rfl
  have hGc : IntegrableOn (fun u => (G u : ℂ)) (Icc ((n : ℝ) * a) 1) := (hG.mono_set hsub).ofReal
  have hpow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s)) (Icc ((n : ℝ) * a) 1) := by
    intro u hu
    have hu0 : 0 < u := (by positivity : (0 : ℝ) < n * a).trans_le hu.1
    exact (Complex.continuousAt_ofReal_cpow_const u (-s) (Or.inr hu0.ne')).continuousWithinAt
  exact hGc.continuousOn_mul hpow isCompact_Icc

theorem integrableOn_term {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) {G : ℝ → ℝ}
    (hG : IntegrableOn G (Icc a 1)) (s : ℂ) :
    IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (((a / θ) * (Icc (0 : ℝ) 1).indicator G (n * a / θ) : ℝ) : ℂ))
      (Icc a 1) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (Cvs.Xi.EImageWindowPoisson.hasDerivWithinAt_recip ha n) (Cvs.Xi.EImageWindowPoisson.injOn_recip ha hn)
    (uInt G s)).1 (image_recip ha hn ▸ integrableOn_uInt ha hn hG s)
  refine IntegrableOn.congr_fun (h.const_mul ((a : ℂ) ^ s * (n : ℂ) ^ (s - 1))) (fun θ hθ => ?_)
    measurableSet_Icc
  simp only [uInt, Complex.real_smul, Complex.ofReal_mul]
  rw [← mul_assoc ((θ : ℂ) ^ (s - 1)), cpow_jac ha (ha.trans_le hθ.1) hn s]
  ring

/-! ### The closed form -/

/-- The window's Mellin integrand, summed: on `[a, 1]`, `θ^{s−1}k_G(θ) = Σ_n θ^{s−1}(a/θ)(1_{[0,1]}G)(na/θ)`. -/
theorem integrand_eq_sum {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1) (G : ℝ → ℝ) (s : ℂ) :
    (θ : ℂ) ^ (s - 1) * (eimage a G θ : ℂ) = ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊,
      (θ : ℂ) ^ (s - 1) * (((a / θ) * (Icc (0 : ℝ) 1).indicator G (n * a / θ) : ℝ) : ℂ) := by
  rw [eimage_eq_sum_indicator ha (ha.trans_le hθ.1) hθ.2, Finset.mul_sum, Complex.ofReal_sum,
    Finset.mul_sum]

/-- **The window is Mellin-convergent at every `s`** when `G` is integrable on `[a, 1]`. -/
theorem mellinConvergent_window {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hG : IntegrableOn G (Icc a 1)) (s : ℂ) :
    MellinConvergent (fun θ => (window a G θ : ℂ)) s := by
  have hsum : IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (eimage a G θ : ℂ)) (Icc a 1) := by
    refine IntegrableOn.congr_fun (integrable_finsetSum (Finset.Icc 1 ⌊1 / a⌋₊) fun n hn =>
      integrableOn_term ha (Finset.mem_Icc.1 hn).1 hG s) (fun θ hθ => ?_) measurableSet_Icc
    rw [integrand_eq_sum ha hθ]
  have e : (fun θ : ℝ => (θ : ℂ) ^ (s - 1) • (window a G θ : ℂ))
      = (Icc a 1).indicator (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (eimage a G θ : ℂ)) := by
    funext θ; exact Cvs.WeilForm.MellinProfileStrips.cpow_smul_indicator _ _ s θ
  unfold MellinConvergent
  rw [e]
  exact ((integrable_indicator_iff measurableSet_Icc).2 hsum).integrableOn

/-! ### The split against `Ĝ(1 − s)` -/

end Cvs.Xi.WindowImageMellinClosed
