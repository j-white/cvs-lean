import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.EulerMaclaurinKernel
import Cvs.Zeta.Convexity.EulerMaclaurinTruncated
import Cvs.Zeta.ConvexityZetaEdges

/-!
# `ζ(1+it) = O(log|t|)`

‖ζ(1+it)‖ ≤ 7 + log|t| for `|t| ≥ 1` ,
-/

open Complex MeasureTheory Set Filter Topology

namespace Cvs.ZetaGrowth

/-- `EulerMaclaurinKernel`'s tail bound, from an arbitrary base `a ≥ 1`: `‖∫_a^∞ {x}x^{-s-1}‖ ≤ a^{-σ}/σ`. -/
theorem norm_integral_emKernel_from {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 1 ≤ a) :
    ‖∫ x in Ioi a, Cvs.ZetaGrowth.emKernel s x‖ ≤ a ^ (-s.re) / s.re := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hdom : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha0
  have hint : IntegrableOn (Cvs.ZetaGrowth.emKernel s) (Ioi a) :=
    (Cvs.ZetaGrowth.integrableOn_emKernel hs).mono_set (fun x hx => lt_of_le_of_lt ha hx)
  have hval : (∫ x in Ioi a, x ^ (-s.re - 1)) = a ^ (-s.re) / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith) ha0, show (-s.re - 1 + 1) = -s.re by ring]
    field_simp
  calc ‖∫ x in Ioi a, Cvs.ZetaGrowth.emKernel s x‖ ≤ ∫ x in Ioi a, ‖Cvs.ZetaGrowth.emKernel s x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi a, x ^ (-s.re - 1) := by
        refine setIntegral_mono_on hint.norm hdom measurableSet_Ioi (fun x hx => ?_)
        exact Cvs.ZetaGrowth.norm_emKernel_le (lt_of_lt_of_le ha0 (le_of_lt hx))
    _ = a ^ (-s.re) / s.re := hval

/-- On `σ = 1` the Dirichlet partial sum is the harmonic number. -/
theorem sum_norm_le {s : ℂ} (hsre : s.re = 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ ≤ 1 + Real.log N := by
  have hcongr : ∀ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ = ((n : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re, hsre, Real.rpow_neg_one]
  rw [Finset.sum_congr rfl hcongr]
  have hharm : ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  rw [hharm]
  exact harmonic_le_one_add_log N

/-- **`ζ(1+it) = O(log|t|)`** , with explicit constants. -/
theorem norm_zeta₀_one_add_I {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta₀ (1 + (t : ℂ) * I)‖ ≤ 6 + Real.log |t| := by
  set s : ℂ := 1 + (t : ℂ) * I with hs_def
  have hsre : s.re = 1 := by rw [hs_def]; simp
  have hsim : s.im = t := by rw [hs_def]; simp
  have hs0 : 0 < s.re := by rw [hsre]; norm_num
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hs1 : s - 1 = (t : ℂ) * I := by rw [hs_def]; ring
  have hsub : s ≠ 1 := by
    intro hc
    have : s - 1 = 0 := by rw [hc]; ring
    rw [hs1] at this
    rcases mul_eq_zero.mp this with h | h
    · have : t = 0 := by exact_mod_cast h
      rw [this] at ht0; simp at ht0
    · exact I_ne_zero h
  set N : ℕ := ⌈|t|⌉₊ with hN_def
  have hNge : |t| ≤ (N : ℝ) := Nat.le_ceil _
  have hNlt : (N : ℝ) < |t| + 1 := Nat.ceil_lt_add_one (le_of_lt ht0)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans ht hNge
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Cvs.ZetaGrowth.euler_maclaurin_trunc hs0 hsub hN1]
  -- the three pieces
  have hA : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + Real.log N :=
    le_trans (norm_sum_le _ _) (sum_norm_le hsre N)
  have hlogN : Real.log (N : ℝ) ≤ Real.log 2 + Real.log |t| := by
    have h2 : (N : ℝ) ≤ 2 * |t| := by linarith
    calc Real.log (N : ℝ) ≤ Real.log (2 * |t|) := Real.log_le_log hNpos h2
      _ = Real.log 2 + Real.log |t| := Real.log_mul (by norm_num) (ne_of_gt ht0)
  have hB : ‖((N : ℂ) ^ (1 - s) - 1) / (s - 1)‖ ≤ 2 / |t| := by
    have hnum : ‖(N : ℂ) ^ (1 - s) - 1‖ ≤ 2 := by
      have h1 : ‖(N : ℂ) ^ (1 - s)‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hN1]
        have : (1 - s).re = 0 := by rw [Complex.sub_re, hsre]; simp
        rw [this, Real.rpow_zero]
      calc ‖(N : ℂ) ^ (1 - s) - 1‖ ≤ ‖(N : ℂ) ^ (1 - s)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [h1, norm_one]; norm_num
    have hden : ‖s - 1‖ = |t| := by
      rw [hs1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_div, hden]
    exact div_le_div_of_nonneg_right hnum ht0.le
  have hC : ‖s * ∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x‖ ≤ (1 + |t|) / |t| := by
    have htail := norm_integral_emKernel_from hs0 (a := (N : ℝ)) (by exact_mod_cast hN1)
    rw [hsre] at htail
    have hrw : (N : ℝ) ^ (-1 : ℝ) / 1 = ((N : ℝ))⁻¹ := by
      rw [Real.rpow_neg_one, div_one]
    rw [hrw] at htail
    have hsn : ‖s‖ ≤ 1 + |t| := by
      rw [hs_def]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hinvN : ((N : ℝ))⁻¹ ≤ (|t|)⁻¹ := by
      exact inv_anti₀ ht0 hNge
    rw [norm_mul]
    calc ‖s‖ * ‖∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x‖
        ≤ (1 + |t|) * ((N : ℝ))⁻¹ := by
          refine mul_le_mul hsn htail (norm_nonneg _) (by linarith [abs_nonneg t])
      _ ≤ (1 + |t|) * (|t|)⁻¹ := by
          refine mul_le_mul_of_nonneg_left hinvN (by linarith [abs_nonneg t])
      _ = (1 + |t|) / |t| := by rw [div_eq_mul_inv]
  -- assemble
  have hb2 : (2 : ℝ) / |t| ≤ 2 := by
    rw [div_le_iff₀ ht0]; nlinarith
  have hc2 : (1 + |t|) / |t| ≤ 2 := by
    rw [div_le_iff₀ ht0]; nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  calc ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + ((N : ℂ) ^ (1 - s) - 1) / (s - 1)
        - s * ∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + ((N : ℂ) ^ (1 - s) - 1) / (s - 1)‖
        + ‖s * ∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x‖ := norm_sub_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ + ‖((N : ℂ) ^ (1 - s) - 1) / (s - 1)‖)
        + ‖s * ∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 + Real.log |t| := by linarith

/-- **`‖ζ(1+it)‖ ≤ 7 + log|t|` for `|t| ≥ 1`**, unconditionally.  The pole term costs `1` more
than `ConvexityZetaEdges`. -/
theorem norm_zeta_one_add_I {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ 7 + Real.log |t| := by
  have him : (1 + (t : ℂ) * I).im = t := by simp
  have h := Cvs.ArchScore.norm_zeta_le_of_zeta₀ (s := 1 + (t : ℂ) * I) (by rw [him]; exact ht)
    (norm_zeta₀_one_add_I ht)
  linarith

end Cvs.ZetaGrowth
