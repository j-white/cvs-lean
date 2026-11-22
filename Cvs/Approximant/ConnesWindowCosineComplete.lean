import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowFourierHalfCosine
import Cvs.Finite.WindowedModeSumDomain
import Cvs.L2a.PlaneCorrelationL2
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Cosine completeness for the actual reflection-even Connes window

The interval Fourier bridge and cosine Parseval need square integrability, not
continuity. The actual Connes window can have internal jumps. Its reflection-even
part has the same cosine coefficients, and the corresponding partial sums converge
in L². This does not assert convergence in the Weil form norm.
-/

noncomputable section

set_option maxHeartbeats 3200000

open MeasureTheory Real Filter Complex

namespace Cvs.Approximant.ConnesWindowCosineComplete
open Cvs.ZeroCounting

variable {L : ℝ}

/-- **The Fourier coefficient of a symmetric window function is real.** -/
theorem fourierCoeffOn_eq (hL : 0 < L) {g : ℝ → ℝ} (hgi : IntervalIntegrable g volume 0 L)
    (hg : ∀ x : ℝ, g (L - x) = g x) (k : ℤ) :
    fourierCoeffOn hL (fun x => (g x : ℂ)) k
      = (((1 / L) * ∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hint : ∀ x : ℝ,
      (fourier (-k) ((x : ℝ) : AddCircle (L - 0))) • ((g x : ℂ))
      = ((g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ)
        - ((g x * Real.sin (2 * π * k / L * x) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [smul_eq_mul, fourier_coe_apply]
    have hLne : (L : ℂ) ≠ 0 := by simpa using hL.ne'
    have harg : (2 * π * Complex.I * ((-k : ℤ) : ℂ) * (x : ℂ) / ((L - 0 : ℝ) : ℂ))
        = ((-(2 * π * (k : ℝ) / L * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp
      ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hi1 : IntervalIntegrable
      (fun x : ℝ => ((g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ)) volume 0 L := by
    have hc := hgi.mul_continuousOn
      (by fun_prop : Continuous fun x : ℝ => Real.cos (2 * π * k / L * x)).continuousOn
    exact ⟨Complex.ofRealCLM.integrable_comp hc.1, Complex.ofRealCLM.integrable_comp hc.2⟩
  have hi2 : IntervalIntegrable
      (fun x : ℝ => ((g x * Real.sin (2 * π * k / L * x) : ℝ) : ℂ) * Complex.I)
      volume 0 L := by
    have hs := hgi.mul_continuousOn
      (by fun_prop : Continuous fun x : ℝ => Real.sin (2 * π * k / L * x)).continuousOn
    have hi : IntervalIntegrable (fun x => ((g x * Real.sin (2 * π * k / L * x) : ℝ) : ℂ))
        volume 0 L :=
      ⟨Complex.ofRealCLM.integrable_comp hs.1, Complex.ofRealCLM.integrable_comp hs.2⟩
    exact hi.mul_const _
  have hkey : (∫ x in (0:ℝ)..L,
        (fourier (-k) ((x : ℝ) : AddCircle (L - 0))) • ((g x : ℂ)))
      = ((∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (fun x _ => hint x),
      intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      Cvs.Finite.WindowFourierHalfCosine.integral_sin_of_symm_int hL.ne' hg k]
    push_cast
    ring
  rw [hkey, Complex.real_smul, sub_zero]
  push_cast
  ring

/-- **Parseval, in the project's own cosine coefficients.** -/
theorem hasSum_coef_sq (hL : 0 < L) {g : ℝ → ℝ} (hgm : MemLp g 2 (volume.restrict (Set.Ioc 0 L)))
    (hg : ∀ x : ℝ, g (L - x) = g x) :
    HasSum (fun n : ℕ => (if n = 0 then 2 else 1) * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2)
      ((2 / L) * ∫ x in (0:ℝ)..L, g x ^ 2) := by
  classical
  set G : ℝ → ℂ := fun x => (g x : ℂ) with hG
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  set f : ℤ → ℝ := fun k => ‖fourierCoeffOn hL G k‖ ^ 2 with hf
  -- Mathlib's Parseval on the interval
  have hgi := (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL.le hgm).1
  have hL2 : MemLp G 2 ((volume : Measure ℝ).restrict (Set.Ioc 0 L)) := by
    refine hgm.congr_norm ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hgm.aestronglyMeasurable
    · filter_upwards [] with x
      simp [G]
  have hpar := hasSum_sq_fourierCoeffOn hL hL2
  rw [← hf] at hpar
  -- the coefficient, in real terms
  have hval : ∀ k : ℤ, f k = ((1 / L) * ∫ x in (0:ℝ)..L,
      g x * Real.cos (2 * π * k / L * x)) ^ 2 := by
    intro k
    rw [hf]
    simp only
    rw [hG, fourierCoeffOn_eq hL hgi hg k, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hcosabs : ∀ k : ℤ, ∀ x : ℝ,
      Real.cos (2 * π * (k : ℝ) / L * x)
        = Real.cos (2 * π * ((k.natAbs : ℕ) : ℝ) / L * x) := by
    intro k x
    have habs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs]
    rcases abs_cases ((k : ℝ)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * π * -((k : ℝ)) / L * x = -(2 * π * (k : ℝ) / L * x) by ring,
        Real.cos_neg]
  have hfabs : ∀ k : ℤ, f k
      = ((if k.natAbs = 0 then 2 else 1) * a k.natAbs / 2) ^ 2 := by
    intro k
    rw [hval k, intervalIntegral.integral_congr (fun x _ => by rw [hcosabs k x]),
      ha, Cvs.Finite.WindowCosineBessel.integral_mul_cos hL g k.natAbs]
    field_simp
  have hfe : ∀ k : ℤ, f (-k) = f k := by
    intro k
    rw [hfabs, hfabs, Int.natAbs_neg]
  -- fold the sum onto the naturals
  have hfold := hpar.nat_add_neg
  have hstep : ∀ n : ℕ, f n + f (-(n : ℤ)) = 2 * f n := fun n => by rw [hfe]; ring
  simp only [hstep] at hfold
  have hquad := hfold.mul_left 2
  have hpt := hasSum_ite_eq (0 : ℕ) (2 * f 0)
  have heq : (fun n : ℕ => (if n = 0 then 2 else 1) * a n ^ 2)
      = fun n : ℕ => 2 * (2 * f n) - (if n = 0 then 2 * f 0 else 0) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero]
      rw [hfabs 0]
      norm_num
      ring
    · rw [if_neg hn, if_neg hn, hfabs (n : ℤ), Int.natAbs_natCast, if_neg hn]
      ring
  have hnormG : ∀ x : ℝ, ‖G x‖ ^ 2 = g x ^ 2 := by
    intro x
    rw [hG]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hval2 : (2 / L) * (∫ x in (0:ℝ)..L, g x ^ 2)
      = 2 * (((L - 0)⁻¹ • ∫ x in (0:ℝ)..L, ‖G x‖ ^ 2) + f 0) - 2 * f 0 := by
    rw [intervalIntegral.integral_congr (fun x _ => hnormG x), smul_eq_mul, sub_zero]
    have hL0 : L ≠ 0 := hL.ne'
    field_simp
    ring
  rw [heq, hval2]
  exact hquad.sub hpt

/-- **The cosine partial sums converge in `L²` on the window.** -/
theorem tendsto_integral_sub_modeSum (hL : 0 < L) {g : ℝ → ℝ} (hgm : MemLp g 2 (volume.restrict (Set.Ioc 0 L)))
    (hg : ∀ x : ℝ, g (L - x) = g x) :
    Filter.Tendsto (fun N : ℕ => ∫ x in (0:ℝ)..L,
        (g x - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g) x) ^ 2)
      Filter.atTop (nhds 0) := by
  have hsum := (hasSum_coef_sq hL hgm hg).tendsto_sum_nat
  have hscale := hsum.const_mul (L / 2)
  have hlim : L / 2 * ((2 / L) * ∫ x in (0:ℝ)..L, g x ^ 2)
      = ∫ x in (0:ℝ)..L, g x ^ 2 := by
    have hL0 : L ≠ 0 := hL.ne'
    field_simp
  rw [hlim] at hscale
  have hdiff := (tendsto_const_nhds
    (x := ∫ x in (0:ℝ)..L, g x ^ 2) (f := Filter.atTop (α := ℕ))).sub hscale
  rw [sub_self] at hdiff
  refine hdiff.congr (fun N => ?_)
  rw [Cvs.Approximant.ConnesVectorRealScale.integral_sub_modeSum_sq hL hgm (Finset.range N)]

/-! ### Reflection and the actual Connes window -/

/-- Averaging a function with its reflection about the midpoint of the window. -/
def evenize (L : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := fun s => (g s + g (L - s)) / 2

/-- The averaged representative is exactly reflection-even, including its endpoints. -/
theorem evenize_symm (L : ℝ) (g : ℝ → ℝ) (s : ℝ) :
    evenize L g (L - s) = evenize L g s := by
  simp only [evenize, sub_sub_cancel]
  ring

/-- Reflection averaging preserves square integrability on the real line. -/
theorem memLp_evenize (L : ℝ) {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    MemLp (evenize L g) 2 volume := by
  have hr := hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume L)
  convert (hg.add hr).const_mul (2 : ℝ)⁻¹ using 1
  funext s
  simp [evenize, Function.comp_def, div_eq_mul_inv, mul_comm]

/-- Reflection does not change any cosine coefficient; no smoothness is required. -/
theorem coef_refl (hL : L ≠ 0) (g : ℝ → ℝ) :
    Cvs.Finite.WindowCosineBessel.coef L (fun s => g (L - s)) = Cvs.Finite.WindowCosineBessel.coef L g := by
  have hc (n : ℕ) (s : ℝ) :
      Real.cos (2 * π * n / L * (L - s)) = Real.cos (2 * π * n / L * s) := by
    have he : 2 * π * (n : ℝ) / L * (L - s)
        = (n : ℤ) * (2 * π) - 2 * π * n / L * s := by
      push_cast
      field_simp
    rw [he, Real.cos_int_mul_two_pi_sub]
  funext n
  unfold Cvs.Finite.WindowCosineBessel.coef
  split_ifs
  · congr 1
    simpa only [sub_zero, sub_self] using
      intervalIntegral.integral_comp_sub_left g L (a := 0) (b := L)
  · congr 1
    have hi := intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => g s * Real.cos (2 * π * n / L * s)) L (a := 0) (b := L)
    simpa only [sub_zero, sub_self, hc] using hi

/-- Reflection averaging preserves the actual coefficients of a square-integrable window. -/
theorem coef_evenize (hL : 0 < L) {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    Cvs.Finite.WindowCosineBessel.coef L (evenize L g) = Cvs.Finite.WindowCosineBessel.coef L g := by
  have hr : MemLp (fun s => g (L - s)) 2 volume :=
    hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume L)
  have hi := (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL.le (hg.restrict (Set.Ioc 0 L))).1
  have hir := (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL.le (hr.restrict (Set.Ioc 0 L))).1
  have he : evenize L g = fun s => (1 / 2 : ℝ) * (g s + g (L - s)) := by
    funext s
    simp [evenize, div_eq_mul_inv, mul_comm]
  rw [he, Cvs.Approximant.ConnesVectorRealScale.coef_smul, Cvs.Approximant.ConnesVectorRealScale.coef_add hi hir, coef_refl hL.ne']
  funext n
  ring

/-- The true reflection-even Connes representative, without a continuity assumption. -/
def connesEven (x : ℝ) : ℝ → ℝ := evenize (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x)

/-- The cosine truncations of the actual Connes coefficients exhaust its even L² part.
This theorem makes no claim about convergence of the unbounded Weil form. -/
theorem tendsto_connesEven_error {x : ℝ} (hx : 1 < x) :
    Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..Real.log x,
      (connesEven x s - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum (Real.log x) (Finset.range N)
        (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x)) s) ^ 2) atTop (nhds 0) := by
  have hm := Cvs.Approximant.ConnesVectorRealScale.connesK_memLp (lt_trans zero_lt_one hx)
  have he := memLp_evenize (Real.log x) hm
  have hc := coef_evenize (Real.log_pos hx) hm
  have ht := tendsto_integral_sub_modeSum (Real.log_pos hx)
    (he.restrict (Set.Ioc 0 (Real.log x))) (evenize_symm (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x))
  simpa only [connesEven, hc] using ht

/-- The reflection-even Connes form-domain class has the explicit averaged representative. -/
theorem coe_even_connesClass_ae {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (((Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
      : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
      : Lp ℝ 2 volume) =ᵐ[volume] connesEven x := by
  let k : Lp ℝ 2 volume := (Cvs.Approximant.CosineColumnTailPairing.connesClass hx).val.val
  have hk : (k : ℝ → ℝ) =ᵐ[volume] Cvs.Approximant.ConnesVectorRealScale.connesK x := Cvs.Approximant.CosineColumnTailPairing.coe_connesClass_ae hx
  have hr := (Measure.measurePreserving_sub_left volume (Real.log x)).quasiMeasurePreserving.ae_eq_comp hk
  change ((1 / 2 : ℝ) • (k + Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k) : Lp ℝ 2 volume)
    =ᵐ[volume] connesEven x
  filter_upwards [Lp.coeFn_smul (E := ℝ) (p := 2) (μ := volume)
      (1 / 2 : ℝ) (k + Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k),
    Lp.coeFn_add k (Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k), Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) k, hk, hr]
    with s h1 h2 h3 h4 h5
  simp only [Function.comp_def] at h5
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.add_apply, h3, h4, h5]
  simp [connesEven, evenize, div_eq_mul_inv, mul_comm]

private theorem formDomain_norm_sq_eq {L : ℝ} {hL : 0 ≤ L}
    (d : Cvs.WeilForm.FormDomain.formDomain hL) :
    ‖d‖ ^ 2 = ‖(d.val.val : Lp ℝ 2 volume)‖ ^ 2 := rfl

/-- The actual even truncation error has exactly the scalar window error energy. -/
theorem norm_even_connes_error_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
      - Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)‖ ^ 2
      = ∫ s in (0 : ℝ)..Real.log x,
        (connesEven x s - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum (Real.log x) (Finset.range (N + 1))
          (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x)) s) ^ 2 := by
  let e : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
    Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
  let m : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
    Cvs.Approximant.CosineColumnTailPairing.modeClass (x := x) (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale (x := x) hx) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef (x : ℝ) N)
  let d : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x) :=
    ((e - m : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  rw [formDomain_norm_sq_eq]
  rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
  change (∫ s : ℝ, (d : Lp ℝ 2 volume) s ^ 2) = _
  have hs : (fun s => (d : Lp ℝ 2 volume) s ^ 2)
      =ᵐ[volume] (Set.Ioc (0 : ℝ) (Real.log x)).indicator
        (fun s => (connesEven x s - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum (Real.log x)
          (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x)) s) ^ 2) := by
    have hd : (d : Lp ℝ 2 volume) = (e.val.val - m.val.val) := rfl
    rw [hd]
    filter_upwards [Lp.coeFn_sub e.val.val m.val.val, coe_even_connesClass_ae hx,
      Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae (x := x) (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N), d.property]
      with s h1 h2 h3 h4
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) (Real.log x)
    · rw [Set.indicator_of_mem hs, h1, Pi.sub_apply, h2]
      change (_ - ((Cvs.Approximant.CosineColumnTailPairing.modeClass (x := x) (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N
        (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)).val.val : ℝ → ℝ) s) ^ 2 = _
      rw [h3, Cvs.Approximant.ConnesVectorRealScale.connesCoef, ← Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum _ N _ _ subset_rfl,
        Cvs.Finite.WindowedModeSumDomain.windowMode, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      change (d : Lp ℝ 2 volume) s ^ 2 = 0
      rw [h4 hs]
      norm_num
  rw [integral_congr_ae hs, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (Real.log_natCast_nonneg x)]

/-- At each actual scale the even Connes class is the L² limit of its actual mode classes. -/
theorem tendsto_norm_even_connes_error_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N : ℕ =>
      ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
        - Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)‖ ^ 2)
      atTop (nhds 0) := by
  have ht := (tendsto_connesEven_error (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)).comp
    (tendsto_add_atTop_nat 1)
  exact ht.congr (fun N => (norm_even_connes_error_sq hx N).symm)

end Cvs.Approximant.ConnesWindowCosineComplete
