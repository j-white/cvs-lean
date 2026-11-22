import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.ConnesWindowCosineComplete
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.EvenConnesEnergyFormDomain
import Cvs.Approximant.EvenConnesEnergyOutput
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.ExponentialKernelValue
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Upstream.SqrtAnalyticPositive
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.CubicTailSeparatedKernel
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PoleCancelsPrimeMean
import Cvs.WeilForm.PoleTermDilationMean
import Cvs.WeilForm.ThetaPairingBilinear
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Mixed prime discrepancy as a translation defect

The actual finite prime and continuous mean channels share a scalar overlap
term. Orthogonality cancels it in mixed pairings; self pairings retain it.
-/

noncomputable section

open Real Set MeasureTheory Filter Matrix

namespace Cvs.WeilForm.PrimeDiscrepancyTranslation
open Cvs.ZeroCounting

open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.ThetaSpaceParseval (dil)
open Cvs.WeilForm.PoleTermDilationMean (dilR)

/-- The mixed logarithmic overlap of two physical profiles. -/
def logPair (F G : ℝ → ℝ) : ℝ := ∫ s, logScale F s * logScale G s

/-- The actual product of two translation differences. -/
def translationDefect (f g : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ s, (f s-f (s+v))*(g s-g (s+v))

/-- The finite Mangoldt-weighted mixed translation defect. -/
def primeDefect (x : ℕ) (F G : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (x+1), (ArithmeticFunction.vonMangoldt n : ℝ)/√(n : ℝ) *
    translationDefect (logScale F) (logScale G) (log (n : ℝ))

/-- The continuous mixed translation defect on the actual log window. -/
def continuousDefect (L : ℝ) (F G : ℝ → ℝ) : ℝ :=
  ∫ v in Ioc (0 : ℝ) L, exp (v/2)*translationDefect (logScale F) (logScale G) v

/-- The exact continuous scalar dilation weight. -/
def continuousWeight (L : ℝ) : ℝ := 2*(exp (L/2)-1)

/-- The two actual angular prime orientations at the complete finite cutoff. -/
def finitePrime (x : ℕ) (F G : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (x+1), (ArithmeticFunction.vonMangoldt n : ℝ)*(dil F G n+dil G F n)

/-- The two actual continuous angular dilation orientations. -/
def continuousMean (F G : ℝ → ℝ) : ℝ :=
  ∫ r in Ioi (1 : ℝ), dilR F G r+dilR G F r

/-- The signed actual finite prime-minus-continuous-mean pairing. -/
def discrepancy (x : ℕ) (F G : ℝ → ℝ) : ℝ := finitePrime x F G-continuousMean F G

/-- Products of the two actual translation differences are genuinely integrable. -/
theorem integrable_translationDefect {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (v : ℝ) :
    Integrable (fun s => (f s-f (s+v))*(g s-g (s+v))) :=
  (hf.sub (Cvs.WeilForm.CentredWindowTranslate.memLp_translate v hf)).integrable_mul
    (hg.sub (Cvs.WeilForm.CentredWindowTranslate.memLp_translate v hg))

/-- The exact mixed translation defect is twice the overlap minus both shifted overlaps. -/
theorem translationDefect_eq {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (v : ℝ) :
    translationDefect f g v = 2*(∫ s, f s*g s)-Cvs.WeilForm.TruncatedFormPolarised.polar f g v := by
  have hf' := Cvs.WeilForm.CentredWindowTranslate.memLp_translate v hf
  have hg' := Cvs.WeilForm.CentredWindowTranslate.memLp_translate v hg
  have h1 := hf.integrable_mul hg
  have h2 := hf.integrable_mul hg'
  have h3 := hf'.integrable_mul hg
  have h4 := hf'.integrable_mul hg'
  have he : (fun s => (f s-f (s+v))*(g s-g (s+v))) =
      fun s => ((f s*g s-f s*g (s+v))-f (s+v)*g s)+f (s+v)*g (s+v) := by
    funext s; ring
  unfold translationDefect Cvs.WeilForm.TruncatedFormPolarised.polar Cvs.WeilForm.TruncatedFormPolarised.crossConv
  have ha := integral_add ((h1.sub h2).sub h3) h4
  have hb := integral_sub (h1.sub h2) h3
  have hc := integral_sub h1 h2
  simp only [Pi.sub_apply, Pi.mul_apply] at ha hb hc
  rw [he, ha, hb, hc, integral_add_right_eq_self (fun s => f s*g s) v]
  have hswap : (∫ s, f (s+v)*g s) = ∫ s, g s*f (s+v) := by
    apply integral_congr_ae
    exact ae_of_all _ fun s => mul_comm _ _
  rw [hswap]
  ring

/-- The finite angular prime channel has the exact mixed budget-minus-defect expression. -/
theorem finitePrime_eq {F G : ℝ → ℝ}
    (hF : MemLp (logScale F) 2 volume) (hG : MemLp (logScale G) 2 volume) (x : ℕ) :
    finitePrime x F G = 2*Cvs.Approximant.EvenConnesEnergyOutput.primeWeight x*logPair F G-primeDefect x F G := by
  unfold finitePrime primeDefect Cvs.Approximant.EvenConnesEnergyOutput.primeWeight
  calc
    _ = ∑ n ∈ Finset.range (x+1),
        (2*((ArithmeticFunction.vonMangoldt n : ℝ)/√(n : ℝ))*logPair F G -
          (ArithmeticFunction.vonMangoldt n : ℝ)/√(n : ℝ) *
            translationDefect (logScale F) (logScale G) (log (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n=0
      · subst n; simp
      have hn0 : (0 : ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hs : √(n : ℝ)≠0 := (sqrt_pos.mpr hn0).ne'
      have hc := Cvs.WeilForm.ThetaPairingBilinear.crossConv_logScale_log F G hn0
      have hc' := Cvs.WeilForm.ThetaPairingBilinear.crossConv_logScale_log G F hn0
      have hd := translationDefect_eq hF hG (log (n : ℝ))
      rw [hd]
      unfold logPair Cvs.WeilForm.TruncatedFormPolarised.polar
      rw [hc, hc']
      change _ = 2*((ArithmeticFunction.vonMangoldt n : ℝ)/√(n : ℝ))*(∫ s, logScale F s*logScale G s) -
        (ArithmeticFunction.vonMangoldt n : ℝ)/√(n : ℝ)*
          (2*(∫ s, logScale F s*logScale G s) -
            (√(n : ℝ)*dil F G n+√(n : ℝ)*dil G F n))
      field_simp
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

private theorem logScale_support {L : ℝ} {F : ℝ → ℝ}
    (hs : ∀ θ ∉ Icc (exp (-L)) 1, F θ=0) :
    ∀ s ∉ Icc (-L) 0, logScale F s=0 := by
  intro s hs'
  unfold logScale
  rw [hs _ (fun h => hs' ⟨exp_le_exp.mp h.1, exp_le_one_iff.mp h.2⟩), zero_mul]

/-- Shifted overlaps vanish once the displacement exceeds the actual support window. -/
theorem polar_eq_zero_of_large {L : ℝ} {F G : ℝ → ℝ}
    (hF : ∀ θ ∉ Icc (exp (-L)) 1, F θ=0)
    (hG : ∀ θ ∉ Icc (exp (-L)) 1, G θ=0) {v : ℝ} (hv : L<v) :
    Cvs.WeilForm.TruncatedFormPolarised.polar (logScale F) (logScale G) v=0 := by
  have hz (F G : ℝ → ℝ)
      (hF : ∀ θ ∉ Icc (exp (-L)) 1, F θ=0)
      (hG : ∀ θ ∉ Icc (exp (-L)) 1, G θ=0) :
      Cvs.WeilForm.TruncatedFormPolarised.crossConv (logScale F) (logScale G) v=0 := by
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro s
    change logScale F s*logScale G (s+v)=0
    by_cases hs : s< -L
    · rw [logScale_support hF s (fun h => hs.not_ge h.1), zero_mul]
    · rw [logScale_support hG (s+v) (fun h => by linarith [h.2]), mul_zero]
  rw [Cvs.WeilForm.TruncatedFormPolarised.polar, hz F G hF hG, hz G F hG hF, add_zero]

/-- The actual continuous angular mean is the exponentially weighted logarithmic overlap. -/
theorem continuousMean_eq_log (F G : ℝ → ℝ) :
    continuousMean F G = ∫ v in Ioi (0 : ℝ),
      exp (v/2)*Cvs.WeilForm.TruncatedFormPolarised.polar (logScale F) (logScale G) v := by
  unfold continuousMean
  have hsub := integral_comp_exp_Ioi (fun r => dilR F G r+dilR G F r) 0
  simp only [exp_zero] at hsub
  rw [← hsub]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  have hc := Cvs.WeilForm.ThetaPairingBilinear.crossConv_logScale_log F G (exp_pos v)
  have hc' := Cvs.WeilForm.ThetaPairingBilinear.crossConv_logScale_log G F (exp_pos v)
  have hs : √(exp v)=exp (v/2) := by
    rw [sqrt_eq_iff_mul_self_eq (exp_pos _).le (exp_pos _).le, Cvs.L2a.TailLogScaleTest.exp_half_sq]
  simp only [log_exp, hs] at hc hc'
  dsimp only
  unfold Cvs.WeilForm.TruncatedFormPolarised.polar
  rw [hc, hc']
  simp only [smul_eq_mul]
  unfold dilR
  rw [show exp v=exp (v/2)*exp (v/2) by rw [Cvs.L2a.TailLogScaleTest.exp_half_sq]]
  ring

/-- The continuous scalar weight has its exact finite-window integral. -/
theorem integral_continuousWeight {L : ℝ} (hL : 0≤L) :
    (∫ v in Ioc (0 : ℝ) L, exp (v/2))=continuousWeight L := by
  rw [← intervalIntegral.integral_of_le hL]
  have h := Cvs.Finite.ExponentialKernelValue.integral_exp_mul (c := (1/2 : ℝ)) (by norm_num) 0 L
  simp only [mul_zero, exp_zero] at h
  have he : (fun v : ℝ => exp (v/2))=fun v => exp ((1/2 : ℝ)*v) := by
    funext v; congr 1; ring
  rw [he, h]
  unfold continuousWeight
  rw [show (1/2 : ℝ)*L=L/2 by ring]
  ring

/-- The continuous defect is genuinely integrable over its finite window. -/
theorem integrableOn_continuousDefect {F G : ℝ → ℝ}
    (hF : MemLp (logScale F) 2 volume) (hG : MemLp (logScale G) 2 volume) (L : ℝ) :
    IntegrableOn (fun v => exp (v/2)*translationDefect (logScale F) (logScale G) v)
      (Ioc (0 : ℝ) L) volume := by
  simp_rw [translationDefect_eq hF hG]
  apply Continuous.integrableOn_Ioc
  exact (by fun_prop : Continuous fun v : ℝ => exp (v/2)).mul
    (continuous_const.sub (Cvs.WeilForm.TruncatedFormPolarised.continuous_polar hF hG))

/-- The actual continuous angular mean has the same scalar overlap and its continuous defect. -/
theorem continuousMean_eq_budget_sub {L : ℝ} (hL : 0≤L) {F G : ℝ → ℝ}
    (hFs : ∀ θ ∉ Icc (exp (-L)) 1, F θ=0)
    (hGs : ∀ θ ∉ Icc (exp (-L)) 1, G θ=0)
    (hF : MemLp (logScale F) 2 volume) (hG : MemLp (logScale G) 2 volume) :
    continuousMean F G = 2*continuousWeight L*logPair F G-continuousDefect L F G := by
  rw [continuousMean_eq_log,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Ioc (0 : ℝ) L ⊆ Ioi 0 from fun _ h => h.1) ?_]
  · have hi : IntegrableOn (fun v : ℝ => exp (v/2)) (Ioc (0 : ℝ) L) volume :=
      (by fun_prop : Continuous fun v : ℝ => exp (v/2)).integrableOn_Ioc
    have hp : IntegrableOn (fun v => exp (v/2)*Cvs.WeilForm.TruncatedFormPolarised.polar (logScale F) (logScale G) v)
        (Ioc (0 : ℝ) L) volume :=
      ((by fun_prop : Continuous fun v : ℝ => exp (v/2)).mul
        (Cvs.WeilForm.TruncatedFormPolarised.continuous_polar hF hG)).integrableOn_Ioc
    have hd := integrableOn_continuousDefect hF hG L
    have he : (fun v => exp (v/2)*Cvs.WeilForm.TruncatedFormPolarised.polar (logScale F) (logScale G) v)=
        fun v => (2*logPair F G)*exp (v/2) -
          exp (v/2)*translationDefect (logScale F) (logScale G) v := by
      funext v
      rw [translationDefect_eq hF hG]
      unfold logPair
      ring
    rw [he, integral_sub (hi.const_mul _) hd, integral_const_mul, integral_continuousWeight hL]
    unfold continuousDefect
    ring
  · intro v hv
    have hvL : L<v := by
      have := hv.2
      simp only [mem_Ioc, not_and, not_le] at this
      exact this hv.1
    rw [polar_eq_zero_of_large hFs hGs hvL, mul_zero]

/-- The signed arithmetic discrepancy is its scalar mismatch minus prime defect plus mean defect. -/
theorem discrepancy_eq {L : ℝ} (hL : 0≤L) {F G : ℝ → ℝ}
    (hFs : ∀ θ ∉ Icc (exp (-L)) 1, F θ=0)
    (hGs : ∀ θ ∉ Icc (exp (-L)) 1, G θ=0)
    (hF : MemLp (logScale F) 2 volume) (hG : MemLp (logScale G) 2 volume) (x : ℕ) :
    discrepancy x F G = 2*(Cvs.Approximant.EvenConnesEnergyOutput.primeWeight x-continuousWeight L)*logPair F G -
      primeDefect x F G+continuousDefect L F G := by
  unfold discrepancy
  rw [finitePrime_eq hF hG, continuousMean_eq_budget_sub hL hFs hGs hF hG]
  ring

/-- Mixed orthogonality removes exactly the scalar weight mismatch from the actual discrepancy. -/
theorem discrepancy_eq_of_logPair_zero {L : ℝ} (hL : 0≤L) {F G : ℝ → ℝ}
    (hFs : ∀ θ ∉ Icc (exp (-L)) 1, F θ=0)
    (hGs : ∀ θ ∉ Icc (exp (-L)) 1, G θ=0)
    (hF : MemLp (logScale F) 2 volume) (hG : MemLp (logScale G) 2 volume) (x : ℕ)
    (hperp : logPair F G=0) :
    discrepancy x F G=continuousDefect L F G-primeDefect x F G := by
  rw [discrepancy_eq hL hFs hGs hF hG, hperp]
  ring

/-- The original two-orientation mixed dilation integrand is absolutely integrable. -/
theorem integrable_mixedDilation {a : ℝ} (ha : 0<a) {F G : ℝ → ℝ}
    (hmF : Measurable F) (hmG : Measurable G) (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hFs : ∀ θ ∉ Icc a 1, F θ=0) (hGs : ∀ θ ∉ Icc a 1, G θ=0) :
    Integrable (fun p : ℝ × ℝ => F p.2*G (p.1*p.2)+G p.2*F (p.1*p.2))
      ((volume.restrict (Ioi (1 : ℝ))).prod Cvs.WeilForm.CubicTailSeparatedKernel.positiveVolume) := by
  have hsum := Cvs.WeilForm.PoleCancelsPrimeMean.integrable_meanDilationPair ha (hmF.add hmG) (hF.add hG)
    (fun θ hθ => by simp only [Pi.add_apply, hFs θ hθ, hGs θ hθ, add_zero])
  have h1 := Cvs.WeilForm.PoleCancelsPrimeMean.integrable_meanDilationPair ha hmF hF hFs
  have h2 := Cvs.WeilForm.PoleCancelsPrimeMean.integrable_meanDilationPair ha hmG hG hGs
  refine ((hsum.sub h1).sub h2).congr (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply, Cvs.WeilForm.PoleCancelsPrimeMean.meanDilationPair, Pi.add_apply]
  ring

/-- The continuous mixed self-pairing is the actual continuous mean. -/
theorem continuousMean_self (F : ℝ → ℝ) : continuousMean F F=Cvs.WeilForm.PoleCancelsPrimeMean.continuousMean F := by
  unfold continuousMean Cvs.WeilForm.PoleCancelsPrimeMean.continuousMean
  simp only [← two_mul, integral_const_mul]

/-- The prime mixed self-defect is the actual nonnegative dilation defect. -/
theorem primeDefect_self (x : ℕ) (F : ℝ → ℝ) : primeDefect x F F=Cvs.Approximant.EvenConnesEnergyOutput.dilationDefect x F := by
  unfold primeDefect Cvs.Approximant.EvenConnesEnergyOutput.dilationDefect translationDefect
  simp only [pow_two]

/-- The continuous self-defect is nonnegative. -/
theorem continuousDefect_self_nonneg (L : ℝ) (F : ℝ → ℝ) : 0≤continuousDefect L F F := by
  unfold continuousDefect translationDefect
  apply setIntegral_nonneg measurableSet_Ioc
  intro v _
  apply mul_nonneg (exp_pos _).le
  exact integral_nonneg fun s => mul_self_nonneg _

/-- The continuous scalar weight at the physical cutoff is exactly twice sqrt(x) minus two. -/
theorem continuousWeight_log {x : ℝ} (hx : 0<x) : continuousWeight (log x)=2*(√x-1) := by
  unfold continuousWeight
  rw [← Cvs.Upstream.SqrtAnalyticPositive.sqrt_eq_exp_log hx]

/-- Exact physical support makes the full mixed prime channel finite. -/
theorem prime_tsum_eq_finite {x : ℕ} (hx : (0 : ℝ)<x) {F G : ℝ → ℝ}
    (hFs : ∀ θ ∉ Icc (1/(x : ℝ)) 1, F θ=0)
    (hGs : ∀ θ ∉ Icc (1/(x : ℝ)) 1, G θ=0) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*(dil F G n+dil G F n))=finitePrime x F G := by
  apply tsum_eq_sum (s := Finset.range (x+1))
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  have hd : (1 : ℝ)/(1/(x : ℝ))<n := by
    rw [one_div_one_div]
    exact_mod_cast (show x<n by omega)
  simp only [Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support (one_div_pos.mpr hx) hFs hGs hd,
    Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support (one_div_pos.mpr hx) hGs hFs hd, add_zero, mul_zero]

/-- The self discrepancy retains its exact scalar weight mismatch. -/
theorem primeDiscrepancy_eq {x : ℕ} (hx : (0 : ℝ)<x) {F : ℝ → ℝ}
    (hFs : ∀ θ ∉ Icc (1/(x : ℝ)) 1, F θ=0)
    (hF : MemLp (logScale F) 2 volume) :
    Cvs.WeilForm.PoleCancelsPrimeMean.primeDiscrepancy F=
      2*(Cvs.Approximant.EvenConnesEnergyOutput.primeWeight x-continuousWeight (log x))*logPair F F-
        Cvs.Approximant.EvenConnesEnergyOutput.dilationDefect x F+continuousDefect (log x) F F := by
  have hs : ∀ θ ∉ Icc (exp (-log (x : ℝ))) 1, F θ=0 := by
    simpa only [exp_neg, exp_log hx, one_div] using hFs
  have he : Cvs.WeilForm.PoleCancelsPrimeMean.primeDiscrepancy F=discrepancy x F F := by
    unfold Cvs.WeilForm.PoleCancelsPrimeMean.primeDiscrepancy discrepancy
    rw [prime_tsum_eq_finite hx hFs hFs, ← continuousMean_self]
  rw [he, discrepancy_eq (log_natCast_nonneg x) hs hs hF hF, primeDefect_self]

/-- The complete supported angular Weil expression keeps both signed defects and the scalar shift. -/
theorem weilθ_eq_defects {x : ℕ} (hx : (0 : ℝ)<x) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume)
    (hFs : ∀ θ ∉ Icc (1/(x : ℝ)) 1, F θ=0)
    (hf : MemLp (logScale F) 2 volume) :
    Cvs.WeilForm.ThetaSpaceParseval.weilθ F F=
      (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t*Cvs.L2a.FullTailPolarisation.crossSpec (logScale F) (logScale F) t)+Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy F-
        2*(Cvs.Approximant.EvenConnesEnergyOutput.primeWeight x-continuousWeight (log x))*logPair F F+
          Cvs.Approximant.EvenConnesEnergyOutput.dilationDefect x F-continuousDefect (log x) F F := by
  rw [Cvs.WeilForm.PoleCancelsPrimeMean.weilθ_eq_arch_green_sub_discrepancy (one_div_pos.mpr hx) hm hF hFs,
    primeDiscrepancy_eq hx hFs hf]
  ring

/-- The actual closed even Connes energy has the coupled arithmetic-defect decomposition. -/
theorem Q_even_connesClass_eq_defects {x : ℕ} (hx : 80≤2*π*x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx))=
      (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t*Cvs.L2a.FullTailPolarisation.crossSpec
        (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t)+
      Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)-
        2*(Cvs.Approximant.EvenConnesEnergyOutput.primeWeight x-continuousWeight (log x))*
          logPair (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)+
        Cvs.Approximant.EvenConnesEnergyOutput.dilationDefect x (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)-
          continuousDefect (log x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  rw [Cvs.Approximant.EvenConnesEnergyFormDomain.Q_even_connesClass_eq_weilθ hx]
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  exact weilθ_eq_defects hx0 (Cvs.WeilForm.PoleCancelsPrimeMean.measurable_connesAngularEven hx0)
    (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven hx0) (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x)
    (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx).2.1

/-- The actual logarithmic overlap is the physical angular L² pairing. -/
theorem logPair_eq_physical (F G : ℝ → ℝ) (hs : ∀ θ≤0, F θ=0) :
    logPair F G=∫ θ, F θ*G θ := by
  unfold logPair
  have he : (fun s => logScale F s*logScale G s)=fun s => exp s • (F (exp s)*G (exp s)) := by
    funext s
    unfold logScale
    simp only [smul_eq_mul]
    rw [← Cvs.L2a.TailLogScaleTest.exp_half_sq s]
    ring
  rw [he]
  have hsub := Cvs.WeilForm.ThetaSpaceParseval.integral_exp_smul_Ioi (fun θ => F θ*G θ)
  rw [hsub]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro θ hθ
  rw [hs θ (by simpa only [mem_Ioi, not_lt] using hθ), zero_mul]

private theorem integral_connesEven_cos {x : ℝ} (hx : 1<x) (N : ℕ) (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    (∫ s in (0 : ℝ)..log x, Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s*
      cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (log x) (Cvs.Finite.SymmetricModeSet.mode N) i*s))=
      log x*Cvs.Approximant.ConnesVectorRealScale.connesCoef x N i := by
  have hcoef := Cvs.Approximant.ConnesWindowCosineComplete.coef_evenize (log_pos hx) (Cvs.Approximant.ConnesVectorRealScale.connesK_memLp (zero_lt_one.trans hx))
  have hzero : (∫ s in (0 : ℝ)..log x, Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s)=
      log x*Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0 := by
    have h := Cvs.Finite.WindowCosineBessel.integral_mul_cos (log_pos hx) (Cvs.Approximant.ConnesWindowCosineComplete.connesEven x) 0
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, cos_zero, mul_one, if_true,
      Cvs.Approximant.ConnesWindowCosineComplete.connesEven, hcoef] at h
    unfold Cvs.Approximant.ConnesWindowCosineComplete.connesEven
    linarith
  rcases i with _ | ⟨k,b⟩
  · simpa only [Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode, Int.cast_zero, mul_zero, zero_mul, zero_div, cos_zero,
      mul_one, Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Finset.mem_range,
      Nat.zero_lt_succ, if_true] using hzero
  · have hc : ∀ s : ℝ, cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (log x) (Cvs.Finite.SymmetricModeSet.mode N) (some (k,b))*s)=
        cos (2*π*((k.val+1 : ℕ) : ℝ)/log x*s) := by
      intro s
      cases b <;> simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode, Bool.false_eq_true,
        if_false, if_true, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_add, Nat.cast_one]
      · rw [show 2*π*-(k.val+1 : ℝ)/log x*s=-(2*π*(k.val+1)/log x*s) by ring, cos_neg]
    simp_rw [hc]
    rw [Cvs.Finite.WindowCosineBessel.integral_mul_cos (log_pos hx)]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
      Cvs.Approximant.ConnesWindowCosineComplete.connesEven, hcoef, Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Finset.mem_range,
      show k.val+1<N+1 from Nat.succ_lt_succ k.isLt, if_true, one_mul]
    ring

/-- The mixed physical Connes/cosine overlap has the exact signed coefficient normalization. -/
theorem logPair_connes_modeTest {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    logPair (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N ξ)=
      log x*(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ ξ) := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hL : 0≤log (x : ℝ) := log_natCast_nonneg x
  have he : (fun s => logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (s-log x)*
        logScale (Cvs.Approximant.CosineColumnTailPairing.modeTest x N ξ) (s-log x))=
      (Icc (0 : ℝ) (log x)).indicator
        (fun s => Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s*Cvs.Approximant.CosineColumnTailPairing.cosineSum (log x) N ξ s) := by
    funext s
    rw [Cvs.Xi.PhysicalReciprocalReflection.logScale_connesAngularEven hx0]
    unfold Cvs.Approximant.CosineColumnTailPairing.modeTest
    rw [Cvs.Approximant.CosineColumnTailPairing.logScale_pullTest]
    by_cases hs : s∈Icc (0 : ℝ) (log x)
    · rw [indicator_of_mem hs, indicator_of_mem hs]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, mul_zero]
  unfold logPair
  rw [← integral_add_right_eq_self _ (-log (x : ℝ))]
  simp only [← sub_eq_add_neg]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL]
  have hg : MemLp (Cvs.Approximant.ConnesWindowCosineComplete.connesEven x) 2 volume :=
    Cvs.Approximant.ConnesWindowCosineComplete.memLp_evenize (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK_memLp hx0)
  have hgi := (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL (hg.restrict (Ioc 0 (log x)))).1
  have hi (i : Cvs.Finite.SymmetricModeSet.Idx N) : IntervalIntegrable
      (fun s => ξ i*(Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s*cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (log x) (Cvs.Finite.SymmetricModeSet.mode N) i*s)))
      volume 0 (log x) := by
    apply IntervalIntegrable.const_mul
    exact hgi.mul_continuousOn (by fun_prop : Continuous fun s : ℝ =>
      cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (log x) (Cvs.Finite.SymmetricModeSet.mode N) i*s)).continuousOn
  have hp : (fun s => Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s*Cvs.Approximant.CosineColumnTailPairing.cosineSum (log x) N ξ s)=
      fun s => ∑ i, ξ i*(Cvs.Approximant.ConnesWindowCosineComplete.connesEven x s*cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega (log x) (Cvs.Finite.SymmetricModeSet.mode N) i*s)) := by
    funext s
    unfold Cvs.Approximant.CosineColumnTailPairing.cosineSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hp, intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simp_rw [intervalIntegral.integral_const_mul, integral_connesEven_cos hx1 N]
  unfold dotProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Coefficient orthogonality removes the scalar mismatch from the actual mixed Connes discrepancy. -/
theorem discrepancy_connes_modeTest_of_perp {x : ℕ} (hx : 80≤2*π*x) (N : ℕ)
    (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (hperp : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ ξ=0) :
    discrepancy x (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N ξ)=
      continuousDefect (log x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N ξ)-
        primeDefect x (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N ξ) := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hsF : ∀ θ ∉ Icc (exp (-log (x : ℝ))) 1, Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ=0 := by
    simpa only [exp_neg, exp_log hx0, one_div] using Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x
  have ht := Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N ξ
  have hsG : ∀ θ ∉ Icc (exp (-log (x : ℝ))) 1, Cvs.Approximant.CosineColumnTailPairing.modeTest x N ξ θ=0 := by
    simpa only [exp_neg, exp_log hx0, one_div] using ht.supp
  apply discrepancy_eq_of_logPair_zero (log_natCast_nonneg x) hsF hsG
    (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx).2.1 ht.log.2 x
  rw [logPair_connes_modeTest hx, hperp, mul_zero]

end Cvs.WeilForm.PrimeDiscrepancyTranslation
