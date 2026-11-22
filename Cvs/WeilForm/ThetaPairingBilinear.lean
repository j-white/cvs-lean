import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The θ-space pairing is the window's bilinear form

For two tame functions on `[α, β] ⊂ (0, ∞)` and a complete truncation, `weilθ F G` equals
`crossW P R (logScale F) (logScale G)`, the polarisation of the window Weil form.
-/

namespace Cvs.WeilForm.ThetaPairingBilinear

open Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction
open Cvs.WeilForm.ThetaSpaceParseval (mellinR poleP poleM dil weilθ)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.L2a.WindowFormTailLimit (Tame)

/-- `(f ⋆ g̃)(log k) = √k ∫_{θ>0} F(θ) G(kθ) dθ` for `f = logScale F`, `g = logScale G`. -/
theorem crossConv_logScale_log (F G : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    Cvs.WeilForm.TruncatedFormPolarised.crossConv (logScale F) (logScale G) (Real.log k)
      = √k * ∫ θ in Ioi (0 : ℝ), F θ * G (k * θ) := by
  unfold Cvs.WeilForm.TruncatedFormPolarised.crossConv
  have e : (fun x => logScale F x * logScale G (x + Real.log k))
      = fun x => exp x • (fun θ => √k * (F θ * G (k * θ))) (exp x) := by
    funext x; unfold logScale
    rw [smul_eq_mul, exp_add, exp_log hk, mul_comm (exp x) k]
    have h1 : exp ((x + Real.log k) / 2) = exp (x / 2) * √k := by
      rw [show (x + Real.log k) / 2 = x / 2 + Real.log k / 2 by ring, exp_add, sqrt_eq_rpow,
        rpow_def_of_pos hk]
      ring_nf
    rw [h1, ← Cvs.L2a.TailLogScaleTest.exp_half_sq x]; ring
  rw [e, ← integral_const_mul]
  exact Cvs.WeilForm.ThetaSpaceParseval.integral_exp_smul_Ioi (fun θ => √k * (F θ * G (k * θ)))

/-- **The prime channel, polarised.** -/
theorem tsum_dil_eq {F G : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hF : ∀ θ ∉ Icc α β, F θ = 0)
    (hG : ∀ θ ∉ Icc α β, G θ = 0) {P R : ℕ} (hP : β / α ≤ P)
    (hR : Real.log (β / α) ≤ R * Real.log 2) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F G n + dil G F n)
      = Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
          (Cvs.WeilForm.TruncatedFormPolarised.polar (logScale F) (logScale G)) / 2 := by
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image, Finset.sum_div]
  rw [tsum_eq_sum (s := Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      unfold Cvs.WeilForm.TruncatedFormPolarised.polar
      rw [Cvs.WeilForm.TruncatedFormPolarised.crossConv_neg (logScale G) (logScale F),
        Cvs.WeilForm.TruncatedFormPolarised.crossConv_neg (logScale F) (logScale G),
        crossConv_logScale_log F G hk', crossConv_logScale_log G F hk']
      have hs : (k : ℝ) ^ (-(1 / 2) : ℝ) * √(k : ℝ) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk']; norm_num
      unfold dil
      set d1 := ∫ θ in Ioi (0 : ℝ), F θ * G (k * θ)
      set d2 := ∫ θ in Ioi (0 : ℝ), G θ * F (k * θ)
      linear_combination (-(ArithmeticFunction.vonMangoldt k * (d1 + d2))) * hs
  · intro n hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    by_cases hd : β / α < n
    · simp [Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support hα hF hG hd,
        Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support hα hG hF hd]
    exfalso
    apply hn
    replace hd := not_lt.mp hd
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hΛ)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    exact Cvs.WeilForm.ThetaFormWindowIdentification.mem_primePowIndex hΛ (by exact_mod_cast hd.trans hP)
      ((Real.log_le_log hn' hd).trans hR)

/-- **`weilθ F G` is the window's bilinear form `crossW` of `logScale F`, `logScale G`.** -/
theorem weilθ_eq_crossW {F G : ℝ → ℝ} {α β : ℝ} (hF : Tame F α β) (hG : Tame G α β)
    {P R : ℕ} (hP : β / α ≤ P) (hR : Real.log (β / α) ≤ R * Real.log 2) :
    weilθ F G = Cvs.WeilForm.SymmetricBilinearForm.crossW P R (logScale F) (logScale G) := by
  obtain ⟨hf1, hf2⟩ := hF.log
  obtain ⟨hg1, hg2⟩ := hG.log
  unfold weilθ Cvs.WeilForm.SymmetricBilinearForm.crossW Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG
  rw [Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hF.supp, Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hG.supp,
    ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp F,
    ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp G,
    ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp_neg F,
    ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp_neg G,
    Cvs.L2a.WindowFormTailLimit.integral_arch_crossSpec_eq hf2 hf1 hF.levy hg2 hg1 hG.levy,
    tsum_dil_eq hF.pos hF.supp hG.supp hP hR]
  ring

end Cvs.WeilForm.ThetaPairingBilinear
