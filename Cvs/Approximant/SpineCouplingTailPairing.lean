import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CouplingRegularisedProfile
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.BilinearCrossRepresentatives
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.ThetaPairingBilinear
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The CORE coupling of a spine vector is the tail pairing

For `80 ≤ 2πx` and a tame `v` on `[1/x, 1]`, the form-domain bilinear pairing of the spine vector
`spineMap x a` with the translated class of `v` equals `−weilθ(τ_reg, v)`, the pairing of `v`
against the regularised tail of the spine profile.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.Approximant.SpineCouplingTailPairing

open Cvs.WeilForm.ThetaSpaceParseval (weilθ)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.WindowFormTailLimit (Tame regProfile)

/-- `80 ≤ 2πx` forces `0 < x`. -/
theorem hx0_of_scale {x : ℕ} (hx : 80 ≤ 2 * π * x) : (0:ℝ) < x := by
  have : (0:ℝ) < 2 * π * x := by linarith
  nlinarith [Real.pi_pos]

/-- The log-scaled test `v`, moved into the window `(0, log x]`. -/
def fv (x : ℕ) (v : ℝ → ℝ) (s : ℝ) : ℝ := Cvs.L2a.TailLogScaleTest.logScale v (s - Real.log x)

theorem fv_eq_translate (x : ℕ) (v : ℝ → ℝ) :
    fv x v = fun s => Cvs.L2a.TailLogScaleTest.logScale v (s + -Real.log x) := by
  funext s; rw [fv, sub_eq_add_neg]

theorem fv_memLp {x : ℕ} {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) : MemLp (fv x v) 2 volume := by
  rw [fv_eq_translate]; exact Cvs.WeilForm.CentredWindowTranslate.memLp_translate _ hv.log.2

theorem fv_levy {x : ℕ} {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fv x v)) (Ioi 0) volume := by
  rw [fv_eq_translate, Cvs.WeilForm.TailBoundOnWindow.levy_translate]; exact hv.levy

/-- `fv` vanishes off `[0, log x]` when `v` is tame on `[1/x, 1]`. -/
theorem fv_supp {x : ℕ} (hx0 : (0:ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    ∀ s ∉ Icc (0:ℝ) (Real.log x), fv x v s = 0 := by
  intro s hs
  have hw : (1 : ℝ) / x = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hx0, one_div]
  unfold fv Cvs.L2a.TailLogScaleTest.logScale
  rw [hv.supp, zero_mul]
  rintro ⟨h1, h2⟩
  apply hs
  rw [hw, Real.exp_le_exp] at h1
  rw [← Real.exp_zero, Real.exp_le_exp] at h2
  exact ⟨by linarith, by linarith⟩

theorem fv_ae_supp {x : ℕ} (hx0 : (0:ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    ∀ᵐ s ∂volume, s ∉ Ioc (0:ℝ) (Real.log x) → fv x v s = 0 := by
  filter_upwards [(Set.countable_singleton (0:ℝ)).ae_notMem volume] with s hs0 hs
  refine fv_supp hx0 hv s fun h => hs ⟨lt_of_le_of_ne h.1 (fun e => hs0 (by simp [← e])), h.2⟩

/-- The form-domain class of a tame test on `[1/x, 1]`. -/
def wv {x : ℕ} (hx0 : (0:ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.Approximant.SpineSubspace.ofFun (Real.log_natCast_nonneg x) (fv_memLp hv) (fv_ae_supp hx0 hv) (fv_levy hv)

theorem coe_wv_ae {x : ℕ} (hx0 : (0:ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    (((wv hx0 hv : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
      : Lp ℝ 2 volume) =ᵐ[volume] fv x v :=
  Cvs.Approximant.SpineSubspace.coe_ofFun_ae _ _ _ _

/-- The spine profile's derivative data (the rungs are `C²` on `[−1, 1]`). -/
theorem spine_profile_data {x : ℕ} (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x)
    (a : S → ℝ) :
    ∃ G₁ G₂ : ℝ → ℝ,
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (G₁ s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) ∧ ContinuousOn G₂ (uIcc (-1) 1) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a (-s) = Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a s) ∧
      ∫ s in (-1 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a s = 0 := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  set c := 2 * π * (x : ℝ) with hc
  have hex : ∀ i : Option S, ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c (Cvs.L2a.ProlateFamilySpine.kOf i) χ := by
    rintro (_ | j)
    · exact Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
    · exact Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.2 (hS j j.2)⟩
  have hspec := fun i => Cvs.Prolate.EvenRungsByIndex.rung_spec (hex i)
  have hG := Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span (Cvs.L2a.ProlateFamilySpine.bOf c a) (fun i => (hspec i).1)
  have hG₁ := Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span (Cvs.L2a.ProlateFamilySpine.bOf c a) (fun i => (hspec i).2.1)
  rw [Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG] at hG
  refine ⟨_, _, hG, hG₁, ?_, ?_, Cvs.Approximant.DeepIndexSpineSpan.integral_spineG hc0 a⟩
  · exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hspec i).2.2.1
  · intro s hs
    rw [← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG]
    exact Finset.sum_congr rfl fun i _ => by rw [(hspec i).2.2.2.2.1 s hs]

/-- **The CORE coupling of a spine vector is the tail pairing**: for `80 ≤ 2πx` and `v` tame on
`[1/x, 1]`, `QWbil (spineMap x a) w_v = −weilθ(τ_reg, v)`, with `τ_reg` the regularised tail of the
spine profile. -/
theorem QWbil_spineMap_eq_neg_tail {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    {v : ℝ → ℝ} (hv : Tame v (1 / x) 1) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a)
        (wv (hx0_of_scale hx) hv)
      = -weilθ (fullTail (psi (2 * π * x)
          (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)))) v := by
  have hx0 : (0:ℝ) < x := hx0_of_scale hx
  have hx2 : 2 ≤ x := by
    by_contra h
    have : (x : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (not_le.1 h)
    nlinarith [Real.pi_lt_four]
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply]
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.crossW_congr x (Nat.clog 2 x)
    ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.SpineSubspace.coe_spineMap_ae x hx a))
    ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (coe_wv_ae hx0 hv))]
  change Cvs.WeilForm.SymmetricBilinearForm.crossW x (Nat.clog 2 x)
    (fun s => Cvs.L2a.TailLogScaleTest.logScale (window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (s - Real.log x))
    (fun s => Cvs.L2a.TailLogScaleTest.logScale v (s - Real.log x)) = _
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.crossW_translate]
  have hα : 2 * π / (2 * π * x) = 1 / x := by field_simp
  have hF := Cvs.Approximant.SpineSubspace.tame_spine hx (Cvs.Approximant.SpineSubspace.SF_lt x) a
  rw [hα] at hF
  obtain ⟨hL0, hexp, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx2
  have hP : (1 : ℝ) / (1 / x) ≤ x := by rw [one_div_one_div]
  have hR' : Real.log (1 / (1 / x)) ≤ (Nat.clog 2 x : ℝ) * Real.log 2 := by rwa [one_div_one_div]
  rw [hα, ← Cvs.WeilForm.ThetaPairingBilinear.weilθ_eq_crossW hF hv hP hR', Cvs.WeilForm.ThetaSpaceParseval.weilθ_comm]
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, heven, hGi⟩ := spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) a
  have hc : 2 * π ≤ 2 * π * x := by
    have : (1:ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
    nlinarith [Real.pi_pos]
  rw [← Cvs.L2a.CouplingRegularisedProfile.coupling_eq_neg_tail_reg hc hg hg₁ hg₂c heven hGi hv, hα, Cvs.WeilForm.ThetaSpaceParseval.weilθ_comm]

end Cvs.Approximant.SpineCouplingTailPairing
