import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MellinZeroSum
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ContinuousApproximation
import Cvs.WeilForm.Mollify.MollifySmooth
import Cvs.WeilForm.Mollify.WindowNormalisation
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.PrimeSideExplicitIndex
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.WeilFormNullSets
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowFormTranslationInvariant
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowTestOperators
import Cvs.WeilForm.WindowTestParseval
import Cvs.WeilForm.WindowTestSelfAdjoint
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Weil's criterion on the window's test functions, and Parseval for the zero samples
RH holds iff, for every `x ≥ x₀ ≥ 2`, `W(f, f) ≥ 0` for every `f ∈ 𝓓((0, log x), ℝ)`, iff
`W(f, f) = Σ_ρ m_ρ |f̂(ρ)|²` for every such `f`. A class of the form domain at `x` is a limit of
`ContinuousApproximation`'s smooth approximants, and each, translated, lies in `𝓓((0, log x'), ℝ)` for any `x' > x`.
-/

noncomputable section

open scoped Distributions
open Set MeasureTheory Complex

namespace Cvs.WeilForm.WindowTestWeilCriterion
open Cvs.ZeroCounting

open Cvs.WeilForm.WindowTestOperators Cvs.WeilForm.WindowTestSelfAdjoint Cvs.WeilForm.WindowTestParseval
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.WeilForm.MellinZeroSum (Z)

/-! ### Test functions and the window form -/

/-- A smooth function with closed support in `(0, L)`, as a test function on the window. -/
def ofContDiff {L : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hs : tsupport f ⊆ Ioo 0 L) : 𝓓(win L, ℝ) where
  toFun := f
  contDiff' := hf
  hasCompactSupport' := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f)
    (hs.trans Ioo_subset_Icc_self)
  tsupport_subset' := hs

theorem coe_ofContDiff {L : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hs : tsupport f ⊆ Ioo 0 L) : ⇑(ofContDiff hf hs) = f := rfl

/-- **The Weil form of a test function is the window form of the function**:
`W(f, f) = weilForm x ⌈log₂ x⌉ f`. -/
theorem weil_self_eq_weilForm {x : ℕ} (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)) :
    weil hx0 f f = Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) f := by
  rw [weil_self]
  show Cvs.WeilForm.WeilFormOnWindowL2.weilQ _ _ _ = _
  have h := Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_one f))
  refine Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (h.trans (Filter.Eventually.of_forall fun s => ?_))
  rw [Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0]
  refine congrFun (indicator_eq_self.2 ?_) s
  exact (subset_tsupport _).trans (f.tsupport_subset.trans Ioo_subset_Ico_self)

/-- At complete `(P, R)` the window form of a function vanishing off `(0, L]` does not depend on `(P, R)`. -/
theorem weilForm_eq_of_complete {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : ∀ s ∉ Ioc (0 : ℝ) L, f s = 0)
    {P R P' R' : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (hP' : Real.exp L ≤ P')
    (hR' : L ≤ R' * Real.log 2) : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P' R' f := by
  have hfi : indicator (Ioc 0 L) f = f :=
    indicator_eq_self.2 fun s hs => by_contra fun h => hs (hf s h)
  rw [← hfi, Cvs.WeilForm.PrimeSideExplicitIndex.weilForm_eq_range hL hP hR, Cvs.WeilForm.PrimeSideExplicitIndex.weilForm_eq_range hL hP' hR']

/-- A function vanishing off `(0, L]`, translated by `δ/2 > 0`, has closed support in `(0, L + δ)`. -/
theorem tsupport_translate_subset {L δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg : ∀ s ∉ Ioc (0 : ℝ) L, g s = 0) :
    tsupport (fun s => g (s + -(δ / 2))) ⊆ Ioo 0 (L + δ) := by
  have hsub : tsupport (fun s => g (s + -(δ / 2))) ⊆ Icc (δ / 2) (L + δ / 2) := by
    refine closure_minimal (fun s hs => ?_) isClosed_Icc
    by_contra hns
    refine hs (hg _ fun hm => hns ?_)
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  exact hsub.trans fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-! ### From the test functions to the form domain -/

/-- **`W ≥ 0` on the test functions at `x' > x` gives `Q ≥ 0` on the form domain at `x`**, for `2 ≤ x`. -/
theorem Q_nonneg_of_weil_nonneg {x x' : ℕ} (hx : 2 ≤ x) (hxx' : x < x')
    (h : ∀ (hx0 : (0 : ℝ) < x') (f : 𝓓(win (Real.log x'), ℝ)), 0 ≤ weil hx0 f f)
    (φ : Dom x) : 0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ := by
  obtain ⟨hL, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx
  by_cases hφ : φ = 0
  · rw [hφ, Cvs.WeilForm.SymmetricBilinearForm.Q_zero]
  set hh := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) with hhdef
  have hE : 0 < ∫ s, hh s ^ 2 := by
    rw [hhdef, ← Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
    exact pow_pos (norm_pos_iff.mpr fun h0 => hφ (Subtype.ext h0)) 2
  have hmem := Cvs.WeilForm.Mollify.WindowNormalisation.mem_windowSet_normalised (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.WindowRepresentative.rep_supp _) φ.2 hE
  obtain ⟨g, hg, hgm, -, hgform⟩ := Cvs.WeilForm.WeilFormNullSets.exists_measurable_rep x (Nat.clog 2 x) hmem
  obtain ⟨Ξ, hΞ, -, -, hlim, hshape⟩ := Cvs.WeilForm.Mollify.ContinuousApproximation.exists_windowApprox hL x (Nat.clog 2 x) hg hgm
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlt : (x : ℝ) < x' := by exact_mod_cast hxx'
  have hx2 : (0 : ℝ) < x' := hx0.trans hlt
  set δ := Real.log x' - Real.log x with hδ
  have hδ0 : 0 < δ := sub_pos.2 (Real.log_lt_log hx0 hlt)
  have hlog : Real.log x + δ = Real.log x' := by rw [hδ]; ring
  have hP' : Real.exp (Real.log x) ≤ (x' : ℝ) := hP.trans hlt.le
  have hR' : Real.log x ≤ (Nat.clog 2 x' : ℝ) * Real.log 2 := by
    refine hR.trans (mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by norm_num)))
    exact_mod_cast Nat.clog_mono_right 2 hxx'.le
  have hnn : ∀ n, 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Ξ n) := by
    intro n
    obtain ⟨c, m, hcm⟩ := hshape n
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ξ n) := by
      rw [hcm]
      exact contDiff_const.mul
        (Cvs.WeilForm.Mollify.MollifySmooth.contDiff_conv (Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hg.1 _ m) (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL m))
    have hsupp : ∀ s ∉ Ioc (0 : ℝ) (Real.log x), Ξ n s = 0 := (hΞ n).2.1
    have hts : tsupport (fun s => Ξ n (s + -(δ / 2))) ⊆ Ioo 0 (Real.log x') := by
      rw [← hlog]
      exact tsupport_translate_subset hδ0 hsupp
    have hcd' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => Ξ n (s + -(δ / 2))) :=
      hcd.comp (contDiff_id.add contDiff_const)
    have h1 := h hx2 (ofContDiff hcd' hts)
    rw [weil_self_eq_weilForm, coe_ofContDiff, Cvs.WeilForm.WindowFormTranslationInvariant.weilForm_translate,
      weilForm_eq_of_complete hL.le hsupp hP' hR' hP hR] at h1
    exact h1
  have hg0 : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) g := ge_of_tendsto' hlim hnn
  rw [hgform, Cvs.WeilForm.Mollify.WindowNormalisation.weilForm_normalised _ _ hE, ← (Cvs.WeilForm.WindowRepresentative.weilQW_rep _ _ _).1] at hg0
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hE)).mp hg0

/-! ### RH -/

/-- **RH from nonnegativity of the Weil form on `𝓓((0, log x), ℝ)` at every `x ≥ x₀`.** -/
theorem rh_of_forall_weil_nonneg (x₀ : ℕ)
    (h : ∀ x : ℕ, x₀ ≤ x → ∀ (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)), 0 ≤ weil hx0 f f) :
    RiemannHypothesis :=
  Cvs.WeilForm.WindowWeilCriterion.rh_of_windowPos (max x₀ 2) fun x hx φ =>
    Q_nonneg_of_weil_nonneg (le_of_max_le_right hx) (Nat.lt_succ_self x)
      (h (x + 1) (by have := le_of_max_le_left hx; omega)) φ

/-- **RH is nonnegativity of the Weil form on `𝓓((0, log x), ℝ)` at every `x ≥ x₀`**, for any `x₀ ≥ 2`. -/
theorem rh_iff_forall_weil_nonneg (x₀ : ℕ) (hx₀ : 2 ≤ x₀) :
    RiemannHypothesis ↔
      ∀ x : ℕ, x₀ ≤ x → ∀ (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)), 0 ≤ weil hx0 f f :=
  ⟨fun hRH _ hx hx0 f => weil_self_nonneg_of_rh hRH hx0 (hx₀.trans hx) f, rh_of_forall_weil_nonneg x₀⟩

/-- **RH is Parseval for the zero samples**: `W(f, f) = Σ_ρ m_ρ |f̂(ρ)|²` for every `f ∈ 𝓓((0, log x), ℝ)`
at every `x ≥ x₀`, for any `x₀ ≥ 2`. -/
theorem rh_iff_forall_hasSum_parseval (x₀ : ℕ) (hx₀ : 2 ≤ x₀) :
    RiemannHypothesis ↔ ∀ x : ℕ, x₀ ≤ x → ∀ (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)),
      HasSum (fun ρ : Z => (Cvs.Criterion.divisorWeight ρ : ℝ) * ‖hat (Real.log x) f ρ‖ ^ 2)
        (weil hx0 f f) :=
  ⟨fun hRH _ hx hx0 f => hasSum_weil_self_of_rh hRH hx0 (hx₀.trans hx) f,
    fun h => rh_of_forall_weil_nonneg x₀ fun x hx hx0 f =>
      (h x hx hx0 f).nonneg fun _ => by positivity⟩

end Cvs.WeilForm.WindowTestWeilCriterion
