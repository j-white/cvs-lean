import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ParallelogramLaw
import Cvs.WeilForm.PrimeShiftOperator
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowMomentsTranslationInvariant
import Cvs.WeilForm.WindowRepresentative
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The spine subspace `R_F` inside the form domain at `L = log x`

The spine tests `k_G`, translated into the window `(0, log x]`, are form-domain classes; `R_F` is
their span, finite-dimensional, and Cvs.L2a.SpineProfileWindowNormPos makes `Q > 0` on its nonzero vectors past `c₀W ≤ 2πx`.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.Approximant.SpineSubspace

/-! ### Functions as window and form-domain classes -/

/-- The window class of a square-integrable function: `PrimeShiftOperator`'s cut of its `L²` class to `(0, L]`. -/
def ofWin (L : ℝ) {f : ℝ → ℝ} (h2 : MemLp f 2 volume) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  Cvs.WeilForm.PrimeShiftOperator.cutLp L (h2.toLp f)

/-- When `f` vanishes a.e. off `(0, L]`, the class `ofWin f` is a.e. `f`. -/
theorem coe_ofWin_ae {L : ℝ} {f : ℝ → ℝ} (h2 : MemLp f 2 volume)
    (hs : ∀ᵐ s ∂volume, s ∉ Set.Ioc (0:ℝ) L → f s = 0) :
    ((ofWin L h2 : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume) =ᵐ[volume] f := by
  unfold ofWin
  filter_upwards [Cvs.WeilForm.PrimeShiftOperator.cutLp_ae L (h2.toLp f), h2.coeFn_toLp, hs] with s h1 h2' h3
  rw [h1]
  by_cases hm : s ∈ Set.Ioc (0:ℝ) L
  · rw [indicator_of_mem hm, h2']
  · rw [indicator_of_notMem hm, h3 hm]

/-- The representative of `ofWin f` is a.e. `f`. -/
theorem rep_ofWin_ae {L : ℝ} {f : ℝ → ℝ} (h2 : MemLp f 2 volume)
    (hs : ∀ᵐ s ∂volume, s ∉ Set.Ioc (0:ℝ) L → f s = 0) :
    Cvs.WeilForm.WindowRepresentative.rep (ofWin L h2) =ᵐ[volume] f :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (coe_ofWin_ae h2 hs)

/-- The Lévy integrand depends only on the a.e. class. -/
theorem levy_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g := by
  funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  rw [Cvs.WeilForm.ParallelogramLaw.selfConvolution_congr_ae h, Cvs.WeilForm.ParallelogramLaw.selfConvolution_congr_ae h]

/-- A square-integrable, Lévy-integrable function vanishing a.e. off `(0, L]`, as a form-domain
class. -/
def ofFun {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (h2 : MemLp f 2 volume)
    (hs : ∀ᵐ s ∂volume, s ∉ Set.Ioc (0:ℝ) L → f s = 0)
    (hlev : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) volume) : Cvs.WeilForm.FormDomain.formDomain hL :=
  ⟨ofWin L h2, by
    show IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (ofWin L h2))) (Set.Ioi 0) volume
    rw [levy_congr_ae (rep_ofWin_ae h2 hs)]; exact hlev⟩

/-- The class `ofFun f` is a.e. `f`. -/
theorem coe_ofFun_ae {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (h2 : MemLp f 2 volume)
    (hs : ∀ᵐ s ∂volume, s ∉ Set.Ioc (0:ℝ) L → f s = 0)
    (hlev : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) volume) :
    (((ofFun hL h2 hs hlev : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume)
      =ᵐ[volume] f :=
  coe_ofWin_ae h2 hs

/-- `Q(ofFun f)` is the Weil form of `f`. -/
theorem Q_ofFun {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {f : ℝ → ℝ} (h2 : MemLp f 2 volume)
    (hs : ∀ᵐ s ∂volume, s ∉ Set.Ioc (0:ℝ) L → f s = 0)
    (hlev : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) volume) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (ofFun hL h2 hs hlev) = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f :=
  Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (coe_ofFun_ae hL h2 hs hlev)

/-! ### The spine tests -/

/-- The spine test `k_G`, moved from `[−log x, 0]` into the window `(0, log x]`. -/
def kG (x : ℕ) {S : Finset ℕ} (a : S → ℝ) (s : ℝ) : ℝ :=
  Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (s - Real.log x)

/-- The spine window is tame. -/
theorem tame_spine {x : ℕ} (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x)
    (a : S → ℝ) :
    Cvs.L2a.WindowFormTailLimit.Tame (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))
      (2 * π / (2 * π * x)) 1 := by
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
  have heven : ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.Approximant.DeepIndexSpineSpan.spineG c a (-s) = Cvs.Approximant.DeepIndexSpineSpan.spineG c a s := by
    intro s hs
    rw [← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG]
    exact Finset.sum_congr rfl fun i _ => by rw [(hspec i).2.2.2.2.1 s hs]
  obtain ⟨h01, h01c, h01i⟩ := Cvs.L2a.WindowFormTailLimit.std_of_even hG hG₁ heven (Cvs.Approximant.DeepIndexSpineSpan.integral_spineG hc0 a)
  exact Cvs.L2a.WindowFormTailLimit.tame_window (by positivity) h01 h01c h01i

/-- The spine profile is additive in its coefficients. -/
theorem spineG_add (c : ℝ) {S : Finset ℕ} (a b : S → ℝ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c (a + b) = fun u => Cvs.Approximant.DeepIndexSpineSpan.spineG c a u + Cvs.Approximant.DeepIndexSpineSpan.spineG c b u := by
  funext u; simp only [Cvs.Approximant.DeepIndexSpineSpan.spineG, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The spine profile is homogeneous in its coefficients. -/
theorem spineG_smul (c t : ℝ) {S : Finset ℕ} (a : S → ℝ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c (t • a) = fun u => t * Cvs.Approximant.DeepIndexSpineSpan.spineG c a u := by
  funext u; simp only [Cvs.Approximant.DeepIndexSpineSpan.spineG, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The window map is additive. -/
theorem window_add (w : ℝ) (G H : ℝ → ℝ) :
    Cvs.Xi.EImageWindowPoisson.window w (fun u => G u + H u) = fun θ => Cvs.Xi.EImageWindowPoisson.window w G θ + Cvs.Xi.EImageWindowPoisson.window w H θ := by
  funext θ; unfold Cvs.Xi.EImageWindowPoisson.window
  by_cases h : θ ∈ Icc w 1
  · simp only [indicator_of_mem h, Cvs.Xi.EImageWindowPoisson.eimage_add]
  · simp [indicator_of_notMem h]

/-- The window map is homogeneous. -/
theorem window_smul (w t : ℝ) (G : ℝ → ℝ) :
    Cvs.Xi.EImageWindowPoisson.window w (fun u => t * G u) = fun θ => t * Cvs.Xi.EImageWindowPoisson.window w G θ := by
  funext θ; unfold Cvs.Xi.EImageWindowPoisson.window
  by_cases h : θ ∈ Icc w 1
  · simp only [indicator_of_mem h, Cvs.Xi.EImageWindowPoisson.eimage_smul]
  · simp [indicator_of_notMem h]

/-- `k_G` is additive in its coefficients. -/
theorem kG_add (x : ℕ) {S : Finset ℕ} (a b : S → ℝ) :
    kG x (a + b) = fun s => kG x a s + kG x b s := by
  funext s; unfold kG Cvs.L2a.TailLogScaleTest.logScale
  rw [spineG_add, window_add]; ring

/-- `k_G` is homogeneous in its coefficients. -/
theorem kG_smul (x : ℕ) (t : ℝ) {S : Finset ℕ} (a : S → ℝ) :
    kG x (t • a) = fun s => t * kG x a s := by
  funext s; unfold kG Cvs.L2a.TailLogScaleTest.logScale
  rw [spineG_smul, window_smul]; ring

/-- `k_G` is a translate of the log-scaled spine window. -/
theorem kG_eq_translate (x : ℕ) {S : Finset ℕ} (a : S → ℝ) :
    kG x a = fun s => Cvs.L2a.TailLogScaleTest.logScale
      (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (s + -Real.log x) := by
  funext s; rw [kG, sub_eq_add_neg]

/-- `k_G` is square integrable. -/
theorem kG_memLp {x : ℕ} (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x)
    (a : S → ℝ) : MemLp (kG x a) 2 volume := by
  rw [kG_eq_translate]; exact Cvs.WeilForm.CentredWindowTranslate.memLp_translate _ (tame_spine hx hS a).log.2

/-- `k_G` is Lévy integrable. -/
theorem kG_levy {x : ℕ} (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x)
    (a : S → ℝ) : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (kG x a)) (Ioi 0) volume := by
  rw [kG_eq_translate, Cvs.WeilForm.TailBoundOnWindow.levy_translate]; exact (tame_spine hx hS a).levy

/-- `k_G` vanishes off `[0, log x]`. -/
theorem kG_supp {x : ℕ} (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x)
    (a : S → ℝ) : ∀ s ∉ Icc (0:ℝ) (Real.log x), kG x a s = 0 := by
  intro s hs
  have hx0 : (0:ℝ) < x := by
    have : (0:ℝ) < 2 * π * x := by linarith
    nlinarith [Real.pi_pos]
  have hw : 2 * π / (2 * π * x) = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hx0]; field_simp
  unfold kG Cvs.L2a.TailLogScaleTest.logScale
  rw [(tame_spine hx hS a).supp, zero_mul]
  rintro ⟨h1, h2⟩
  apply hs
  rw [hw, Real.exp_le_exp] at h1
  rw [← Real.exp_zero, Real.exp_le_exp] at h2
  exact ⟨by linarith, by linarith⟩

/-- `k_G` vanishes a.e. off `(0, log x]`. -/
theorem kG_ae_supp {x : ℕ} (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x)
    (a : S → ℝ) : ∀ᵐ s ∂volume, s ∉ Ioc (0:ℝ) (Real.log x) → kG x a s = 0 := by
  filter_upwards [(Set.countable_singleton (0:ℝ)).ae_notMem volume] with s hs0 hs
  refine kG_supp hx hS a s fun h => hs ⟨lt_of_le_of_ne h.1 (fun e => hs0 (by simp [← e])), h.2⟩

/-- The Weil form of `k_G` is that of the untranslated spine window. -/
theorem weilForm_kG (P R : ℕ) (x : ℕ) {S : Finset ℕ} (a : S → ℝ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (kG x a)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
          (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))) :=
  Cvs.WeilForm.WindowMomentsTranslationInvariant.weilForm_translate P R _ (Real.log x)

/-! ### The subspace `R_F` -/

/-- The L2a threshold `c₀W ≤ 2πx` gives the spine scale `80 ≤ 2πx`. -/
theorem scale80_of_c0W {x : ℕ} (hx : Cvs.L2a.WindowChainInputsProlate.c0W ≤ 2 * π * x) : 80 ≤ 2 * π * x :=
  (Cvs.L2a.BandInputsFromCutMultipliers.scale_ge (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx)).2

/-- The index set of `R_F`: `1 ≤ j < x`. -/
abbrev SF (x : ℕ) : Finset ℕ := (Finset.range x).filter (1 ≤ ·)

/-- Every index of `R_F` is below `x`. -/
theorem SF_lt (x : ℕ) : ∀ j ∈ SF x, j < x := fun _ hj =>
  Finset.mem_range.1 (Finset.mem_filter.1 hj).1

/-- The linear map `a ↦ k_G` into the form domain, at `80 ≤ 2πx`. -/
def spineMapOf (x : ℕ) (hx : 80 ≤ 2 * π * x) :
    (SF x → ℝ) →ₗ[ℝ] Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) where
  toFun a := ofFun _ (kG_memLp hx (SF_lt x) a) (kG_ae_supp hx (SF_lt x) a) (kG_levy hx (SF_lt x) a)
  map_add' a b := by
    apply Subtype.ext; apply Subtype.ext; apply Lp.ext
    rw [Submodule.coe_add, Submodule.coe_add]
    filter_upwards [coe_ofFun_ae (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) (a + b))
        (kG_ae_supp hx (SF_lt x) (a + b)) (kG_levy hx (SF_lt x) (a + b)),
      coe_ofFun_ae (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) a)
        (kG_ae_supp hx (SF_lt x) a) (kG_levy hx (SF_lt x) a),
      coe_ofFun_ae (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) b)
        (kG_ae_supp hx (SF_lt x) b) (kG_levy hx (SF_lt x) b),
      Lp.coeFn_add (E := ℝ) (p := 2) (μ := volume) _ _] with s h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3, kG_add]
  map_smul' t a := by
    set A := ofFun (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) a)
        (kG_ae_supp hx (SF_lt x) a) (kG_levy hx (SF_lt x) a) with hA
    apply Subtype.ext; apply Subtype.ext; apply Lp.ext
    rw [RingHom.id_apply, Submodule.coe_smul, Submodule.coe_smul]
    filter_upwards [coe_ofFun_ae (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) (t • a))
        (kG_ae_supp hx (SF_lt x) (t • a)) (kG_levy hx (SF_lt x) (t • a)),
      coe_ofFun_ae (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) a)
        (kG_ae_supp hx (SF_lt x) a) (kG_levy hx (SF_lt x) a),
      Lp.coeFn_smul (E := ℝ) (p := 2) (μ := volume) t
        ((A : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 volume)] with s h1 h2 h4
    rw [h4, Pi.smul_apply, h1, h2, kG_smul, smul_eq_mul]

open Classical in
/-- The spine map `a ↦ k_G`, extended by `0` below `80 ≤ 2πx`. -/
def spineMap (x : ℕ) : (SF x → ℝ) →ₗ[ℝ] Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  if hx : 80 ≤ 2 * π * x then spineMapOf x hx else 0

/-- `R_F`: the range of the spine map at `L = log x`, the `k_G` classes of the mean-corrected
profiles `Σ a_j (h_{4j} − α_j h₀)`, `1 ≤ j < x`; it is `⊥` when `2πx < 80`. -/
def RF (x : ℕ) : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :=
  LinearMap.range (spineMap x)

/-- The additive group structure on `R_F`, given explicitly: instance search cannot unify the
nested submodule instances through the `Lp` ambient space. -/
instance RF.addCommGroup (x : ℕ) : AddCommGroup (RF x) :=
  @Submodule.addCommGroup ℝ _ _ (Submodule.addCommGroup _) (Submodule.module _) (RF x)

/-- `R_F` is finite-dimensional. -/
instance RF.finiteDimensional (x : ℕ) : FiniteDimensional ℝ (RF x) :=
  Module.Finite.range (spineMap x)

/-- **`R_F` is spanned by the `k_G` classes** of the coordinate vectors. -/
theorem RF_eq_span (x : ℕ) :
    RF x = Submodule.span ℝ (Set.range fun j : SF x => spineMap x (Pi.single j 1)) := by
  rw [RF, LinearMap.range_eq_map, ← (Pi.basisFun ℝ (SF x)).span_eq, Submodule.map_span,
    ← Set.range_comp]
  congr 2
  funext j
  simp [Pi.basisFun_apply]

/-- The class `spineMap x a` is a.e. the function `k_G`. -/
theorem coe_spineMap_ae (x : ℕ) (hx : 80 ≤ 2 * π * x) (a : SF x → ℝ) :
    (((spineMap x a : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
      : Lp ℝ 2 volume) =ᵐ[volume] kG x a := by
  rw [spineMap, dite_eq_left hx]
  exact coe_ofFun_ae (Real.log_natCast_nonneg x) (kG_memLp hx (SF_lt x) a)
    (kG_ae_supp hx (SF_lt x) a) (kG_levy hx (SF_lt x) a)

/-- `Q` on the spine map is the Weil form of the spine window. -/
theorem Q_spineMap (x : ℕ) (hx : 80 ≤ 2 * π * x) (P R : ℕ) (a : SF x → ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R (spineMap x a)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
          (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))) := by
  rw [spineMap, dite_eq_left hx]
  simp only [spineMapOf, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Q_ofFun, weilForm_kG]

/-- **`Q > 0` on the nonzero vectors of `R_F`** at `P = x`, `R = ⌈log₂ x⌉`, past `c₀W ≤ 2πx`. -/
theorem RF_pos (x : ℕ) (hx : Cvs.L2a.WindowChainInputsProlate.c0W ≤ 2 * π * x) :
    ∀ r ∈ RF x, r ≠ 0 → 0 < Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r := by
  rintro r ⟨a, rfl⟩ hr
  have ha : a ≠ 0 := by rintro rfl; exact hr (map_zero _)
  rw [Q_spineMap x (scale80_of_c0W hx)]
  exact (Cvs.L2a.SpineProfileWindowNormPos.L2a_window_full_strict x hx).2 a ha

/-! ### The window sizes at `L = log x` -/

/-- **The sizes**: `0 < log x`, `e^{log x} ≤ x` and `log x ≤ ⌈log₂ x⌉ log 2`, for `2 ≤ x`. -/
theorem sizes (x : ℕ) (hx : 2 ≤ x) :
    0 < Real.log x ∧ Real.exp (Real.log x) ≤ x
      ∧ Real.log x ≤ (Nat.clog 2 x : ℝ) * Real.log 2 := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have h := (Cvs.Approximant.DeepIndexSpineSpan.sizes_PR (x := x) (by omega)).2
  rw [show 1 / (2 * π / (2 * π * x)) = (x : ℝ) by field_simp] at h
  exact ⟨Real.log_pos (by exact_mod_cast (show 1 < x by omega)), (Real.exp_log hx0).le, h⟩

end Cvs.Approximant.SpineSubspace
