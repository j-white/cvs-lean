import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.DirectMethodBottomAttained
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.WeilPositivityStatement

/-!
# Evenness survives L² limits, and the even-sector minimiser

    F k even, F k → g in L²   ⟹   g is even almost everywhere

The reflection `x ↦ L − x` preserves Lebesgue measure, so `g` and `g (L − ·)` are limits of
the same sequence and agree as classes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.EvennessSurvivesL2Limit

/-- The `L²` distance between two classes. -/
theorem norm_toLp_sub_sq_real {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x : ℝ, (f x - g x) ^ 2 := by
  have hsub : (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g := MemLp.toLp_sub hf hg
  rw [← hsub, Cvs.Upstream.CauchySchwarzLine.norm_toLp_sq_real (hf.sub hg)]
  rfl

/-- **`L²` convergence of functions is convergence of their classes.** -/
theorem tendsto_toLp {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hF : ∀ k, MemLp (F k) 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (h : Tendsto (fun k => ∫ x : ℝ, (F k x - g x) ^ 2) atTop (nhds 0)) :
    Tendsto (fun k => (hF k).toLp (F k)) atTop (nhds (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrw : ∀ k, ‖(hF k).toLp (F k) - hg.toLp g‖
      = Real.sqrt (∫ x : ℝ, (F k x - g x) ^ 2) := by
    intro k
    rw [← norm_toLp_sub_sq_real (hF k) hg, Real.sqrt_sq (norm_nonneg _)]
  simp only [hrw]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Real.sqrt_zero, Function.comp_def] using this

/-- The reflection preserves `L²` membership. -/
theorem memLp_reflect {L : ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun x => f (L - x)) 2 (volume : Measure ℝ) :=
  hf.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left L)

/-- The reflection preserves integrals. -/
theorem integral_reflect {L : ℝ} (G : ℝ → ℝ) : (∫ x : ℝ, G (L - x)) = ∫ x : ℝ, G x :=
  ((volume : Measure ℝ).measurePreserving_sub_left L).integral_comp
    (MeasurableEquiv.subLeft L).measurableEmbedding G

/-- **Evenness survives `L²` limits.** -/
theorem even_of_tendsto {L : ℝ} {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hF : ∀ k, MemLp (F k) 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hev : ∀ k, (fun x => F k (L - x)) =ᵐ[(volume : Measure ℝ)] F k)
    (h : Tendsto (fun k => ∫ x : ℝ, (F k x - g x) ^ 2) atTop (nhds 0)) :
    (fun x => g (L - x)) =ᵐ[(volume : Measure ℝ)] g := by
  have hgr : MemLp (fun x => g (L - x)) 2 (volume : Measure ℝ) := memLp_reflect hg
  -- the same sequence also converges to the reflection of `g`
  have h2 : Tendsto (fun k => ∫ x : ℝ, (F k x - g (L - x)) ^ 2) atTop (nhds 0) := by
    have heq : ∀ k, (∫ x : ℝ, (F k x - g (L - x)) ^ 2) = ∫ x : ℝ, (F k x - g x) ^ 2 := by
      intro k
      have hstep : (∫ x : ℝ, (F k x - g (L - x)) ^ 2)
          = ∫ x : ℝ, (F k (L - x) - g (L - x)) ^ 2 := by
        refine integral_congr_ae ((hev k).mono fun x hx => ?_)
        simp only at hx ⊢
        rw [hx]
      rw [hstep, integral_reflect (fun y => (F k y - g y) ^ 2)]
    simpa [heq] using h
  -- two limits of one sequence
  have hlim1 := tendsto_toLp hF hg h
  have hlim2 := tendsto_toLp hF hgr h2
  have := tendsto_nhds_unique hlim1 hlim2
  exact (MemLp.toLp_eq_toLp_iff hg hgr).mp this |>.symm

/-- **The bottom of the even sector is attained.** -/
theorem exists_even_minimiser {D : Set (ℝ → ℝ)} (P R : ℕ) {L lam : ℝ}
    (hmemD : ∀ f ∈ D, MemLp f 2 (volume : Measure ℝ))
    (hsuppD : ∀ f ∈ D, ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hcontD : ∀ f ∈ D, AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ))
    (hintD : ∀ f ∈ D, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0)
      (volume : Measure ℝ))
    (hnormD : ∀ f ∈ D, (∫ x : ℝ, f x ^ 2) = 1)
    (hlam : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R ''
      {f | f ∈ D ∧ (fun x => f (L - x)) =ᵐ[(volume : Measure ℝ)] f}) lam)
    (hcpt : ∀ (F : ℕ → ℝ → ℝ) (B : ℝ), (∀ n, F n ∈ D) →
      (∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ B) →
      ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ g ∈ D ∧
        Tendsto (fun k => ∫ x : ℝ, (F (φ k) x - g x) ^ 2) atTop (nhds 0)) :
    ∃ g ∈ {f | f ∈ D ∧ (fun x => f (L - x)) =ᵐ[(volume : Measure ℝ)] f},
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam := by
  set Dev : Set (ℝ → ℝ) := {f | f ∈ D ∧ (fun x => f (L - x)) =ᵐ[(volume : Measure ℝ)] f}
    with hDev
  refine Cvs.WeilForm.DirectMethodBottomAttained.exists_minimiser (D := Dev) P R
    (fun f hf => hmemD f hf.1) (fun f hf => hsuppD f hf.1) (fun f hf => hcontD f hf.1)
    (fun f hf => hintD f hf.1) (fun f hf => hnormD f hf.1) hlam ?_
  intro F B hFD hFB
  obtain ⟨φ, g, hφ, hgD, htend⟩ := hcpt F B (fun n => (hFD n).1) hFB
  refine ⟨φ, g, hφ, ⟨hgD, ?_⟩, htend⟩
  exact even_of_tendsto (fun k => hmemD _ (hFD (φ k)).1) (hmemD g hgD)
    (fun k => (hFD (φ k)).2) htend

end Cvs.WeilForm.EvennessSurvivesL2Limit
