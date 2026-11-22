import Mathlib
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.ParallelogramLaw
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# From step (a) on the form domain to mode sums converging to the minimiser

The older even-window-set language and the form-domain language are translated into each other,
step (a) yields the infimum and uniqueness statements of `Cvs.Limit.TerminalApproximantsExist` and `Cvs.WeilForm.MinimisingSequenceConverges`, and cosine mode sums
converge in `L²` to the normalised minimiser.
-/

noncomputable section

open MeasureTheory Set Filter Topology Cvs.Zeta.Explicit.Weil

namespace Cvs.Limit.ModeSumsToMinimiser

variable {L : ℝ} {f : ℝ → ℝ}

/-- A window-set function as a window class. -/
def toWindow (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(hf.1).toLp f, by
    filter_upwards [(hf.1).coeFn_toLp] with x hx hxn
    rw [hx]; exact hf.2.1 x hxn⟩

theorem rep_toWindow_ae (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    Cvs.WeilForm.WindowRepresentative.rep (toWindow hf) =ᵐ[volume] f :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep (toWindow hf)).symm.trans (hf.1).coeFn_toLp

/-- **The self-convolution of a scaled function.** -/
theorem selfConvolution_const_mul (c : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    selfConvolution (fun x => c * g x) u = c ^ 2 * selfConvolution g u := by
  unfold selfConvolution
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-- A window-set function lies in the form domain. -/
def toDomain (hL : 0 ≤ L) (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    Cvs.WeilForm.FormDomain.formDomain hL :=
  ⟨toWindow hf, by
    show IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (toWindow hf)))
      (Set.Ioi 0) volume
    have h : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (toWindow hf))
        = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f := by
      funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
      rw [Cvs.WeilForm.ParallelogramLaw.selfConvolution_congr_ae (rep_toWindow_ae hf),
        Cvs.WeilForm.ParallelogramLaw.selfConvolution_congr_ae (rep_toWindow_ae hf)]
    rw [h]; exact hf.2.2.2⟩

theorem Q_toDomain (hL : 0 ≤ L) (P R : ℕ) (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (toDomain hL hf) = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f :=
  Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep (toWindow hf)).trans
    (rep_toWindow_ae hf))

theorem norm_toDomain (hL : 0 ≤ L) (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    ‖toDomain hL hf‖ = 1 := by
  have h2 : ‖toDomain hL hf‖ ^ 2 = 1 := by
    show ‖toWindow hf‖ ^ 2 = 1
    rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
    calc (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (toWindow hf) x ^ 2) = ∫ x : ℝ, f x ^ 2 := by
          apply integral_congr_ae
          filter_upwards [rep_toWindow_ae hf] with x hx
          rw [hx]
      _ = 1 := hf.2.2.1
  have := norm_nonneg (toDomain hL hf)
  nlinarith

theorem reflD_toDomain (hL : 0 ≤ L) (hf : f ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (toDomain hL hf.1) = toDomain hL hf.1 := by
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (toWindow hf.1)
  have h2 := (MeasureTheory.Measure.measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
    (rep_toWindow_ae hf.1)
  have h3 : (fun x => f (L - x)) =ᵐ[volume] f := hf.2
  calc ⇑((Cvs.WeilForm.WindowReflectionSymmetry.reflW (toWindow hf.1) : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (toWindow hf.1)) :=
        Cvs.WeilForm.WindowRepresentative.ae_eq_rep _
    _ =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep (toWindow hf.1) (L - x) := h1
    _ =ᵐ[volume] fun x => f (L - x) := h2
    _ =ᵐ[volume] f := h3
    _ =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep (toWindow hf.1) := (rep_toWindow_ae hf.1).symm
    _ =ᵐ[volume] ⇑((toWindow hf.1 : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) :=
        (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm

/-- The normalised representative of a class. -/
def normRep {hL : 0 ≤ L} (η : Cvs.WeilForm.FormDomain.formDomain hL) : ℝ → ℝ :=
  fun x => (1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x

/-- **The normalised minimiser lies in the even window set.** -/
theorem normRep_mem_evenWindowSet (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL)
    (hne : η ≠ 0) (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL η = η) :
    normRep η ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L := by
  have hn : 0 < ‖η‖ := by simpa using hne
  have hn2 : ‖η‖ ^ 2 = ∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x ^ 2 :=
    Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show MemLp (fun x => (1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x)
      2 volume
    exact (Cvs.WeilForm.WindowRepresentative.memLp_rep _).const_mul _
  · intro s hs
    show (1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) s = 0
    rw [Cvs.WeilForm.WindowRepresentative.rep_supp _ s hs, mul_zero]
  · show (∫ x : ℝ, ((1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x) ^ 2) = 1
    simp_rw [mul_pow]
    rw [integral_const_mul, ← hn2]
    field_simp
  · have h : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (normRep η)
        = fun u => (1 / ‖η‖) ^ 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
            (Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)) u := by
      funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy normRep
      rw [selfConvolution_const_mul, selfConvolution_const_mul]; ring
    rw [h]; exact η.2.const_mul _
  · have hrw : Cvs.WeilForm.WindowReflectionSymmetry.reflW (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        = (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) := congrArg Subtype.val heven
    have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    rw [hrw] at h1
    filter_upwards [h1] with x hx
    simp only [normRep]
    rw [← hx]

/-- **Step (a) gives the infimum over the even window set.** -/
theorem isGLB_of_stepA (hL : 0 < L) (P R : ℕ) {lam : ℝ} {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η) :
    IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R '' Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam := by
  have hn : 0 < ‖η‖ := by simpa using h.nonzero
  -- the value at the normalised minimiser
  have hval : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (normRep η) = lam := by
    have hsm : Cvs.WeilForm.WindowRepresentative.rep ((1 / ‖η‖) • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        =ᵐ[volume] normRep η := by
      show _ =ᵐ[volume] fun x => (1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x
      exact Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae _ _
    have := Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (P := P) (R := R)
      ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep ((1 / ‖η‖) • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L))).trans hsm)
    rw [← this]
    show Cvs.WeilForm.WindowRepresentative.weilQW P R ((1 / ‖η‖) • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = lam
    rw [Cvs.WeilForm.BottomAttained.weilQW_smul]
    have hatt : Cvs.WeilForm.WindowRepresentative.weilQW P R (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        = lam * ‖η‖ ^ 2 := h.attains
    rw [hatt]; field_simp
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    have this : lam * ‖toDomain hL.le hg.1‖ ^ 2
        ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R (toDomain hL.le hg.1) := h.bottom _
    rw [Q_toDomain hL.le P R hg.1, norm_toDomain hL.le hg.1] at this
    simpa using this
  · intro b hb
    exact hb ⟨normRep η, normRep_mem_evenWindowSet hL.le η h.nonzero h.even, hval⟩

/-- **Step (a) gives uniqueness up to sign on the even window set.** -/
theorem unique_of_stepA (hL : 0 < L) (P R : ℕ) {lam : ℝ} {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η) :
    ∀ g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L,
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam →
        g =ᵐ[volume] normRep η ∨ g =ᵐ[volume] (fun x => -normRep η x) := by
  intro g hg hval
  have hn : 0 < ‖η‖ := by simpa using h.nonzero
  have hmin : Cvs.WeilForm.WindowRepresentative.weilQW P R ((toDomain hL.le hg.1 : Cvs.WeilForm.FormDomain.formDomain hL.le)
      : Cvs.WeilForm.WeilFormOnWindowL2.window L) = lam * ‖toDomain hL.le hg.1‖ ^ 2 := by
    rw [norm_toDomain hL.le hg.1]
    have := Q_toDomain hL.le P R hg.1
    simp only [Cvs.WeilForm.InfimumAttainedSphere.Q] at this
    rw [this, hval]; ring
  obtain ⟨c, hc⟩ := h.simple _ hmin
  have hnorm : (1:ℝ) = |c| * ‖η‖ := by
    have h1 := norm_toDomain hL.le hg.1
    rw [hc] at h1
    have h2 : ‖c • η‖ = |c| * ‖η‖ := by
      calc ‖c • η‖ = ‖(((c • η : Cvs.WeilForm.FormDomain.formDomain hL.le)
              : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ := rfl
        _ = ‖c • ((η : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ := by
            rw [Submodule.coe_smul, Submodule.coe_smul]
        _ = |c| * ‖η‖ := by rw [norm_smul, Real.norm_eq_abs]; rfl
    rw [h2] at h1; exact h1.symm
  have hrep : g =ᵐ[volume] fun x => c * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x := by
    have h1 := rep_toWindow_ae hg.1
    have h2 : Cvs.WeilForm.WindowRepresentative.rep (toWindow hg.1)
        = Cvs.WeilForm.WindowRepresentative.rep ((toDomain hL.le hg.1 : Cvs.WeilForm.FormDomain.formDomain hL.le)
            : Cvs.WeilForm.WeilFormOnWindowL2.window L) := rfl
    have h3 := Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae c (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    have h4 : ((toDomain hL.le hg.1 : Cvs.WeilForm.FormDomain.formDomain hL.le)
        : Cvs.WeilForm.WeilFormOnWindowL2.window L) = c • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
      rw [hc]; rfl
    rw [h2, h4] at h1
    exact h1.symm.trans h3
  have hc' : |c| = 1 / ‖η‖ := by
    rw [eq_div_iff hn.ne']; linarith
  rcases (abs_eq (by positivity : (0:ℝ) ≤ 1 / ‖η‖)).mp hc' with hc1 | hc1
  · left
    filter_upwards [hrep] with x hx
    rw [hx, hc1]
    show _ = (1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x
    rfl
  · right
    filter_upwards [hrep] with x hx
    rw [hx, hc1]
    show _ = -((1 / ‖η‖) * Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x)
    ring

end Cvs.Limit.ModeSumsToMinimiser
