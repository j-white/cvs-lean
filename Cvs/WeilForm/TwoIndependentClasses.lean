import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.HatLevyDeficit
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.HatFunctionWindow
import Cvs.WeilForm.HatInFormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The form domain has two independent classes, so every class has a nonzero orthogonal

    `hatSmallD ≠ c • hatD` for every `c`,   and   `∀ η, ∃ w ≠ 0, ⟪η, w⟫ = 0`

for `0 < L`: the hat of half width sits in the domain too, and two hats of different widths are
not proportional.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.TwoIndependentClasses

/-- **The half-width hat, as a class in the window of width `L`.** -/
def hatSmallW (L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(Cvs.WeilForm.HatFunctionWindow.memLp_hat (L / 2)).toLp _, by
    show ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (0:ℝ) L →
      ((Cvs.WeilForm.HatFunctionWindow.memLp_hat (L / 2)).toLp _ : ℝ → ℝ) x = 0
    filter_upwards [(Cvs.WeilForm.HatFunctionWindow.memLp_hat (L / 2)).coeFn_toLp] with x hx hxL
    rw [hx]
    refine Cvs.WeilForm.HatFunctionWindow.hat_eq_zero_of_notMem (L / 2) fun h => hxL ⟨h.1, ?_⟩
    linarith [h.1, h.2]⟩

theorem hatSmallW_ae (L : ℝ) :
    ((hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] Cvs.WeilForm.HatFunctionWindow.hat (L / 2) :=
  (Cvs.WeilForm.HatFunctionWindow.memLp_hat (L / 2)).coeFn_toLp

theorem rep_hatSmallW_ae {L : ℝ} (hL : 0 ≤ L) :
    Cvs.WeilForm.WindowRepresentative.rep (hatSmallW L) =ᵐ[volume] Cvs.WeilForm.HatFunctionWindow.hat (L / 2) := by
  filter_upwards [hatSmallW_ae L] with x hx
  show (Ioc (0:ℝ) L).indicator (Cvs.WeilForm.WindowRepresentative.fn (hatSmallW L)) x = _
  rw [Set.indicator_apply]
  split_ifs with h
  · exact hx
  · symm
    refine Cvs.WeilForm.HatFunctionWindow.hat_eq_zero_of_notMem (L / 2) fun h' => h ⟨h'.1, ?_⟩
    linarith [h'.2]

/-- Its self-convolution is that of the small hat. -/
theorem selfConvolution_rep_hatSmallW {L : ℝ} (hL : 0 ≤ L) (v : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (hatSmallW L)) v
      = selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat (L / 2)) v := by
  unfold selfConvolution
  refine integral_congr_ae ?_
  have h1 := rep_hatSmallW_ae hL
  have h2 := (measurePreserving_add_right volume v).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with s hs1 hs2
  rw [hs1]
  exact congrArg _ hs2

/-- **The half-width hat lies in the form domain.** -/
theorem hatSmallW_mem_formDomain {L : ℝ} (hL : 0 < L) :
    hatSmallW L ∈ Cvs.WeilForm.FormDomain.formDomain hL.le := by
  show IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (hatSmallW L))) _ _
  have h1 : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (hatSmallW L))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.HatFunctionWindow.hat (L / 2)) := by
    funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [selfConvolution_rep_hatSmallW hL.le, selfConvolution_rep_hatSmallW hL.le]
  have h2 : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.HatFunctionWindow.hatW (L / 2)))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.HatFunctionWindow.hat (L / 2)) := by
    funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [Cvs.WeilForm.Archimedean.HatLevyDeficit.selfConvolution_rep_hatW, Cvs.WeilForm.Archimedean.HatLevyDeficit.selfConvolution_rep_hatW]
  rw [h1, ← h2]
  exact Cvs.WeilForm.HatInFormDomain.integrableOn_levy_hat (by linarith)

def hatSmallD {L : ℝ} (hL : 0 < L) : Cvs.WeilForm.FormDomain.formDomain hL.le :=
  ⟨hatSmallW L, hatSmallW_mem_formDomain hL⟩

/-- **The two hats are not proportional.** -/
theorem hatSmallD_ne_smul {L : ℝ} (hL : 0 < L) (c : ℝ) :
    hatSmallD hL ≠ c • Cvs.WeilForm.HatInFormDomain.hatD hL := by
  intro h
  have hLp : ((hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      = c • ((Cvs.WeilForm.HatFunctionWindow.hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
        Lp ℝ 2 (volume : Measure ℝ)) := by
    have := congrArg (fun φ : Cvs.WeilForm.FormDomain.formDomain hL.le =>
      ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) h
    simp only [Submodule.coe_smul] at this
    exact this
  have hae : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) =ᵐ[volume] fun x => c * Cvs.WeilForm.HatFunctionWindow.hat L x := by
    have h1 := hatSmallW_ae L
    have h2 := Cvs.WeilForm.HatFunctionWindow.hatW_ae L
    have h3 := Lp.coeFn_smul c ((Cvs.WeilForm.HatFunctionWindow.hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
      Lp ℝ 2 (volume : Measure ℝ))
    rw [hLp] at h1
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [← hx1, hx3, Pi.smul_apply, hx2, smul_eq_mul]
  have heq : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) = fun x => c * Cvs.WeilForm.HatFunctionWindow.hat L x :=
    (Continuous.ae_eq_iff_eq (volume : Measure ℝ) (Cvs.WeilForm.HatFunctionWindow.continuous_hat _)
      (continuous_const.mul (Cvs.WeilForm.HatFunctionWindow.continuous_hat L))).mp hae
  -- at `L/2` the small hat vanishes and the large one is `L/2`, so `c = 0`
  have hmid := congrFun heq (L / 2)
  have hsmall : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L / 2) = 0 := by
    unfold Cvs.WeilForm.HatFunctionWindow.hat
    rw [sub_self, min_eq_right (by linarith), max_self]
  rw [hsmall, Cvs.WeilForm.HatFunctionWindow.hat_half hL.le] at hmid
  have hc : c = 0 := by
    have : c * (L / 2) = 0 := hmid.symm
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  -- but then the small hat vanishes at its own midpoint, where it is `L/4`
  have hq := congrFun heq (L / 4)
  rw [hc, zero_mul] at hq
  have : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L / 4) = L / 4 := by
    have := Cvs.WeilForm.HatFunctionWindow.hat_half (show (0:ℝ) ≤ L / 2 by linarith)
    rwa [show L / 2 / 2 = L / 4 by ring] at this
  linarith

/-- The inner product on the domain is the ambient one. -/
theorem inner_coe {L : ℝ} (hL : 0 ≤ L) (x y : Cvs.WeilForm.FormDomain.formDomain hL) :
    (inner ℝ x y : ℝ) = inner ℝ ((x : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) := rfl

/-- **Every class in the domain has a nonzero orthogonal class.** -/
theorem exists_perp_ne_zero {L : ℝ} (hL : 0 < L) (η : Cvs.WeilForm.FormDomain.formDomain hL.le) :
    ∃ w : Cvs.WeilForm.FormDomain.formDomain hL.le, w ≠ 0 ∧ (inner ℝ η w : ℝ) = 0 := by
  by_cases hη : η = 0
  · refine ⟨Cvs.WeilForm.HatInFormDomain.hatD hL, Cvs.WeilForm.HatInFormDomain.hatD_ne_zero hL, ?_⟩
    rw [hη, inner_coe, Submodule.coe_zero, Submodule.coe_zero, inner_zero_left]
  -- one of the two hats is not a multiple of `η`
  have hpick : ∃ h : Cvs.WeilForm.FormDomain.formDomain hL.le, ∀ c : ℝ, h ≠ c • η := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c₁, hc₁⟩ := hcon (Cvs.WeilForm.HatInFormDomain.hatD hL)
    obtain ⟨c₂, hc₂⟩ := hcon (hatSmallD hL)
    have hc₁0 : c₁ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc₁
      exact Cvs.WeilForm.HatInFormDomain.hatD_ne_zero hL hc₁
    apply hatSmallD_ne_smul hL (c₂ / c₁)
    rw [hc₂, hc₁, smul_smul, div_mul_cancel₀ _ hc₁0]
  obtain ⟨h, hh⟩ := hpick
  have hn : ‖η‖ ≠ 0 := by simpa using hη
  refine ⟨h - ((inner ℝ η h : ℝ) / ‖η‖ ^ 2) • η, ?_, ?_⟩
  · intro h0
    apply hh ((inner ℝ η h : ℝ) / ‖η‖ ^ 2)
    exact sub_eq_zero.mp h0
  · rw [inner_coe, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ← inner_coe]
    have hnorm : ‖((η : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = ‖η‖ := rfl
    rw [hnorm]
    field_simp
    ring

end Cvs.WeilForm.TwoIndependentClasses
