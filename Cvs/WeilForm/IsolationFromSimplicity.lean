import Mathlib
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MinimisationPrincipleLsc
import Cvs.WeilForm.TwoIndependentClasses
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-!
# Isolation follows from simplicity, on the form domain

    bottom attained at `η ≠ 0`, every minimiser a multiple of `η`
        ⟹   `∃ mu > lam, mu ‖v‖² ≤ weilQW v` for every `v ⊥ η`

by minimising the form on the sphere of `η`'s orthogonal complement.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Cvs.WeilForm.IsolationFromSimplicity

/-- The unit sphere of the orthogonal complement of `η`. -/
def perpSphere {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL) :
    Set (Cvs.WeilForm.FormDomain.formDomain hL) :=
  {v | ‖v‖ = 1 ∧ (inner ℝ η v : ℝ) = 0}

/-- **It is nonempty.** -/
theorem perpSphere_nonempty {L : ℝ} (hL : 0 < L) (η : Cvs.WeilForm.FormDomain.formDomain hL.le) :
    (perpSphere hL.le η).Nonempty := by
  obtain ⟨w, hw0, hw⟩ := Cvs.WeilForm.TwoIndependentClasses.exists_perp_ne_zero hL η
  have hn : ‖((w : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ≠ 0 :=
    (by simpa using hw0 : ‖w‖ ≠ 0)
  refine ⟨(‖w‖⁻¹) • w, ?_, ?_⟩
  · show ‖((((‖w‖⁻¹) • w : Cvs.WeilForm.FormDomain.formDomain hL.le) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = 1
    rw [Submodule.coe_smul, Submodule.coe_smul, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg w)]
    exact inv_mul_cancel₀ hn
  · rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_smul, Submodule.coe_smul, inner_smul_right,
      ← Cvs.WeilForm.TwoIndependentClasses.inner_coe, hw, mul_zero]

/-- **Bounded-form sequences on it converge along subsequences, with the limit on it.** -/
theorem exists_subseq {L : ℝ} (hL : 0 < L) (P R : ℕ) (η : Cvs.WeilForm.FormDomain.formDomain hL.le)
    (c : ℝ) (x : ℕ → Cvs.WeilForm.FormDomain.formDomain hL.le) (hxS : ∀ n, x n ∈ perpSphere hL.le η)
    (hxQ : ∀ n, Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R (x n) ≤ c) :
    ∃ (σ : ℕ → ℕ) (y : Cvs.WeilForm.FormDomain.formDomain hL.le), StrictMono σ ∧
      y ∈ perpSphere hL.le η ∧ Tendsto (fun k => ‖x (σ k) - y‖) atTop (𝓝 0) := by
  obtain ⟨σ, y, hσ, hyS, hconv⟩ := Cvs.WeilForm.InfimumAttainedSphere.exists_subseq hL.le P R c x
    (fun n => (hxS n).1) hxQ
  refine ⟨σ, y, hσ, ⟨hyS, ?_⟩, hconv⟩
  have hx : Tendsto (fun k => x (σ k)) atTop (𝓝 y) := (tendsto_iff_norm_sub_tendsto_zero (E := Cvs.WeilForm.FormDomain.formDomain hL.le)).mpr hconv
  have h1 : Tendsto (fun k => (inner ℝ η (x (σ k)) : ℝ)) atTop (𝓝 (inner ℝ η y)) :=
    tendsto_const_nhds.inner hx
  have h2 : Tendsto (fun k => (inner ℝ η (x (σ k)) : ℝ)) atTop (𝓝 0) := by
    have : ∀ k, (inner ℝ η (x (σ k)) : ℝ) = 0 := fun k => (hxS (σ k)).2
    simp only [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-- **The form attains its infimum on the orthogonal sphere.** -/
theorem exists_min_perp {L : ℝ} (hL : 0 < L) (P R : ℕ) (η : Cvs.WeilForm.FormDomain.formDomain hL.le)
    {lam : ℝ} (hbot : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
      lam * ‖v‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v) :
    ∃ η' ∈ perpSphere hL.le η,
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η' = sInf (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' perpSphere hL.le η) := by
  have hS := perpSphere_nonempty hL η
  have hbdd : BddBelow (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' perpSphere hL.le η) :=
    ⟨lam, by rintro _ ⟨v, hv, rfl⟩; have := hbot v; rw [hv.1, one_pow, mul_one] at this; exact this⟩
  refine Cvs.WeilForm.MinimisationPrincipleLsc.exists_min_of_lsc hS ?_ ?_ ?_ ?_
  · intro v hv; exact csInf_le hbdd ⟨v, hv, rfl⟩
  · intro ε hε
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hS.image _)
      (show sInf (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' perpSphere hL.le η)
        < sInf (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' perpSphere hL.le η) + ε by linarith)
    exact ⟨v, hv, hlt⟩
  · intro c x hxS hxQ; exact exists_subseq hL P R η c x hxS hxQ
  · intro x y _ _ hconv c hxQ; exact Cvs.WeilForm.InfimumAttainedSphere.lsc_sphere hL.le P R x y hconv c hxQ

/-- **Isolation from simplicity.** -/
theorem isolated_of_simple {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (hbot : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
      lam * ‖v‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v)
    (hne : η ≠ 0)
    (hsimple : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v = lam * ‖v‖ ^ 2 → ∃ c : ℝ, v = c • η) :
    ∃ mu : ℝ, lam < mu ∧ ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
      (inner ℝ η v : ℝ) = 0 → mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v := by
  obtain ⟨η', hη', hQ⟩ := exists_min_perp hL P R η hbot
  set mu := sInf (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' perpSphere hL.le η) with hmu
  have hbdd : BddBelow (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' perpSphere hL.le η) :=
    ⟨lam, by rintro _ ⟨v, hv, rfl⟩; have := hbot v; rw [hv.1, one_pow, mul_one] at this; exact this⟩
  -- `mu ≥ lam`, and `mu ≠ lam`
  have hge : lam ≤ mu := by
    have := hbot η'; rw [hη'.1, one_pow, mul_one, hQ] at this; exact this
  have hne' : mu ≠ lam := by
    intro heq
    have hmin : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η' = lam * ‖η'‖ ^ 2 := by
      rw [hQ, heq, hη'.1, one_pow, mul_one]
    obtain ⟨c, hc⟩ := hsimple η' hmin
    have hinner : (inner ℝ η η' : ℝ) = c * ‖η‖ ^ 2 := by
      rw [hc, Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_smul, Submodule.coe_smul,
        inner_smul_right, real_inner_self_eq_norm_sq]
      rfl
    rw [hη'.2] at hinner
    have hn : ‖η‖ ≠ 0 := by simpa using hne
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hinner.symm with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hn
    have : ‖η'‖ = 0 := by rw [hc, hc0, zero_smul, Cvs.WeilForm.BottomAttained.norm_zero' hL]
    rw [hη'.1] at this
    exact one_ne_zero this
  refine ⟨mu, lt_of_le_of_ne hge (Ne.symm hne'), fun v hv => ?_⟩
  by_cases hv0 : v = 0
  · subst hv0
    rw [Cvs.WeilForm.BottomAttained.norm_zero' hL, zero_pow two_ne_zero, mul_zero]
    show 0 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R ((0 : Cvs.WeilForm.FormDomain.formDomain hL.le) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L)
    rw [Submodule.coe_zero, Cvs.WeilForm.BottomAttained.weilQW_zero]
  · have hn : ‖((v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ≠ 0 :=
      (by simpa using hv0 : ‖v‖ ≠ 0)
    have hw : (‖v‖⁻¹ • v) ∈ perpSphere hL.le η := by
      refine ⟨?_, ?_⟩
      · show ‖((((‖v‖⁻¹) • v : Cvs.WeilForm.FormDomain.formDomain hL.le) :
          Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = 1
        rw [Submodule.coe_smul, Submodule.coe_smul, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg v)]
        exact inv_mul_cancel₀ hn
      · rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_smul, Submodule.coe_smul,
          inner_smul_right, ← Cvs.WeilForm.TwoIndependentClasses.inner_coe, hv, mul_zero]
    have hQw : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R (‖v‖⁻¹ • v)
        = ‖v‖⁻¹ ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v := by
      show Cvs.WeilForm.WindowRepresentative.weilQW P R (((‖v‖⁻¹ • v : Cvs.WeilForm.FormDomain.formDomain hL.le) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L)) = _
      rw [Submodule.coe_smul, Cvs.WeilForm.BottomAttained.weilQW_smul]
    have hmu' : mu ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R (‖v‖⁻¹ • v) := csInf_le hbdd ⟨_, hw, rfl⟩
    rw [hQw] at hmu'
    have hne2 : ‖v‖ ≠ 0 := by simpa using hv0
    have hpos : 0 < ‖v‖ ^ 2 := by positivity
    calc mu * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmu' hpos.le
      _ = Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v := by field_simp

end Cvs.WeilForm.IsolationFromSimplicity
