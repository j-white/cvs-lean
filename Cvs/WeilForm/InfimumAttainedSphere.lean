import Mathlib
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.FormLscDomainClosed
import Cvs.WeilForm.MinimisationPrincipleLsc
import Cvs.WeilForm.SublevelSetTotallyBounded
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowClosedL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative

/-!
# The Weil form attains its infimum on the unit sphere of the form domain

    `∃ η`, `‖η‖ = 1`, `weilQW η = inf {weilQW φ | ‖φ‖ = 1}`

given one nonzero class in the domain: sublevel sets are sequentially compact, the form is
lower semicontinuous, and the domain closes under bounded limits.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Cvs.WeilForm.InfimumAttainedSphere

/-- The unit sphere of the form domain. -/
def sphere {L : ℝ} (hL : 0 ≤ L) : Set (Cvs.WeilForm.FormDomain.formDomain hL) := {φ | ‖φ‖ = 1}

/-- The form on the domain. -/
abbrev Q {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) : ℝ :=
  Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)

/-- **The sphere is nonempty** once the domain has a nonzero class. -/
theorem sphere_nonempty {L : ℝ} (hL : 0 ≤ L)
    (hne : ∃ φ : Cvs.WeilForm.FormDomain.formDomain hL, φ ≠ 0) : (sphere hL).Nonempty := by
  obtain ⟨φ, hφ⟩ := hne
  have hn : ‖((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by
      intro h
      apply hφ
      exact Subtype.ext (Subtype.ext h))
  refine ⟨(‖φ‖⁻¹) • φ, ?_⟩
  show ‖((((‖φ‖⁻¹) • φ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Lp ℝ 2 (volume : Measure ℝ))‖ = 1
  rw [Submodule.coe_smul, Submodule.coe_smul, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg φ)]
  exact inv_mul_cancel₀ hn

/-- **The form is bounded below on the sphere.** -/
theorem floor_le_Q {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : φ ∈ sphere hL) : Cvs.WeilForm.WindowFormNormFloor.floorConst L P R ≤ Q hL P R φ := by
  have h := Cvs.WeilForm.FormDomain.weilQW_ge_floor hL P R φ
  have hn : ‖φ‖ = 1 := hφ
  rw [hn, one_pow, mul_one] at h
  exact h

/-- **Bounded-form sequences on the sphere have convergent subsequences with limit on the
sphere.** -/
theorem exists_subseq {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ)
    (x : ℕ → Cvs.WeilForm.FormDomain.formDomain hL) (hxS : ∀ n, x n ∈ sphere hL)
    (hxQ : ∀ n, Q hL P R (x n) ≤ c) :
    ∃ (σ : ℕ → ℕ) (y : Cvs.WeilForm.FormDomain.formDomain hL), StrictMono σ ∧ y ∈ sphere hL ∧
      Tendsto (fun k => ‖x (σ k) - y‖) atTop (𝓝 0) := by
  obtain ⟨σ, hσ, y₀, hy₀⟩ := Cvs.WeilForm.SublevelSetTotallyBounded.exists_subseq_tendsto hL P R c x
    fun n => ⟨(hxS n).le, hxQ n⟩
  obtain ⟨hyw, _⟩ := Cvs.WeilForm.WindowClosedL2.tendsto_window (x := fun k => (x (σ k) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L)) hy₀
  obtain ⟨hmem, _⟩ := Cvs.WeilForm.FormLscDomainClosed.lsc hL P R (fun k => x (σ k)) (fun k => hxQ (σ k))
    (y := ⟨y₀, hyw⟩) hy₀
  refine ⟨σ, ⟨⟨y₀, hyw⟩, hmem⟩, hσ, ?_, ?_⟩
  · -- the norm passes to the limit
    show ‖y₀‖ = 1
    have h1 : Tendsto (fun k => ‖(((x (σ k) : Cvs.WeilForm.FormDomain.formDomain hL) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖) atTop (𝓝 ‖y₀‖) :=
      hy₀.norm
    have h2 : Tendsto (fun k => ‖(((x (σ k) : Cvs.WeilForm.FormDomain.formDomain hL) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖) atTop (𝓝 1) := by
      have : ∀ k, ‖(((x (σ k) : Cvs.WeilForm.FormDomain.formDomain hL) :
          Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = 1 := fun k => hxS (σ k)
      simp only [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · have h := tendsto_iff_norm_sub_tendsto_zero.mp hy₀
    refine h.congr fun k => ?_
    rfl

/-- **The form is lower semicontinuous on the sphere.** -/
theorem lsc_sphere {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (x : ℕ → Cvs.WeilForm.FormDomain.formDomain hL) (y : Cvs.WeilForm.FormDomain.formDomain hL)
    (hconv : Tendsto (fun k => ‖x k - y‖) atTop (𝓝 0)) (c : ℝ) (hxQ : ∀ k, Q hL P R (x k) ≤ c) :
    Q hL P R y ≤ c := by
  have hx : Tendsto (fun k => (((x k : Cvs.WeilForm.FormDomain.formDomain hL) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) atTop
      (𝓝 (((y : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
        Lp ℝ 2 (volume : Measure ℝ))) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hconv
  exact (Cvs.WeilForm.FormLscDomainClosed.lsc hL P R x hxQ hx).2

/-- **The form attains its infimum on the sphere.** -/
theorem exists_min {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (hne : ∃ φ : Cvs.WeilForm.FormDomain.formDomain hL, φ ≠ 0) :
    ∃ η ∈ sphere hL, Q hL P R η = sInf (Q hL P R '' sphere hL) := by
  have hS := sphere_nonempty hL hne
  have hbdd : BddBelow (Q hL P R '' sphere hL) :=
    ⟨Cvs.WeilForm.WindowFormNormFloor.floorConst L P R, by rintro _ ⟨φ, hφ, rfl⟩; exact floor_le_Q hL P R hφ⟩
  refine Cvs.WeilForm.MinimisationPrincipleLsc.exists_min_of_lsc hS ?_ ?_ ?_ ?_
  · intro v hv
    exact csInf_le hbdd ⟨v, hv, rfl⟩
  · intro ε hε
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hS.image _)
      (show sInf (Q hL P R '' sphere hL) < sInf (Q hL P R '' sphere hL) + ε by linarith)
    exact ⟨v, hv, hlt⟩
  · intro c x hxS hxQ
    exact exists_subseq hL P R c x hxS hxQ
  · intro x y _ _ hconv c hxQ
    exact lsc_sphere hL P R x y hconv c hxQ

end Cvs.WeilForm.InfimumAttainedSphere
