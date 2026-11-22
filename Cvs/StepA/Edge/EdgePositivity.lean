import Mathlib
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.DampedEdgeGram
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.EdgeSpace
import Cvs.StepA.Edge.OneOrdinateDiscriminant
import Cvs.StepA.Edge.VertexChains
import Cvs.StepA.Edge.VertexSignRule
import Cvs.StepA.Edge.WedgeAbove
import Cvs.StepA.Edge.WedgeBelow
import Cvs.Upstream.FlowFirstContact

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Edge positivity of every finite family

On the phase torus with the orbit flow `φᵢ ↦ φᵢ e^{i gᵢ x}`, the edge discriminant of the weights
`mᵢ e^{−gᵢ² y} φᵢ` takes both signs on every nonempty compact flow-invariant set at every heat level
`y` (first contact, Lemma C, the wedges above and below); on the orbit closure of `1` this is edge
positivity of every finite family, hence `EdgeResidue` and the RH criteria of an earlier result without it.
-/

noncomputable section

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
open Cvs.StepA.Edge.EdgeDiscriminant (edgeDisc)
open Cvs.StepA.Edge.DampedEdgeGram (mergeOrd mergeW edgeDisc_merge pos_of_mem_mergeOrd mergeW_pos nonempty_mergeOrd)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The phase torus and the heat weights -/

/-- The orbit flow on the phase torus, `φᵢ ↦ φᵢ e^{i gᵢ x}`. -/
def phaseFlow (g : ι → ℝ) (x : ℝ) (φ : ι → Circle) : ι → Circle :=
  fun i => φ i * Circle.exp (g i * x)

/-- The weights at phases `φ` and heat level `y`: `m_i e^{−gᵢ² y} φᵢ`. -/
def heatWts (m g : ι → ℝ) (y : ℝ) (φ : ι → Circle) : ι → ℂ :=
  fun i => ((m i * Real.exp (-(g i ^ 2 * y)) : ℝ) : ℂ) * (φ i : ℂ)

omit [Fintype ι] [DecidableEq ι] in
/-- The orbit flow is jointly continuous. -/
theorem continuous_phaseFlow (g : ι → ℝ) :
    Continuous fun p : ℝ × (ι → Circle) => phaseFlow g p.1 p.2 :=
  continuous_pi fun i => ((continuous_apply i).comp continuous_snd).mul
    (Circle.exp.continuous.comp (continuous_const.mul continuous_fst))

omit [Fintype ι] [DecidableEq ι] in
/-- The orbit flow is additive. -/
theorem phaseFlow_add (g : ι → ℝ) (a b : ℝ) (φ : ι → Circle) :
    phaseFlow g (a + b) φ = phaseFlow g a (phaseFlow g b φ) := by
  funext i
  simp only [phaseFlow, mul_add, Circle.exp_add]
  ac_rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The orbit flow at time `0` is the identity. -/
theorem phaseFlow_zero (g : ι → ℝ) (φ : ι → Circle) : phaseFlow g 0 φ = φ := by
  funext i
  simp [phaseFlow]

omit [Fintype ι] [DecidableEq ι] in
/-- The heat weights are jointly continuous in the phases and the level. -/
theorem continuous_heatWts (m g : ι → ℝ) :
    Continuous fun p : (ι → Circle) × ℝ => heatWts m g p.2 p.1 := by
  refine continuous_pi fun i => ?_
  simp only [heatWts]
  refine (Complex.continuous_ofReal.comp (continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd).neg))).mul ?_
  exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)

omit [Fintype ι] [DecidableEq ι] in
/-- **Heat and orbit act on the weights by the flow**:
`heatWts (y + y') (phaseFlow x φ) = flow x y' (heatWts y φ)`. -/
theorem heatWts_phaseFlow (m g : ι → ℝ) (y y' x : ℝ) (φ : ι → Circle) :
    heatWts m g (y + y') (phaseFlow g x φ) = flow g x y' (heatWts m g y φ) := by
  funext i
  simp only [heatWts, phaseFlow, flow, Circle.coe_mul, Circle.coe_exp]
  have h1 : Complex.exp (((g i * x : ℝ) : ℂ) * Complex.I - ((g i ^ 2 * y' : ℝ) : ℂ))
      = Complex.exp (((g i * x : ℝ) : ℂ) * Complex.I)
        * Complex.exp (-((g i ^ 2 * y' : ℝ) : ℂ)) := by
    rw [sub_eq_add_neg, Complex.exp_add]
  have h2 : ((m i * Real.exp (-(g i ^ 2 * (y + y'))) : ℝ) : ℂ)
      = ((m i * Real.exp (-(g i ^ 2 * y)) : ℝ) : ℂ) * Complex.exp (-((g i ^ 2 * y' : ℝ) : ℂ)) := by
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [h1, h2]
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The orbit flow alone acts on the weights by the orbit flow. -/
theorem heatWts_phaseFlow_zero (m g : ι → ℝ) (y x : ℝ) (φ : ι → Circle) :
    heatWts m g y (phaseFlow g x φ) = flow g x 0 (heatWts m g y φ) := by
  rw [← heatWts_phaseFlow, add_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- With positive amplitudes every heat weight is nonzero. -/
theorem heatWts_ne_zero {m : ι → ℝ} (hm : ∀ i, 0 < m i) (g : ι → ℝ) (y : ℝ) (φ : ι → Circle)
    (i : ι) : heatWts m g y φ i ≠ 0 := by
  refine mul_ne_zero ?_ (Circle.coe_ne_zero (φ i))
  exact_mod_cast (mul_pos (hm i) (Real.exp_pos _)).ne'

omit [Fintype ι] [DecidableEq ι] in
/-- On the orbit of `1` at level `0` the heat weights are `mᵢ e^{i gᵢ x}`. -/
theorem heatWts_orbit (m g : ι → ℝ) (x : ℝ) :
    heatWts m g 0 (phaseFlow g x 1)
      = fun i => (m i : ℂ) * Complex.exp ((g i * x : ℝ) * Complex.I) := by
  funext i
  simp [heatWts, phaseFlow, Circle.coe_exp]

/-! ### The seed -/

-- merged §3, Lemma Y
/-- **The seed**: on a nonempty flow-invariant set the edge discriminant is
positive somewhere at every large heat level. -/
theorem exists_seed [Nonempty ι] (P : EdgeData ι) {m : ι → ℝ} (hm : ∀ i, 0 < m i)
    {K : Set (ι → Circle)} (hKne : K.Nonempty) (hKinv : ∀ x, ∀ φ ∈ K, phaseFlow P.g x φ ∈ K) :
    ∃ Y₀, ∀ y ≥ Y₀, ∃ φ ∈ K, 0 < edgeDiscZ P.δ P.g (heatWts m P.g y φ) := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ P.g Finset.univ_nonempty
  have hmin : ∀ i ≠ i₀, P.g i₀ < P.g i := fun i hi =>
    lt_of_le_of_ne (hi₀ i (Finset.mem_univ i)) fun h => hi (P.hg h).symm
  obtain ⟨Y₀, hY⟩ := exists_seed_level P.hδ P.hg0 hmin hm
  refine ⟨Y₀, fun y hy => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hKne
  set w : ℂ := (P.δ : ℂ) + (P.g i₀ : ℂ) * Complex.I with hw
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hw] at this
    exact P.hδ.ne' this
  set u : Circle := Circle.exp (Complex.arg w) with hu
  obtain ⟨t, ht⟩ := Circle.exp_surjective ((φ₀ i₀)⁻¹ * u)
  set φ := phaseFlow P.g (t / P.g i₀) φ₀ with hφ
  have hφi : φ i₀ = u := by
    simp only [hφ, phaseFlow, mul_div_cancel₀ t (P.hg0 i₀).ne', ht, mul_inv_cancel_left]
  refine ⟨φ, hKinv _ φ₀ hφ₀, ?_⟩
  have hb := edgeDiscZ_ge_single P.hδ P.g i₀ (heatWts m P.g y φ)
  have hre : (heatWts m P.g y φ i₀ / (2 * w)).re
      = m i₀ * Real.exp (-(P.g i₀ ^ 2 * y)) / (2 * ‖w‖) := by
    have hwu : w = (‖w‖ : ℂ) * (u : ℂ) := by
      rw [hu, Circle.coe_exp]; exact (Complex.norm_mul_exp_arg_mul_I w).symm
    have hu0 : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
    have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hw0).ne'
    have hval : heatWts m P.g y φ i₀ / (2 * w)
        = ((m i₀ * Real.exp (-(P.g i₀ ^ 2 * y)) / (2 * ‖w‖) : ℝ) : ℂ) := by
      simp only [heatWts, hφi]
      conv_lhs => rw [hwu]
      push_cast
      field_simp
    rw [hval, Complex.ofReal_re]
  have hsum : ∑ i ∈ Finset.univ.erase i₀, ‖heatWts m P.g y φ i‖
      = ∑ i ∈ Finset.univ.erase i₀, m i * Real.exp (-(P.g i ^ 2 * y)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [heatWts, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (hm i), abs_of_pos (Real.exp_pos _)]
  rw [hre, hsum] at hb
  have := hY y hy
  linarith

/-! ### First contact (merged §5-§6) -/

-- merged §6, through the first contact of `Cvs.Upstream.FlowFirstContact`
/-- **Positivity on every compact invariant set**: on a nonempty compact
flow-invariant set of phases the edge discriminant at heat level `y` is positive somewhere. -/
theorem exists_pos_of_invariant [Nonempty ι] (P : EdgeData ι) {m : ι → ℝ} (hm : ∀ i, 0 < m i)
    {K : Set (ι → Circle)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKinv : ∀ x, ∀ φ ∈ K, phaseFlow P.g x φ ∈ K) (y : ℝ) :
    ∃ φ ∈ K, 0 < edgeDiscZ P.δ P.g (heatWts m P.g y φ) := by
  have hv : ∀ φ y, edgeDiscZ P.δ P.g (heatWts m P.g y φ) = 0 →
      IsVertex P (heatWts m P.g y φ) := fun φ y h0 => ⟨heatWts_ne_zero hm P.g y φ, h0⟩
  exact exists_pos_of_firstContact (fun x φ => phaseFlow P.g x φ)
    (continuous_phaseFlow P.g) (phaseFlow_add P.g)
    (fun φ y => edgeDiscZ P.δ P.g (heatWts m P.g y φ))
    ((continuous_edgeDiscZ P.hδ P.g).comp (continuous_heatWts m P.g)) hK hKinv
    (fun φ _ => phaseFlow_zero P.g φ)
    (fun φ y => BottomStart P (heatWts m P.g y φ))
    (exists_seed P hm hKne hKinv)
    (fun φ y h0 hle => (hv φ y h0).bottomStart_of_le (by
      obtain ⟨ε, hε, h⟩ := hle
      exact ⟨ε, hε, fun x hx => by rw [← heatWts_phaseFlow_zero]; exact h x hx⟩))
    (fun φ y hb => by
      obtain ⟨r, hr, h⟩ := hb.wedgeAbove
      exact ⟨r, hr, fun x y' hy' hpos hlt => by
        rw [heatWts_phaseFlow]; exact h x y' hy' hpos hlt⟩)
    (fun φ y hb => by
      obtain ⟨lam, hlam, η₀, hη₀, h⟩ := hb.wedgeBelow
      exact ⟨lam, hlam, η₀, hη₀, fun η hη => by
        rw [sub_eq_add_neg, heatWts_phaseFlow]; exact h η hη⟩)
    y

-- merged §7(i)

/-! ### The orbit -/

/-- The orbit closure of `1` on the phase torus. -/
def orbitClosure (g : ι → ℝ) : Set (ι → Circle) := closure (range fun x : ℝ => phaseFlow g x 1)

omit [Fintype ι] [DecidableEq ι] in
theorem isCompact_orbitClosure (g : ι → ℝ) : IsCompact (orbitClosure g) :=
  isClosed_closure.isCompact

omit [Fintype ι] [DecidableEq ι] in
theorem orbitClosure_nonempty (g : ι → ℝ) : (orbitClosure g).Nonempty :=
  ⟨_, subset_closure ⟨0, rfl⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem phaseFlow_mem_orbitClosure (g : ι → ℝ) (x : ℝ) {φ : ι → Circle}
    (hφ : φ ∈ orbitClosure g) : phaseFlow g x φ ∈ orbitClosure g := by
  have hc : Continuous fun ψ : ι → Circle => phaseFlow g x ψ :=
    continuous_pi fun i => (continuous_apply i).mul continuous_const
  refine map_mem_closure (f := fun ψ : ι → Circle => phaseFlow g x ψ) hc hφ ?_
  rintro _ ⟨x', rfl⟩
  exact ⟨x + x', phaseFlow_add g x x' 1⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A continuous function of the phases positive at a point of the orbit closure is positive on
the orbit. -/
theorem exists_orbit_of_closure {f : (ι → Circle) → ℝ} (hf : Continuous f) (g : ι → ℝ)
    {φ : ι → Circle} (hφ : φ ∈ orbitClosure g) (hpos : 0 < f φ) :
    ∃ x : ℝ, 0 < f (phaseFlow g x 1) := by
  obtain ⟨_, hU, x, rfl⟩ := mem_closure_iff.mp hφ {ψ | 0 < f ψ}
    (isOpen_lt continuous_const hf) hpos
  exact ⟨x, hU⟩

-- merged §7(ii)-(iii)
/-- **The orbit form, positive sign**: distinct positive ordinates and
positive weights have a positive edge discriminant at some real scale. -/
theorem exists_edgeDisc_pos [Nonempty ι] (P : EdgeData ι) {m : ι → ℝ} (hm : ∀ i, 0 < m i) :
    ∃ L : ℝ, 0 < edgeDisc Finset.univ m P.g P.δ L := by
  obtain ⟨φ, hφ, hpos⟩ := exists_pos_of_invariant P hm (isCompact_orbitClosure P.g)
    (orbitClosure_nonempty P.g) (fun x _ hφ => phaseFlow_mem_orbitClosure P.g x hφ) 0
  have hc : Continuous fun ψ : ι → Circle => edgeDiscZ P.δ P.g (heatWts m P.g 0 ψ) :=
    (continuous_edgeDiscZ P.hδ P.g).comp (continuous_pi fun i =>
      continuous_const.mul (continuous_subtype_val.comp (continuous_apply i)))
  obtain ⟨L, hL⟩ := exists_orbit_of_closure (f := fun ψ => edgeDiscZ P.δ P.g (heatWts m P.g 0 ψ))
    hc P.g hφ hpos
  refine ⟨L, ?_⟩
  rw [← edgeDiscZ_orbit]
  simpa only [heatWts_orbit] using hL

-- merged §7(vi)

/-! ### Every finite family -/

/-- The data of the merged ordinates of a family with nonzero ordinates at depth `δ > 0`. -/
def mergeData {α : Type*} {s : Finset α} {γ : α → ℝ} (hγ : ∀ i ∈ s, γ i ≠ 0) {δ : ℝ}
    (hδ : 0 < δ) : EdgeData (mergeOrd s γ) where
  δ := δ
  g := fun r => (r : ℝ)
  hδ := hδ
  hg0 := pos_of_mem_mergeOrd hγ
  hg := Subtype.val_injective

-- merged §7(iii); Cvs.StepA.Edge.OneOrdinateDiscriminant `EdgePositiveFamilies`
/-- **Edge positivity of every finite family**. -/
theorem edgePositiveFamilies : Cvs.StepA.Edge.OneOrdinateDiscriminant.EdgePositiveFamilies := by
  intro α s m γ δ hδ hs hm hγ
  classical
  have := nonempty_mergeOrd hs γ
  obtain ⟨L, hL⟩ := exists_edgeDisc_pos (mergeData hγ hδ) (m := fun r => mergeW s m γ r)
    (mergeW_pos hm)
  exact ⟨L, by rw [← edgeDisc_merge]; exact hL⟩

-- merged corollary (5)

-- an earlier result

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

end Cvs.StepA.Edge.PlanarBoxLemma
