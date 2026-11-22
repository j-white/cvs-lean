import Mathlib
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.VolterraResolventEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The regular solution in `χ`: the variational solution and the mass identity

`regDot = ∂_χ regSol` solves `((ξ²−1)ḟ')' + (Q − χ)ḟ = f` with `ḟ(1) = 0` and zero flux at `1`; the flux `regU` is
differentiable in `χ` with derivative `regUDot`. The Wronskian `f U̇ − U ḟ` is `∫₁^ξ f²`. Both `regSol` and `regU`
are jointly continuous in `(χ, ξ)` on `ℝ × (−1, ∞)`.
-/

noncomputable section

open Real Set intervalIntegral MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.VolterraResolventEdge Cvs.Prolate.RegularSolutionEdge
open scoped Interval

namespace Cvs.Prolate.RegularSolutionChiVariation

variable {a b : ℝ}

theorem ext_sub (h : a ≤ b) (y₁ y₂ : Cab a b) : (y₁ - y₂).ext h = y₁.ext h - y₂.ext h := by
  funext x; rfl

/-! ### The pointwise `χ`-derivative -/

theorem regSol_chi_eq_on (Q : C(ℝ, ℝ)) (h : Adm a b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    (fun χ => regSol Q χ ξ) =
      (Cab.evalAt h.le ξ) ∘ (fun χ => regOn h (Cab.restr Q - algebraMap ℝ (Cab a b) χ)) := by
  funext χ
  simp only [Function.comp_apply, Cab.evalAt_apply]
  rw [regSol_eq_regOn Q χ h hξ, restr_sub_const]

/-- On any admissible interval containing `ξ`, the `χ`-derivative of `regSol` is `dotOn` there. -/
theorem hasDerivAt_regSol_chi_on (Q : C(ℝ, ℝ)) (χ : ℝ) (h : Adm a b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    HasDerivAt (fun χ' => regSol Q χ' ξ)
      ((dotOn h (Cab.restr (Q - ContinuousMap.const ℝ χ))).ext h.le ξ) χ := by
  have hd := hasDerivAt_regOn_sub h (Cab.restr Q) χ
  have he := (Cab.evalAt h.le ξ).hasFDerivAt.comp_hasDerivAt χ hd
  rw [regSol_chi_eq_on Q h hξ]
  refine he.congr_deriv ?_
  rw [restr_sub_const]
  rfl

/-- The variational solution `ḟ = ∂_χ regSol`. -/
def regDot (Q : C(ℝ, ℝ)) (χ ξ : ℝ) : ℝ := deriv (fun χ' => regSol Q χ' ξ) χ

/-- The source of the variational equation, `f − (Q − χ)ḟ`. -/
def regDotZ (Q : C(ℝ, ℝ)) (χ s : ℝ) : ℝ := regSol Q χ s - (Q s - χ) * regDot Q χ s

/-- The derivative of the variational solution, `avg (f − (Q − χ)ḟ)`. -/
def regDotV (Q : C(ℝ, ℝ)) (χ ξ : ℝ) : ℝ := avg (regDotZ Q χ) ξ

/-- The flux `(ξ²−1)ḟ'` of the variational solution. -/
def regUDot (Q : C(ℝ, ℝ)) (χ ξ : ℝ) : ℝ := ∫ t in (1:ℝ)..ξ, regDotZ Q χ t

theorem hasDerivAt_regSol_regDot (Q : C(ℝ, ℝ)) (χ ξ : ℝ) :
    HasDerivAt (fun χ' => regSol Q χ' ξ) (regDot Q χ ξ) χ :=
  (Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regSol_chi Q ξ χ).differentiableAt.hasDerivAt

theorem regDot_eq_dotOn (Q : C(ℝ, ℝ)) (χ : ℝ) (h : Adm a b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    regDot Q χ ξ = (dotOn h (Cab.restr (Q - ContinuousMap.const ℝ χ))).ext h.le ξ :=
  (hasDerivAt_regSol_chi_on Q χ h hξ).deriv

/-! ### The variational equation -/

theorem dotOn_apply (h : Adm a b) (q : Cab a b) (ξ : Icc a b) :
    (dotOn h q).toC ξ = green ((regOn h q - q * dotOn h q).ext h.le) ξ := by
  have e : dotOn h q = volterra h (regOn h q - q * dotOn h q) := by
    rw [map_sub]; exact eq_sub_of_add_eq (dotOn_add h q)
  exact (congrArg (fun y : Cab a b => y.toC ξ) e).trans (volterra_apply _ _ _)

theorem ext_dotZ (Q : C(ℝ, ℝ)) (χ : ℝ) (h : Adm a b) {s : ℝ} (hs : s ∈ Icc a b) :
    (regOn h (Cab.restr (Q - ContinuousMap.const ℝ χ)) -
        Cab.restr (Q - ContinuousMap.const ℝ χ) * dotOn h (Cab.restr (Q - ContinuousMap.const ℝ χ))).ext h.le s =
      regDotZ Q χ s := by
  rw [ext_sub, Cab.ext_mul]
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [Cab.ext_restr _ _ hs, ← regSol_eq_regOn Q χ h hs, ← regDot_eq_dotOn Q χ h hs]
  rfl

theorem hasDerivAt_regDot (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ₀ : ℝ} (hξ₀ : -1 < ξ₀) :
    HasDerivAt (regDot Q χ) (regDotV Q χ ξ₀) ξ₀ := by
  have h₀ := adm_lohi ξ₀
  have hm := mem_lohi hξ₀
  set q : Cab (lo ξ₀) (hi ξ₀) := Cab.restr (Q - ContinuousMap.const ℝ χ)
  set z := (regOn h₀ q - q * dotOn h₀ q).ext h₀.le
  have hF : HasDerivAt (green z) (avg z ξ₀) ξ₀ := hasDerivAt_green (Cab.continuous_ext _ _) hξ₀
  have heq : regDot Q χ =ᶠ[𝓝 ξ₀] green z := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with ξ hξ
    have hξI : ξ ∈ Icc (lo ξ₀) (hi ξ₀) := ⟨hξ.1.le, hξ.2.le⟩
    rw [regDot_eq_dotOn Q χ h₀ hξI, Cab.ext_eq _ _ hξI, dotOn_apply]
  refine (hF.congr_of_eventuallyEq heq).congr_deriv ?_
  apply avg_congr
  intro s hs
  exact ext_dotZ Q χ h₀ (h₀.sub ⟨hm.1.le, hm.2.le⟩ hs)

theorem regDot_one (Q : C(ℝ, ℝ)) (χ : ℝ) : regDot Q χ 1 = 0 := by
  have h := adm_lohi 1
  have h1 : (1:ℝ) ∈ Icc (lo 1) (hi 1) := ⟨h.le_one, h.one_le⟩
  rw [regDot_eq_dotOn Q χ h h1, Cab.ext_eq _ _ h1, dotOn_apply]
  simp [green]

theorem continuousOn_regDot (Q : C(ℝ, ℝ)) (χ : ℝ) : ContinuousOn (regDot Q χ) (Ioi (-1)) :=
  fun _ hξ => (hasDerivAt_regDot Q χ hξ).continuousAt.continuousWithinAt

theorem continuousOn_regDotZ (Q : C(ℝ, ℝ)) (χ : ℝ) : ContinuousOn (regDotZ Q χ) (Ioi (-1)) :=
  (continuousOn_regSol Q χ).sub
    (((Q.continuous.sub continuous_const).continuousOn).mul (continuousOn_regDot Q χ))

theorem pP_mul_regDotV (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    pP ξ * regDotV Q χ ξ = regUDot Q χ ξ :=
  pP_mul_avg _ (by intro e; linarith)

theorem hasDerivAt_regUDot (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    HasDerivAt (regUDot Q χ) (regDotZ Q χ ξ) ξ := by
  have hz := continuousOn_regDotZ Q χ
  have hI : IntervalIntegrable (regDotZ Q χ) volume 1 ξ :=
    (hz.mono (uIcc_one_subset_Ioi hξ)).intervalIntegrable
  exact integral_hasDerivAt_right hI (hz.stronglyMeasurableAtFilter isOpen_Ioi ξ hξ)
    (hz.continuousAt (Ioi_mem_nhds hξ))

/-! ### The flux in `χ` -/

/-- `y ↦ ∫₁^ξ y`, as a continuous linear functional on `C([a, b])`. -/
def primAt (h : a ≤ b) (ξ : ℝ) : Cab a b →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun y => ∫ s in (1:ℝ)..ξ, y.ext h s
      map_add' := fun y₁ y₂ => by
        rw [Cab.ext_add]
        exact intervalIntegral.integral_add ((y₁.continuous_ext h).intervalIntegrable _ _)
          ((y₂.continuous_ext h).intervalIntegrable _ _)
      map_smul' := fun r y => by
        simp only [Cab.ext_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          intervalIntegral.integral_const_mul] }
    |ξ - 1| (fun y => by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => ?_)).trans_eq (mul_comm _ _)
      rw [Real.norm_eq_abs]; exact Cab.abs_ext_le h y s)

theorem primAt_apply (h : a ≤ b) (ξ : ℝ) (y : Cab a b) : primAt h ξ y = ∫ s in (1:ℝ)..ξ, y.ext h s := rfl

theorem regU_eq_primAt (Q : C(ℝ, ℝ)) (χ : ℝ) (h : Adm a b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    regU Q χ ξ = -primAt h.le ξ ((Cab.restr Q - algebraMap ℝ (Cab a b) χ) *
      regOn h (Cab.restr Q - algebraMap ℝ (Cab a b) χ)) := by
  rw [regU, primAt_apply, ← restr_sub_const]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsI := h.sub hξ hs
  simp only [Cab.ext_mul, Pi.mul_apply]
  rw [Cab.ext_restr _ _ hsI, ← regSol_eq_regOn Q χ h hsI]
  rfl

/-- The flux of the regular solution is differentiable in `χ`, with derivative `regUDot`. -/
theorem hasDerivAt_regU_chi (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    HasDerivAt (fun χ' => regU Q χ' ξ) (regUDot Q χ ξ) χ := by
  have h := adm_lohi ξ
  have hm := mem_lohi hξ
  have hξI : ξ ∈ Icc (lo ξ) (hi ξ) := ⟨hm.1.le, hm.2.le⟩
  have hq : HasDerivAt (fun χ' => Cab.restr Q - algebraMap ℝ (Cab (lo ξ) (hi ξ)) χ') (-1) χ := by
    have := ((hasDerivAt_id χ).smul_const (1 : Cab (lo ξ) (hi ξ))).const_sub (Cab.restr Q)
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have hf := hasDerivAt_regOn_sub h (Cab.restr Q) χ
  have hprod := hq.mul hf
  have hP := ((primAt h.le ξ).hasFDerivAt.comp_hasDerivAt χ hprod).neg
  have e : (fun χ' => regU Q χ' ξ) = fun χ' => -(primAt h.le ξ ∘ ((fun χ' => Cab.restr Q -
      algebraMap ℝ (Cab (lo ξ) (hi ξ)) χ') * fun χ' => regOn h (Cab.restr Q -
        algebraMap ℝ (Cab (lo ξ) (hi ξ)) χ'))) χ' := by
    funext χ'
    rw [regU_eq_primAt Q χ' h hξI]
    rfl
  rw [e]
  refine hP.congr_deriv ?_
  rw [← restr_sub_const]
  set q : Cab (lo ξ) (hi ξ) := Cab.restr (Q - ContinuousMap.const ℝ χ)
  have e2 : -1 * regOn h q + q * dotOn h q = -(regOn h q - q * dotOn h q) := by ring
  rw [e2, map_neg, neg_neg, primAt_apply, regUDot]
  apply intervalIntegral.integral_congr
  intro s hs
  exact ext_dotZ Q χ h (h.sub hξI hs)

/-! ### The mass identity -/

/-- **The mass identity**: `f U̇ − U ḟ = ∫₁^ξ f²` on `(−1, ∞)`. -/
theorem mass_identity (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    regSol Q χ ξ * regUDot Q χ ξ - regU Q χ ξ * regDot Q χ ξ = ∫ t in (1:ℝ)..ξ, regSol Q χ t ^ 2 := by
  set F : ℝ → ℝ := fun t => regSol Q χ t * regUDot Q χ t - regU Q χ t * regDot Q χ t
  have hd : ∀ t, -1 < t → HasDerivAt F (regSol Q χ t ^ 2) t := by
    intro t ht
    have d := ((hasDerivAt_regSol Q χ ht).mul (hasDerivAt_regUDot Q χ ht)).sub
      ((hasDerivAt_regU Q χ ht).mul (hasDerivAt_regDot Q χ ht))
    refine d.congr_deriv ?_
    rw [← pP_mul_regV Q χ ht, ← pP_mul_regDotV Q χ ht, regDotZ]
    ring
  have hsub := uIcc_one_subset_Ioi hξ
  have hI := ftc_uIcc (f := F) (f' := fun t => regSol Q χ t ^ 2) (x := 1) (y := ξ)
    (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht)))
    (((continuousOn_regSol Q χ).pow 2).mono hsub).intervalIntegrable
  rw [hI]
  simp [F, regUDot, regU, regDot_one]

/-! ### Joint continuity in `(χ, ξ)` -/

theorem continuous_ext_joint (h : a ≤ b) {R : ℝ → Cab a b} (hR : Continuous R) :
    Continuous fun p : ℝ × ℝ => (R p.1).ext h p.2 := by
  rw [continuous_iff_continuousAt]; intro p₀
  have e : (fun p : ℝ × ℝ => (R p.1).ext h p.2) =
      fun p => (R p.1 - R p₀.1).ext h p.2 + (R p₀.1).ext h p.2 := by
    funext p; rw [ext_sub]; simp
  rw [e]
  have h2 : ContinuousAt (fun p : ℝ × ℝ => (R p₀.1).ext h p.2) p₀ :=
    ((R p₀.1).continuous_ext h).continuousAt.comp continuous_snd.continuousAt
  have h1 : ContinuousAt (fun p : ℝ × ℝ => (R p.1 - R p₀.1).ext h p.2) p₀ := by
    have h0 : (R p₀.1 - R p₀.1).ext h p₀.2 = 0 := by rw [sub_self]; rfl
    rw [ContinuousAt, h0]
    have ht := tendsto_iff_norm_sub_tendsto_zero.1 ((hR.comp continuous_fst).continuousAt (x := p₀))
    refine squeeze_zero_norm (fun p => ?_) ht
    rw [Real.norm_eq_abs]; exact Cab.abs_ext_le h _ p.2
  exact h1.add h2

/-- The regular solution is jointly continuous in `(χ, ξ)`. -/
theorem continuousOn_regSol_joint (Q : C(ℝ, ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ => regSol Q p.1 p.2) (univ ×ˢ Ioi (-1)) := by
  rintro ⟨χ₀, ξ₀⟩ ⟨-, hξ₀⟩
  have h₀ := adm_lohi ξ₀
  have hm := mem_lohi (show -1 < ξ₀ from hξ₀)
  set R : ℝ → Cab (lo ξ₀) (hi ξ₀) := fun χ => regOn h₀ (Cab.restr Q - algebraMap ℝ _ χ)
  have hR : Continuous R :=
    continuous_iff_continuousAt.2 fun χ => (hasDerivAt_regOn_sub h₀ _ χ).continuousAt
  have hG := (continuous_ext_joint h₀.le hR).continuousAt (x := (χ₀, ξ₀))
  have heq : (fun p : ℝ × ℝ => (R p.1).ext h₀.le p.2) =ᶠ[𝓝 (χ₀, ξ₀)] fun p => regSol Q p.1 p.2 := by
    filter_upwards [prod_mem_nhds univ_mem (Ioo_mem_nhds hm.1 hm.2)] with p hp
    rw [regSol_eq_regOn Q p.1 h₀ ⟨hp.2.1.le, hp.2.2.le⟩, restr_sub_const]
  exact (hG.congr heq).continuousWithinAt

/-- The flux of the regular solution is jointly continuous in `(χ, ξ)`. -/
theorem continuousOn_regU_joint (Q : C(ℝ, ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ => regU Q p.1 p.2) (univ ×ˢ Ioi (-1)) := by
  rintro ⟨χ₀, ξ₀⟩ ⟨-, hξ₀⟩
  have h₀ := adm_lohi ξ₀
  have hm := mem_lohi (show -1 < ξ₀ from hξ₀)
  set R : ℝ → Cab (lo ξ₀) (hi ξ₀) := fun χ =>
    (Cab.restr Q - algebraMap ℝ _ χ) * regOn h₀ (Cab.restr Q - algebraMap ℝ _ χ)
  have hR : Continuous R := by
    have hq : Continuous fun χ => Cab.restr Q - algebraMap ℝ (Cab (lo ξ₀) (hi ξ₀)) χ :=
      continuous_const.sub (continuous_algebraMap ℝ (Cab (lo ξ₀) (hi ξ₀)))
    have hf : Continuous fun χ => regOn h₀ (Cab.restr Q - algebraMap ℝ (Cab (lo ξ₀) (hi ξ₀)) χ) :=
      continuous_iff_continuousAt.2 fun χ => (hasDerivAt_regOn_sub h₀ _ χ).continuousAt
    exact hq.mul hf
  have hG := (intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) (a₀ := 1)
    (f := fun χ s => (R χ).ext h₀.le s) (continuous_ext_joint h₀.le hR)).neg.continuousAt
    (x := (χ₀, ξ₀))
  have heq : (fun p : ℝ × ℝ => -∫ s in (1:ℝ)..p.2, (R p.1).ext h₀.le s) =ᶠ[𝓝 (χ₀, ξ₀)]
      fun p => regU Q p.1 p.2 := by
    filter_upwards [prod_mem_nhds univ_mem (Ioo_mem_nhds hm.1 hm.2)] with p hp
    rw [regU_eq_primAt Q p.1 h₀ ⟨hp.2.1.le, hp.2.2.le⟩, primAt_apply]
  exact (hG.congr heq).continuousWithinAt

end Cvs.Prolate.RegularSolutionChiVariation
