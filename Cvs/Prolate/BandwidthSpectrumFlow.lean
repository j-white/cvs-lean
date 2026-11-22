import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformVirial
import Cvs.Prolate.ScaleGeneratorCauchyWeight
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bandwidth flow of the prolate spectrum

Along a `C¹` branch `ψ_c G_c = μ_c G_c` of even eigenfunctions, paired with an eigenfunction `ψ_c h = νh` at `c₀`:
`∫ h · ∂_c ψ_c G = μ′∫hG + (μ − ν)∫h ∂_cG`. With Cvs.Prolate.CosineTransformVirial and Cvs.Prolate.ScaleGeneratorCauchyWeight this is the flow: `μ′ = (μ/c)(G(1)² − ½)`
(Slepian's `d log λ/dc = 2ψ(1)²/c`) and `(μ − ν)∫h ∂_cG = 2μν h(1)G(1)/(c(μ + ν))` for `ν ≠ μ`: the edge values
drive the spectrum through the Cauchy weight. The branch's regularity in `c` is a hypothesis.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace Cvs.Prolate.BandwidthSpectrumFlow

open Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex Cvs.Prolate.CosineTransformVirial Cvs.Prolate.ScaleGeneratorCauchyWeight

theorem uIcc_eq : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)

/-- **The finite cosine transform is symmetric**: `∫ h · ψ_c g = ∫ g · ψ_c h`. -/
theorem psi_symm {g h : ℝ → ℝ} (hgc : ContinuousOn g (Icc (-1) 1)) (hhc : ContinuousOn h (Icc (-1) 1)) (c : ℝ) :
    ∫ ξ in (-1 : ℝ)..1, h ξ * psi c g ξ = ∫ ξ in (-1 : ℝ)..1, g ξ * psi c h ξ := by
  unfold psi kint
  simp_rw [← intervalIntegral.integral_const_mul]
  have hK : Continuous fun p : ℝ × ℝ => cos (c * p.1 * p.2) := by fun_prop
  have hcont : ContinuousOn (Function.uncurry fun ξ s => h ξ * (g s * cos (c * ξ * s)))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1) 1) :=
    (hhc.comp continuousOn_fst (fun (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1) 1) => hp.1)).mul
      ((hgc.comp continuousOn_snd (fun (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1) 1) => hp.2)).mul hK.continuousOn)
  have hint : IntegrableOn (Function.uncurry fun ξ s => h ξ * (g s * cos (c * ξ * s)))
      (uIoc (-1 : ℝ) 1 ×ˢ uIoc (-1) 1) := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegral_intervalIntegral_swap hint]
  refine intervalIntegral.integral_congr fun s _ => intervalIntegral.integral_congr fun ξ _ => ?_
  rw [show c * s * ξ = c * ξ * s by ring]; ring

/-- **Eigenfunctions of distinct eigenvalues are orthogonal.** -/
theorem orthogonal {g h : ℝ → ℝ} {c μ ν : ℝ} (hgc : ContinuousOn g (Icc (-1) 1))
    (hhc : ContinuousOn h (Icc (-1) 1)) (heg : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (heh : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = ν * h s) (hμν : μ ≠ ν) :
    ∫ ξ in (-1 : ℝ)..1, h ξ * g ξ = 0 := by
  have hS := psi_symm hgc hhc c
  have e1 : ∫ ξ in (-1 : ℝ)..1, h ξ * psi c g ξ = μ * ∫ ξ in (-1 : ℝ)..1, h ξ * g ξ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    show h ξ * psi c g ξ = μ * (h ξ * g ξ)
    rw [heg ξ (uIcc_eq ▸ hξ)]; ring
  have e2 : ∫ ξ in (-1 : ℝ)..1, g ξ * psi c h ξ = ν * ∫ ξ in (-1 : ℝ)..1, h ξ * g ξ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    show g ξ * psi c h ξ = ν * (h ξ * g ξ)
    rw [heh ξ (uIcc_eq ▸ hξ)]; ring
  rw [e1, e2] at hS
  have : (μ - ν) * ∫ ξ in (-1 : ℝ)..1, h ξ * g ξ = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hμν)

/-- A `C¹` branch of eigenfunctions near `c₀`: pointwise derivative `G'` in `c`, a uniform bound, continuity. -/
structure Branch (G G' : ℝ → ℝ → ℝ) (μ : ℝ → ℝ) (c₀ : ℝ) (U : Set ℝ) (M : ℝ) : Prop where
  mem : U ∈ 𝓝 c₀
  deriv : ∀ c ∈ U, ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun c => G c t) (G' c t) c
  bound : ∀ c ∈ U, ∀ t ∈ Icc (-1 : ℝ) 1, |G c t| ≤ M ∧ |G' c t| ≤ M
  cont : ∀ c ∈ U, ContinuousOn (G c) (Icc (-1) 1)
  cont' : ContinuousOn (G' c₀) (Icc (-1) 1)
  eig : ∀ c ∈ U, ∀ ξ ∈ Icc (-1 : ℝ) 1, psi c (G c) ξ = μ c * G c ξ

/-- **The transform along the branch**: `∂_c[ψ_c G_c](ξ) = (∂_c ψ_c)G + ψ_c(∂_c G)`. -/
theorem hasDerivAt_psi_branch {G G' : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {c₀ M : ℝ} {U : Set ℝ}
    (hB : Branch G G' μ c₀ U M) (ξ : ℝ) :
    HasDerivAt (fun c => psi c (G c) ξ)
      (kint (G c₀) (fun c s => -(ξ * s * sin (c * ξ * s))) c₀ + psi c₀ (G' c₀) ξ) c₀ := by
  have hc₀ : c₀ ∈ U := mem_of_mem_nhds hB.mem
  have hIoc : Ι (-1 : ℝ) 1 = Ioc (-1) 1 := uIoc_of_le (by norm_num)
  have hcos : Continuous fun t : ℝ => cos (c₀ * ξ * t) := by fun_prop
  have hsin : Continuous fun t : ℝ => -(ξ * t * sin (c₀ * ξ * t)) := by fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1) (b := 1) (F := fun c t => G c t * cos (c * ξ * t))
    (F' := fun c t => G' c t * cos (c * ξ * t) + G c t * -(ξ * t * sin (c * ξ * t)))
    (x₀ := c₀) (bound := fun _ => M + M * |ξ|) hB.mem
    (Filter.mem_of_superset hB.mem fun c hc => by
      rw [hIoc]
      exact (((hB.cont c hc).mono Ioc_subset_Icc_self).mul (by fun_prop : Continuous fun t : ℝ =>
        cos (c * ξ * t)).continuousOn).aestronglyMeasurable measurableSet_Ioc)
    ((hB.cont c₀ hc₀).mul hcos.continuousOn |>.mono (uIcc_eq ▸ subset_rfl)).intervalIntegrable
    (by
      rw [hIoc]
      exact (((hB.cont'.mono Ioc_subset_Icc_self).mul hcos.continuousOn).add
        (((hB.cont c₀ hc₀).mono Ioc_subset_Icc_self).mul hsin.continuousOn)).aestronglyMeasurable
          measurableSet_Ioc)
    (Filter.Eventually.of_forall fun t ht c hc => by
      rw [hIoc] at ht
      have htI : t ∈ Icc (-1 : ℝ) 1 := Ioc_subset_Icc_self ht
      obtain ⟨hG, hG'⟩ := hB.bound c hc t htI
      have ht1 : |t| ≤ 1 := abs_le.2 ⟨htI.1, htI.2⟩
      rw [Real.norm_eq_abs]
      have hM : 0 ≤ M := (abs_nonneg _).trans hG
      have a1 : |G' c t| * |cos (c * ξ * t)| ≤ M * 1 :=
        mul_le_mul hG' (abs_cos_le_one _) (abs_nonneg _) hM
      have a2 : |ξ| * |t| * |sin (c * ξ * t)| ≤ |ξ| * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)) (abs_sin_le_one _) (abs_nonneg _)
          (by positivity)
      have a3 : |G c t| * (|ξ| * |t| * |sin (c * ξ * t)|) ≤ M * (|ξ| * 1 * 1) :=
        mul_le_mul hG a2 (by positivity) hM
      calc |G' c t * cos (c * ξ * t) + G c t * -(ξ * t * sin (c * ξ * t))|
          ≤ |G' c t| * |cos (c * ξ * t)| + |G c t| * (|ξ| * |t| * |sin (c * ξ * t)|) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_mul]
        _ ≤ M + M * |ξ| := by linarith)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht c hc => by
      rw [hIoc] at ht
      have h1 := hB.deriv c hc t (Ioc_subset_Icc_self ht)
      have h2 := ((hasDerivAt_id c).mul_const ξ |>.mul_const t).cos
      refine (h1.mul h2).congr_deriv ?_; simp only [id]; ring)
  have hsplit : (∫ t in (-1 : ℝ)..1, G' c₀ t * cos (c₀ * ξ * t) + G c₀ t * -(ξ * t * sin (c₀ * ξ * t)))
      = psi c₀ (G' c₀) ξ + kint (G c₀) (fun c s => -(ξ * s * sin (c * ξ * s))) c₀ := by
    rw [intervalIntegral.integral_add]
    · rfl
    · exact (hB.cont'.mul hcos.continuousOn |>.mono (uIcc_eq ▸ subset_rfl)).intervalIntegrable
    · exact ((hB.cont c₀ hc₀).mul hsin.continuousOn |>.mono (uIcc_eq ▸ subset_rfl)).intervalIntegrable
  have := key.2
  rw [hsplit, add_comm] at this
  exact this

/-- **The differentiated eigen relation**, pointwise on `[−1, 1]`. -/
theorem deriv_eig {G G' : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {c₀ M μ' : ℝ} {U : Set ℝ}
    (hB : Branch G G' μ c₀ U M) (hμ : HasDerivAt μ μ' c₀) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    kint (G c₀) (fun c s => -(ξ * s * sin (c * ξ * s))) c₀ + psi c₀ (G' c₀) ξ
      = μ' * G c₀ ξ + μ c₀ * G' c₀ ξ := by
  have hc₀ : c₀ ∈ U := mem_of_mem_nhds hB.mem
  have hev : (fun c => psi c (G c) ξ) =ᶠ[𝓝 c₀] fun c => μ c * G c ξ :=
    Filter.mem_of_superset hB.mem fun c hc => hB.eig c hc ξ hξ
  exact (hasDerivAt_psi_branch hB ξ).unique ((hμ.mul (hB.deriv c₀ hc₀ ξ hξ)).congr_of_eventuallyEq hev)

/-- **The branch paired with an eigenfunction**: `∫ h · ∂_c ψ_c G = μ′∫hG + (μ − ν)∫h ∂_cG`. -/
theorem branch_pair {G G' : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {c₀ M μ' ν : ℝ} {U : Set ℝ}
    (hB : Branch G G' μ c₀ U M) (hμ : HasDerivAt μ μ' c₀) {h : ℝ → ℝ} (hhc : ContinuousOn h (Icc (-1) 1))
    (heh : ∀ s ∈ Icc (-1 : ℝ) 1, psi c₀ h s = ν * h s) :
    ∫ ξ in (-1 : ℝ)..1, h ξ * kint (G c₀) (fun c s => -(ξ * s * sin (c * ξ * s))) c₀
      = μ' * (∫ ξ in (-1 : ℝ)..1, h ξ * G c₀ ξ) + (μ c₀ - ν) * ∫ ξ in (-1 : ℝ)..1, h ξ * G' c₀ ξ := by
  have hc₀ : c₀ ∈ U := mem_of_mem_nhds hB.mem
  have hGc := hB.cont c₀ hc₀
  have hψc : ContinuousOn (psi c₀ (G' c₀)) (Icc (-1) 1) := fun ξ _ =>
    (hasDerivAt_psi_freq (uIcc_eq ▸ hB.cont') c₀ ξ).continuousAt.continuousWithinAt
  have hpt : ∀ ξ ∈ uIcc (-1 : ℝ) 1, h ξ * kint (G c₀) (fun c s => -(ξ * s * sin (c * ξ * s))) c₀
      = μ' * (h ξ * G c₀ ξ) + μ c₀ * (h ξ * G' c₀ ξ) - h ξ * psi c₀ (G' c₀) ξ := by
    intro ξ hξ
    have := deriv_eig hB hμ (uIcc_eq ▸ hξ)
    rw [show kint (G c₀) (fun c s => -(ξ * s * sin (c * ξ * s))) c₀
      = μ' * G c₀ ξ + μ c₀ * G' c₀ ξ - psi c₀ (G' c₀) ξ by linarith]
    ring
  have i1 : IntervalIntegrable (fun ξ => h ξ * G c₀ ξ) volume (-1) 1 :=
    (hhc.mul hGc |>.mono (uIcc_eq ▸ subset_rfl)).intervalIntegrable
  have i2 : IntervalIntegrable (fun ξ => h ξ * G' c₀ ξ) volume (-1) 1 :=
    (hhc.mul hB.cont' |>.mono (uIcc_eq ▸ subset_rfl)).intervalIntegrable
  have i3 : IntervalIntegrable (fun ξ => h ξ * psi c₀ (G' c₀) ξ) volume (-1) 1 :=
    (hhc.mul hψc |>.mono (uIcc_eq ▸ subset_rfl)).intervalIntegrable
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub ((i1.const_mul _).add (i2.const_mul _)) i3,
    intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, psi_symm hB.cont' hhc c₀,
    intervalIntegral.integral_congr (fun ξ hξ => by
      show G' c₀ ξ * psi c₀ h ξ = ν * (h ξ * G' c₀ ξ)
      rw [heh ξ (uIcc_eq ▸ hξ)]; ring :
      EqOn (fun ξ => G' c₀ ξ * psi c₀ h ξ) (fun ξ => ν * (h ξ * G' c₀ ξ)) (uIcc (-1) 1)),
    intervalIntegral.integral_const_mul]
  ring

/-- **Slepian's flow for the eigenvalue**: along a normalised branch, `μ′ = (μ/c)(G(1)² − ½)`. -/
theorem flow_eigenvalue {G G' : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {c₀ M μ' : ℝ} {U : Set ℝ} {g₁ : ℝ → ℝ}
    (hB : Branch G G' μ c₀ U M) (hμ : HasDerivAt μ μ' c₀) (hc : c₀ ≠ 0)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (G c₀) (g₁ s) s) (hg₁c : ContinuousOn g₁ (uIcc (-1) 1))
    (heven : G c₀ (-1) = G c₀ 1) (hnorm : ∫ ξ in (-1 : ℝ)..1, G c₀ ξ ^ 2 = 1) :
    μ' = μ c₀ / c₀ * (G c₀ 1 ^ 2 - 1 / 2) := by
  have hc₀ : c₀ ∈ U := mem_of_mem_nhds hB.mem
  have hP := branch_pair hB hμ (hB.cont c₀ hc₀) (hB.eig c₀ hc₀)
  rw [virial hc hg hg₁c heven (hB.eig c₀ hc₀), sub_self, zero_mul, add_zero] at hP
  simp only [← pow_two, hnorm, mul_one] at hP
  exact hP.symm

/-- **The off-diagonal flow**: for an even eigenfunction `h` at `c₀` with `ν ≠ μ`, `μ + ν ≠ 0`,
`(μ − ν)∫h ∂_cG = 2μν h(1)G(1)/(c(μ + ν))`. -/
theorem flow_offdiag {G G' : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {c₀ M μ' ν : ℝ} {U : Set ℝ} {g₁ h h₁ : ℝ → ℝ}
    (hB : Branch G G' μ c₀ U M) (hμ : HasDerivAt μ μ' c₀) (hc : c₀ ≠ 0)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (G c₀) (g₁ s) s) (hg₁c : ContinuousOn g₁ (uIcc (-1) 1))
    (heven : G c₀ (-1) = G c₀ 1)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁c : ContinuousOn h₁ (uIcc (-1) 1))
    (hhe : h (-1) = h 1) (heh : ∀ s ∈ Icc (-1 : ℝ) 1, psi c₀ h s = ν * h s)
    (hne : μ c₀ ≠ ν) (hsum : ν + μ c₀ ≠ 0) :
    (μ c₀ - ν) * ∫ ξ in (-1 : ℝ)..1, h ξ * G' c₀ ξ = 2 * ν * μ c₀ * h 1 * G c₀ 1 / (c₀ * (ν + μ c₀)) := by
  have hc₀ : c₀ ∈ U := mem_of_mem_nhds hB.mem
  have hhc : ContinuousOn h (Icc (-1) 1) := fun s hs =>
    (hh s (uIcc_eq ▸ hs)).continuousAt.continuousWithinAt
  have hP := branch_pair hB hμ hhc heh
  have hO := orthogonal (hB.cont c₀ hc₀) hhc (hB.eig c₀ hc₀) heh hne
  rw [pair_virial hc hsum hh hh₁c hg hg₁c hhe heven heh (hB.eig c₀ hc₀), hO] at hP
  rw [mul_zero, zero_add] at hP
  rw [← hP]; field_simp; ring

end Cvs.Prolate.BandwidthSpectrumFlow
