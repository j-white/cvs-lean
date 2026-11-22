import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.RungSpanTailHighMass
import Cvs.Prolate.AngularEndpointLowerBound
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A rung's tail mass is at least `e^{−3πc/2}` up to powers of `c`, and its edge data are polynomial

With `ψ = μh` on `[−1, 1]`: `|h(±1)| ≤ L/|μ|`, `h′(±1) = ±(χ − c²)h(±1)/2` and `h″ = ψ″/μ` inside, so
`∫|h″| ≤ 2c²L/|μ|`, where `L = ∫|h| ≤ √2`. Near `ξ = 1`, `|ψ′| ≤ cL` keeps `|ψ| ≥ a/2` on an interval of length
`a/(2(cL + a))`, `a = |ψ(1)|`, so `∫₁^∞ ψ² ≥ a³/(8(cL + a))`; Cvs.Prolate.AngularEndpointLowerBound gives `a ≥ |μ|e^{−πc/2}/√2`.
-/

namespace Cvs.Prolate.RungTailMassLower

open Real Set MeasureTheory Filter Topology
open Cvs.L2a.AngularProlateTailPositive (psi)

variable {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}

/-- `L = ∫|h| ≤ √2` for `∫h² = 1`. -/
theorem integral_abs_le_sqrt_two (hgc : ContinuousOn g (Icc (-1) 1)) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) :
    ∫ s in (-1 : ℝ)..1, |g s| ≤ √2 := by
  have h := Cvs.Prolate.RungTailIntegralMass.sq_integral_le (f := fun s => |g s|) (by norm_num) hgc.abs
  simp only [sq_abs] at h
  rw [hnorm] at h
  norm_num at h
  have h0 : 0 ≤ ∫ s in (-1 : ℝ)..1, |g s| := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  rw [← Real.sqrt_sq h0]; exact Real.sqrt_le_sqrt h

/-- `|h(1)| ≤ L/|μ|`. -/
theorem abs_endpoint_le (hgc : ContinuousOn g (uIcc (-1) 1)) (hμ0 : μ ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    |g 1| ≤ (∫ s in (-1 : ℝ)..1, |g s|) / |μ| := by
  have h := Cvs.L2a.RungSpanTailHighMass.abs_psi_le_L1 (c := c) (ξ := 1) hgc
  rw [hμ 1 ⟨by norm_num, le_rfl⟩, abs_mul, one_mul] at h
  rw [le_div_iff₀ (abs_pos.mpr hμ0)]; linarith

/-- `|h(−1)| ≤ L/|μ|`. -/
theorem abs_endpoint_neg_le (hgc : ContinuousOn g (uIcc (-1) 1)) (hμ0 : μ ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    |g (-1)| ≤ (∫ s in (-1 : ℝ)..1, |g s|) / |μ| := by
  have h := Cvs.L2a.RungSpanTailHighMass.abs_psi_le_L1 (c := c) (ξ := -1) hgc
  rw [hμ (-1) ⟨le_rfl, by norm_num⟩, abs_mul, one_mul] at h
  rw [le_div_iff₀ (abs_pos.mpr hμ0)]; linarith

/-- At `s = ±1` the angular equation gives `h′(1) = (χ − c²)h(1)/2` and `h′(−1) = (c² − χ)h(−1)/2`. -/
theorem deriv_endpoints
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    g₁ 1 = (χ - c ^ 2) * g 1 / 2 ∧ g₁ (-1) = (c ^ 2 - χ) * g (-1) / 2 := by
  have h1 := hang 1 (by rw [uIcc_of_le (by norm_num)]; exact ⟨by norm_num, le_rfl⟩)
  have h2 := hang (-1) (by rw [uIcc_of_le (by norm_num)]; exact ⟨le_rfl, by norm_num⟩)
  constructor <;> nlinarith

/-- Inside `(−1, 1)`, `h″ = ψ″/μ` with `ψ″ = kint h (−c²s² cos(cξs))`. -/
theorem second_eq (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hμ0 : μ ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    g₂ s = Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) s / μ := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hU : ∀ t ∈ Ioo (-1 : ℝ) 1, t ∈ uIcc (-1 : ℝ) 1 := fun t ht => by
    rw [uIcc_of_le (by norm_num)]; exact ⟨ht.1.le, ht.2.le⟩
  -- `g₁ = ψ′/μ` on the open interval
  have h1 : ∀ t ∈ Ioo (-1 : ℝ) 1,
      g₁ t = Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))) t / μ := by
    intro t ht
    have hev : (fun ξ => psi c g ξ / μ) =ᶠ[𝓝 t] g := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with ξ hξ
      rw [hμ ξ ⟨hξ.1.le, hξ.2.le⟩]; field_simp
    have hd := ((Cvs.Prolate.SincTopIsRung.hasDerivAt_psi (c := c) hgc t).div_const μ).congr_of_eventuallyEq hev.symm
    exact (hg t (hU t ht)).unique hd
  have hev1 : (fun ξ => Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ / μ) =ᶠ[𝓝 s] g₁ := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with ξ hξ
    exact (h1 ξ hξ).symm
  have hd := ((Cvs.Prolate.SincTopIsRung.hasDerivAt_psi₁ (c := c) hgc s).div_const μ).congr_of_eventuallyEq hev1.symm
  exact (hg₁ s (hU s hs)).unique hd

/-- `∫|h″| ≤ 2c²L/|μ|`. -/
theorem integral_abs_second_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hμ0 : μ ≠ 0) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    ∫ s in (-1 : ℝ)..1, |g₂ s| ≤ 2 * (c ^ 2 * (∫ s in (-1 : ℝ)..1, |g s|) / |μ|) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hpt : ∀ s ∈ Ioo (-1 : ℝ) 1, |g₂ s| ≤ c ^ 2 * (∫ s in (-1 : ℝ)..1, |g s|) / |μ| := by
    intro s hs
    rw [second_eq hg hg₁ hμ0 hμ hs, abs_div]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
    refine Cvs.L2a.RungSpanTailHighMass.abs_kint_le ?_ hgc.intervalIntegrable fun t ht => ?_
    · exact (hgc.mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable
    · have ht' : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg (sq_nonneg t)]
      calc c ^ 2 * t ^ 2 * |cos (c * s * t)| ≤ c ^ 2 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left ht' (sq_nonneg c)) (abs_cos_le_one _) (abs_nonneg _) (by positivity)
        _ = c ^ 2 := by ring
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1)
    (hg₂c.abs.intervalIntegrable) intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-! ### The tail mass from the endpoint -/

/-- **Mass near the edge**: if `|ψ′| ≤ D` on `[1, 3/2]`, `D > 0`, and `a = |ψ(1)|`, then `∫₁^∞ ψ² ≥ a³/(8(D + a))`. -/
theorem mass_ge_of_endpoint {ψ ψ₁ : ℝ → ℝ} {D : ℝ} (hD : 0 < D)
    (hψ : ∀ ξ ∈ Icc (1 : ℝ) (3 / 2), HasDerivAt ψ (ψ₁ ξ) ξ) (hψ₁ : ∀ ξ ∈ Icc (1 : ℝ) (3 / 2), |ψ₁ ξ| ≤ D)
    (hint : IntegrableOn (fun ξ => ψ ξ ^ 2) (Ioi 1)) :
    |ψ 1| ^ 3 / (8 * (D + |ψ 1|)) ≤ ∫ ξ in Ioi 1, ψ ξ ^ 2 := by
  set a := |ψ 1| with had
  have ha0 : 0 ≤ a := abs_nonneg _
  set δ := a / (2 * (D + a)) with hδd
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 2 := by
    rw [hδd, div_le_iff₀ (by positivity)]; nlinarith
  -- `|ψ| ≥ a/2` on `[1, 1 + δ]`
  have hlow : ∀ ξ ∈ Icc (1 : ℝ) (1 + δ), a / 2 ≤ |ψ ξ| := by
    intro ξ hξ
    have hsub : Icc (1 : ℝ) ξ ⊆ Icc 1 (3 / 2) := Icc_subset_Icc le_rfl (by linarith [hξ.2])
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ψ) (f' := ψ₁) (s := Icc (1 : ℝ) ξ)
      (fun x hx => (hψ x (hsub hx)).hasDerivWithinAt) (fun x hx => by
        rw [Real.norm_eq_abs]; exact hψ₁ x (hsub hx)) (convex_Icc 1 ξ) ⟨le_rfl, hξ.1⟩ ⟨hξ.1, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ ξ - 1 by linarith [hξ.1])] at hmvt
    have hDδ : D * (ξ - 1) ≤ a / 2 := by
      calc D * (ξ - 1) ≤ D * δ := mul_le_mul_of_nonneg_left (by linarith [hξ.2]) hD.le
        _ ≤ a / 2 := by
          rw [hδd, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    have := abs_sub_abs_le_abs_sub (ψ 1) (ψ ξ)
    rw [abs_sub_comm (ψ 1) (ψ ξ)] at this
    linarith
  have hsq : ∀ ξ ∈ Ioc (1 : ℝ) (1 + δ), a ^ 2 / 4 ≤ ψ ξ ^ 2 := fun ξ hξ => by
    have h := hlow ξ ⟨hξ.1.le, hξ.2⟩
    have := pow_le_pow_left₀ (by positivity) h 2
    rw [sq_abs] at this; nlinarith
  calc a ^ 3 / (8 * (D + a)) = (a ^ 2 / 4) * δ := by rw [hδd]; field_simp; ring
    _ = ∫ ξ in Ioc (1 : ℝ) (1 + δ), a ^ 2 / 4 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]; ring
    _ ≤ ∫ ξ in Ioc (1 : ℝ) (1 + δ), ψ ξ ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hsq
    _ ≤ ∫ ξ in Ioi 1, ψ ξ ^ 2 :=
        setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)

/-- **A rung's tail mass**: for an even normalised angular eigenfunction with `0 ≤ χ ≤ c²`, `c ≥ 1`, `μ ≠ 0`,
`M = ∫₁^∞ ψ² ≥ (|μ|e^{−πc/2}/√2)³/(16√2c)`. -/
theorem mass_ge (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) (hμ0 : μ ≠ 0) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (|μ| * exp (-(π * c / 2)) / √2) ^ 3 / (16 * √2 * c) ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hgcI : ContinuousOn g (Icc (-1) 1) := by simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hgc
  set L := ∫ s in (-1 : ℝ)..1, |g s| with hLd
  have hL : L ≤ √2 := integral_abs_le_sqrt_two hgcI hnorm
  have hL0 : 0 ≤ L := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  have hint : IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1) :=
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi hg hg₁ hg₂c hang hc0).integrable_sq
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hD : 0 < c * √2 := by positivity
  have hm := mass_ge_of_endpoint (ψ := psi c g)
    (ψ₁ := Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s)))) hD
    (fun ξ _ => Cvs.Prolate.SincTopIsRung.hasDerivAt_psi hgc ξ)
    (fun ξ _ => (Cvs.L2a.RungSpanTailHighMass.abs_psi₁_le_L1 hgc).trans (by
      rw [abs_of_pos hc0]; exact mul_le_mul_of_nonneg_left hL hc0.le)) hint
  -- the endpoint value
  have ha : |μ| * exp (-(π * c / 2)) / √2 ≤ |psi c g 1| := by
    rw [hμ 1 ⟨by norm_num, le_rfl⟩, abs_mul]
    have he := Cvs.Prolate.AngularEndpointLowerBound.endpoint_sq_ge hc0 hχ0 hχ hg hg₁ hang heven hnorm
    have h1 : exp (-(π * c / 2)) / √2 ≤ |g 1| := by
      rw [← Real.sqrt_sq (abs_nonneg (g 1)), sq_abs]
      have : (exp (-(π * c / 2)) / √2) ^ 2 = 1 / 2 * exp (-(π * c)) := by
        rw [div_pow, Real.sq_sqrt (by norm_num), ← exp_nat_mul]; push_cast; ring_nf
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ exp (-(π * c / 2)) / √2), this]
      exact Real.sqrt_le_sqrt he
    calc |μ| * exp (-(π * c / 2)) / √2 = |μ| * (exp (-(π * c / 2)) / √2) := by ring
      _ ≤ |μ| * |g 1| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have haup : |psi c g 1| ≤ √2 := (Cvs.L2a.RungSpanTailHighMass.abs_psi_le_L1 hgc).trans (by rw [one_mul]; exact hL)
  set a := |psi c g 1|
  set a₀ := |μ| * exp (-(π * c / 2)) / √2
  have ha₀ : 0 ≤ a₀ := by positivity
  have hden : c * √2 + a ≤ 2 * √2 * c := by nlinarith
  calc a₀ ^ 3 / (16 * √2 * c) ≤ a ^ 3 / (16 * √2 * c) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ ha₀ ha 3) (by positivity)
    _ ≤ a ^ 3 / (8 * (c * √2 + a)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
    _ ≤ _ := hm

end Cvs.Prolate.RungTailMassLower
