import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge Green identity with an eigenvalue mismatch

`EdgeGreenIdentity`'s multiplier is built at a reference `χ < c²`; a rung at any `χ'` has `W' = ψ(y + ρ) + (χ − χ')ψ(ξ²/D)y`,
so `∫₁^b ψy = W(b) − ∫₁^b ψρ − (χ − χ')∫₁^b ψ(ξ²/D)y`. The multiplier norm is
`∫₁²(ξ²/D)²/ξ ≤ 1/(2(c² − w)(c² − χ))`, and the boundary at `ξ = 2` keeps `EdgeGreenIdentity`'s `ω₂²/(6c³)` with the rung's energy.
-/

namespace Cvs.Prolate.Mellin.EdgeGreenMismatch

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.GreenBoundaryBound Cvs.Prolate.Mellin.EdgeGreenIdentity

/-- `W' = ψ(y + ρ) + (χ − χ')ψ(ξ²/D)y` for a rung pair `u' = −q_{χ'}ψ` against the multiplier built at `χ`. -/
theorem hasDerivAt_greenW_mis {c χ χ' w ξ : ℝ} {ψ u y v : ℝ → ℝ} (hξ : 1 < ξ) (hD : DM c χ w ξ ≠ 0)
    (hψ : HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : HasDerivAt u (-(qP c χ' ξ * ψ ξ)) ξ)
    (hy : HasDerivAt y (v ξ / ξ ^ 2) ξ) (hv : HasDerivAt v (-(w * y ξ)) ξ) :
    HasDerivAt (greenW c χ w ψ u y v)
      (ψ ξ * (y ξ + greenRho c χ w y v ξ) + (χ - χ') * (ψ ξ * (ξ ^ 2 / DM c χ w ξ * y ξ))) ξ := by
  have hp : pP ξ ≠ 0 := (pP_pos hξ).ne'
  have hξ0 : ξ ≠ 0 := by positivity
  have hA : HasDerivAt (fun r => pP r / DM c χ w r) (alphaM c χ w ξ) ξ := by
    have := hasDerivAt_pdivD (w := w) hD; simp only [one_mul] at this; exact this
  have hB : HasDerivAt (fun r => r ^ 2 / DM c χ w r) (betaM c χ w ξ) ξ := by
    have := hasDerivAt_sqdivD (w := w) hD; simp only [one_mul] at this; exact this
  have h := ((hA.mul (hψ.mul hv)).sub (hB.mul (hu.mul hy))).add
    (((hasDerivAt_betaM hD).mul (hasDerivAt_pP ξ)).mul (hψ.mul hy))
  refine h.congr_deriv ?_
  have hq : qP c χ' ξ = (DM c χ w ξ + pP ξ * w) / ξ ^ 2 + (χ - χ') := by
    unfold DM qP; field_simp; ring
  unfold greenRho gEdge
  rw [← alphaM_add_eq hD hξ0, hq]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- **The edge Green identity with a mismatch**: `∫₁^b ψy = W(b) − ∫₁^b ψρ − (χ − χ')∫₁^b ψ(ξ²/D)y`. -/
theorem integral_mul_eq_greenW_mis {c χ χ' w b : ℝ} {ψ u y v : ℝ → ℝ} (hb : 1 ≤ b) (hχ : χ < c ^ 2)
    (hw : w ≤ c ^ 2) (hψc : ContinuousOn ψ (Icc 1 b)) (huc : ContinuousOn u (Icc 1 b)) (hu1 : u 1 = 0)
    (hψ : ∀ ξ ∈ Ioo 1 b, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioo 1 b, HasDerivAt u (-(qP c χ' ξ * ψ ξ)) ξ)
    (hy : ∀ ξ ∈ Icc 1 b, HasDerivAt y (v ξ / ξ ^ 2) ξ) (hv : ∀ ξ ∈ Icc 1 b, HasDerivAt v (-(w * y ξ)) ξ) :
    ∫ ξ in (1 : ℝ)..b, ψ ξ * y ξ
      = greenW c χ w ψ u y v b - (∫ ξ in (1 : ℝ)..b, ψ ξ * greenRho c χ w y v ξ)
        - (χ - χ') * ∫ ξ in (1 : ℝ)..b, ψ ξ * (ξ ^ 2 / DM c χ w ξ * y ξ) := by
  have hD : ∀ ξ ∈ Icc (1 : ℝ) b, 0 < DM c χ w ξ := fun ξ hξ => DM_pos_of_le hχ hw hξ.1
  have hyc : ContinuousOn y (Icc 1 b) := fun ξ hξ => (hy ξ hξ).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc 1 b) := fun ξ hξ => (hv ξ hξ).continuousAt.continuousWithinAt
  have hDc : ContinuousOn (DM c χ w) (Icc 1 b) := (continuous_DM c χ w).continuousOn
  have hDne : ∀ ξ ∈ Icc (1 : ℝ) b, DM c χ w ξ ≠ 0 := fun ξ hξ => (hD ξ hξ).ne'
  have hp : ContinuousOn pP (Icc 1 b) := Continuous.continuousOn (by unfold pP; fun_prop)
  have hβ : ContinuousOn (betaM c χ w) (Icc 1 b) := continuousOn_betaM hD
  have hρ := continuousOn_greenRho hχ hw hyc hvc
  have hh : ContinuousOn (fun ξ => ξ ^ 2 / DM c χ w ξ * y ξ) (Icc 1 b) :=
    (((continuousOn_id.pow 2).div hDc hDne)).mul hyc
  have hWc : ContinuousOn (greenW c χ w ψ u y v) (Icc 1 b) := by
    unfold greenW
    exact (((hp.div hDc hDne).mul (hψc.mul hvc)).sub (((continuousOn_id.pow 2).div hDc hDne).mul
      (huc.mul hyc))).add ((hβ.mul hp).mul (hψc.mul hyc))
  have hW1 : greenW c χ w ψ u y v 1 = 0 := by unfold greenW pP; simp [hu1]
  have i1 : IntervalIntegrable (fun ξ => ψ ξ * y ξ) MeasureTheory.volume 1 b :=
    (hψc.mul hyc).intervalIntegrable_of_Icc hb
  have i2 : IntervalIntegrable (fun ξ => ψ ξ * greenRho c χ w y v ξ) MeasureTheory.volume 1 b :=
    (hψc.mul hρ).intervalIntegrable_of_Icc hb
  have i3 : IntervalIntegrable (fun ξ => ψ ξ * (ξ ^ 2 / DM c χ w ξ * y ξ)) MeasureTheory.volume 1 b :=
    (hψc.mul hh).intervalIntegrable_of_Icc hb
  have hftc := integral_eq_sub_of_hasDerivAt_of_le hb hWc
    (fun ξ hξ => hasDerivAt_greenW_mis hξ.1 (hDne ξ (Ioo_subset_Icc_self hξ)) (hψ ξ hξ) (hu ξ hξ)
      (hy ξ (Ioo_subset_Icc_self hξ)) (hv ξ (Ioo_subset_Icc_self hξ)))
    (((hψc.mul (hyc.add hρ)).add (continuousOn_const.mul (hψc.mul hh))).intervalIntegrable_of_Icc hb)
  rw [hW1, sub_zero] at hftc
  have e : ∫ ξ in (1 : ℝ)..b, (ψ ξ * (y ξ + greenRho c χ w y v ξ)
        + (χ - χ') * (ψ ξ * (ξ ^ 2 / DM c χ w ξ * y ξ)))
      = (∫ ξ in (1 : ℝ)..b, ψ ξ * y ξ) + (∫ ξ in (1 : ℝ)..b, ψ ξ * greenRho c χ w y v ξ)
        + (χ - χ') * ∫ ξ in (1 : ℝ)..b, ψ ξ * (ξ ^ 2 / DM c χ w ξ * y ξ) := by
    simp_rw [mul_add]
    rw [integral_add (i1.add i2) (i3.const_mul _), integral_add i1 i2, integral_const_mul]
  rw [e] at hftc
  rw [sub_sub, eq_sub_iff_add_eq, ← add_assoc]
  exact hftc

/-- `D ≥ ξ²(σ² + p(c² − w))` on `ξ ≥ 1` for `0 ≤ w`. -/
theorem DM_ge {c χ w ξ : ℝ} (hw0 : 0 ≤ w) (hξ : 1 ≤ ξ) :
    ξ ^ 2 * ((c ^ 2 - χ) + pP ξ * (c ^ 2 - w)) ≤ DM c χ w ξ := by
  have e : DM c χ w ξ - ξ ^ 2 * ((c ^ 2 - χ) + pP ξ * (c ^ 2 - w)) = pP ξ * w * (ξ ^ 2 - 1) := by
    unfold DM pP qP; ring
  have hp : 0 ≤ pP ξ := by unfold pP; nlinarith
  have : 0 ≤ pP ξ * w * (ξ ^ 2 - 1) := by
    have : 0 ≤ ξ ^ 2 - 1 := by nlinarith
    positivity
  linarith

/-- **The multiplier norm**: `∫₁² (ξ²/D)²/ξ ≤ 1/(2(c² − w)(c² − χ))` for `χ < c²`, `0 ≤ w < c²`. -/
theorem integral_mult_sq_le {c χ w : ℝ} (hχ : χ < c ^ 2) (hw0 : 0 ≤ w) (hw : w < c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, (ξ ^ 2 / DM c χ w ξ) ^ 2 / ξ ≤ 1 / (2 * (c ^ 2 - w) * (c ^ 2 - χ)) := by
  set σ2 := c ^ 2 - χ with hσ2
  set k := c ^ 2 - w with hk
  have hσ0 : 0 < σ2 := by rw [hσ2]; linarith
  have hk0 : 0 < k := by rw [hk]; linarith
  have hDp : ∀ ξ ∈ Icc (1 : ℝ) 2, 0 < σ2 + pP ξ * k := fun ξ hξ => by
    have : 0 ≤ pP ξ := by unfold pP; nlinarith [hξ.1]
    positivity
  -- pointwise: (ξ²/D)²/ξ ≤ ξ/(σ² + pk)²
  have hpt : ∀ ξ ∈ Icc (1 : ℝ) 2, (ξ ^ 2 / DM c χ w ξ) ^ 2 / ξ ≤ ξ / (σ2 + pP ξ * k) ^ 2 := by
    intro ξ hξ
    have hξ1 : 1 ≤ ξ := hξ.1
    have hξ0 : 0 < ξ := by linarith
    have hge := DM_ge (c := c) (χ := χ) hw0 hξ1
    rw [← hσ2, ← hk] at hge
    have hb := hDp ξ hξ
    have hDpos : 0 < DM c χ w ξ := lt_of_lt_of_le (by positivity) hge
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (ξ ^ 2 * (σ2 + pP ξ * k)) ^ 2 ≤ DM c χ w ξ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hge 2
    calc (ξ ^ 2) ^ 2 * (σ2 + pP ξ * k) ^ 2 = ξ ^ 4 * (σ2 + pP ξ * k) ^ 2 := by ring
      _ ≤ ξ ^ 4 * (σ2 + pP ξ * k) ^ 2 * ξ ^ 2 := by
          have : 0 ≤ ξ ^ 4 * (σ2 + pP ξ * k) ^ 2 := by positivity
          exact le_mul_of_one_le_right this (by nlinarith)
      _ = ξ * (ξ * (ξ ^ 2 * (σ2 + pP ξ * k)) ^ 2) := by ring
      _ ≤ ξ * (ξ * DM c χ w ξ ^ 2) := by gcongr
      _ = ξ * (DM c χ w ξ ^ 2 * ξ) := by ring
  -- the antiderivative of ξ/(σ² + pk)² is −1/(2k(σ² + pk))
  have hF : ∀ ξ ∈ uIcc (1 : ℝ) 2, HasDerivAt (fun r => -(1 / (2 * k * (σ2 + pP r * k))))
      (ξ / (σ2 + pP ξ * k) ^ 2) ξ := by
    intro ξ hξ
    rw [uIcc_of_le (by norm_num)] at hξ
    have hb := hDp ξ hξ
    have hd : HasDerivAt (fun r => 2 * k * (σ2 + pP r * k)) (2 * k * (2 * ξ * k)) ξ := by
      have := (((hasDerivAt_pP ξ).mul_const k).const_add σ2).const_mul (2 * k)
      exact this
    have := ((hd.inv (by positivity)).neg)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp
    · filter_upwards with r; simp [one_div]
  have hcont : ContinuousOn (fun ξ => ξ / (σ2 + pP ξ * k) ^ 2) (Icc 1 2) :=
    have hc' : Continuous fun ξ => (σ2 + pP ξ * k) ^ 2 := by unfold pP; fun_prop
    continuousOn_id.div₀ hc'.continuousOn fun ξ hξ => by
      have := hDp ξ hξ; positivity
  have hI : ∫ ξ in (1 : ℝ)..2, ξ / (σ2 + pP ξ * k) ^ 2
      = 1 / (2 * k * σ2) - 1 / (2 * k * (σ2 + 3 * k)) := by
    rw [integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable_of_Icc (by norm_num))]
    unfold pP; norm_num; ring
  have hcont2 : ContinuousOn (fun ξ => (ξ ^ 2 / DM c χ w ξ) ^ 2 / ξ) (Icc 1 2) := by
    refine ContinuousOn.div (ContinuousOn.pow ((continuousOn_id.pow 2).div (continuous_DM c χ w).continuousOn
      fun ξ hξ => ?_) 2) continuousOn_id fun ξ hξ => by linarith [hξ.1]
    have := DM_ge (c := c) (χ := χ) hw0 hξ.1
    have := hDp ξ hξ
    have : 0 < ξ ^ 2 := by nlinarith [hξ.1]
    exact (lt_of_lt_of_le (by positivity) (DM_ge (c := c) (χ := χ) hw0 hξ.1)).ne'
  calc ∫ ξ in (1 : ℝ)..2, (ξ ^ 2 / DM c χ w ξ) ^ 2 / ξ ≤ ∫ ξ in (1 : ℝ)..2, ξ / (σ2 + pP ξ * k) ^ 2 :=
        integral_mono_on (by norm_num) (hcont2.intervalIntegrable_of_Icc (by norm_num))
          (hcont.intervalIntegrable_of_Icc (by norm_num)) hpt
    _ = 1 / (2 * k * σ2) - 1 / (2 * k * (σ2 + 3 * k)) := hI
    _ ≤ 1 / (2 * k * σ2) := by
        have : 0 ≤ 1 / (2 * k * (σ2 + 3 * k)) := by positivity
        linarith
    _ = 1 / (2 * (c ^ 2 - w) * (c ^ 2 - χ)) := by rw [hk, hσ2]

/-- The mismatch multiplier against `ξ^{−1/2−it}`: `h_t = (ξ²/D)(y_t − iỹ_t)`, `w = t² + ¼`. -/
noncomputable def hEdge (c χ t ξ : ℝ) : ℂ :=
  ((ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * ky t ξ : ℝ) : ℂ)
    - Complex.I * ((ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * kys t ξ : ℝ) : ℂ)

/-- `‖h_t‖² = (ξ²/D)²/ξ`. -/
theorem norm_hEdge_sq (c χ t : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖hEdge c χ t ξ‖ ^ 2 = (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ) ^ 2 / ξ := by
  have hk : ky t ξ ^ 2 + kys t ξ ^ 2 = 1 / ξ := by
    unfold ky kys
    rw [div_pow, div_pow, Real.sq_sqrt hξ.le, ← add_div, Real.cos_sq_add_sin_sq]
  have e : hEdge c χ t ξ = ((ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * ky t ξ : ℝ) : ℂ)
      + ((-(ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * kys t ξ) : ℝ) : ℂ) * Complex.I := by
    unfold hEdge; push_cast; ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h2 : (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * ky t ξ) ^ 2 + (-(ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * kys t ξ)) ^ 2
      = (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ) ^ 2 * (ky t ξ ^ 2 + kys t ξ ^ 2) := by ring
  rw [h2, hk]; ring

/-- **The edge Green identity against `ξ^{−1/2−it}` with a mismatch**: for a rung at `χ'` and the multiplier at
`χ < c²`, `I(1, b; t) = W(b) − ∫₁^b ψρ_t − (χ − χ')∫₁^b ψh_t`. -/
theorem mellinI_one_eq_mis {g g₁ g₂ : ℝ → ℝ} {c χ χ' b t : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ' * g s = 0)
    (hb : 1 ≤ b) (hχ : χ < c ^ 2) (hw : t ^ 2 + 1 / 4 ≤ c ^ 2) :
    Cvs.L2a.FarPartDirichletSplit.mellinI (psi c g) 1 b t
      = greenWC c χ t (psi c g) (rungU c g) b - (∫ ξ in (1 : ℝ)..b, (psi c g ξ : ℂ) * rhoEdge c χ t ξ)
        - ((χ - χ' : ℝ) : ℂ) * ∫ ξ in (1 : ℝ)..b, (psi c g ξ : ℂ) * hEdge c χ t ξ := by
  obtain ⟨hψ, hu, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  have hpos : ∀ ξ ∈ Icc (1 : ℝ) b, 0 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hy1 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (ky t) (ku t ξ / ξ ^ 2) ξ := fun ξ hξ => hasDerivAt_ky (hpos ξ hξ)
  have hv1 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (ku t) (-((t ^ 2 + 1 / 4) * ky t ξ)) ξ :=
    fun ξ hξ => hasDerivAt_ku (hpos ξ hξ)
  have hy2 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (kys t) (kus t ξ / ξ ^ 2) ξ :=
    fun ξ hξ => hasDerivAt_kys (hpos ξ hξ)
  have hv2 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (kus t) (-((t ^ 2 + 1 / 4) * kys t ξ)) ξ :=
    fun ξ hξ => hasDerivAt_kus (hpos ξ hξ)
  have hcos := integral_mul_eq_greenW_mis (χ' := χ') hb hχ hw hψc.continuousOn huc.continuousOn
    (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g) (fun ξ hξ => hψ ξ hξ.1) (fun ξ _ => hu ξ) hy1 hv1
  have hsin := integral_mul_eq_greenW_mis (χ' := χ') hb hχ hw hψc.continuousOn huc.continuousOn
    (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g) (fun ξ hξ => hψ ξ hξ.1) (fun ξ _ => hu ξ) hy2 hv2
  have hD : ∀ ξ ∈ Icc (1 : ℝ) b, DM c χ (t ^ 2 + 1 / 4) ξ ≠ 0 := fun ξ hξ => (DM_pos_of_le hχ hw hξ.1).ne'
  have hDc : ContinuousOn (DM c χ (t ^ 2 + 1 / 4)) (Icc 1 b) := (continuous_DM c χ _).continuousOn
  have cont : ∀ {y v : ℝ → ℝ}, (∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt y (v ξ / ξ ^ 2) ξ) →
      (∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt v (-((t ^ 2 + 1 / 4) * y ξ)) ξ) →
      ContinuousOn (fun ξ => psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) y v ξ) (Icc 1 b) :=
    fun hy hv => hψc.continuousOn.mul (continuousOn_greenRho hχ hw
      (fun ξ hξ => (hy ξ hξ).continuousAt.continuousWithinAt)
      (fun ξ hξ => (hv ξ hξ).continuousAt.continuousWithinAt))
  have contH : ∀ {y : ℝ → ℝ}, ContinuousOn y (Icc 1 b) →
      ContinuousOn (fun ξ => psi c g ξ * (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * y ξ)) (Icc 1 b) :=
    fun hy => hψc.continuousOn.mul (((continuousOn_id.pow 2).div hDc hD).mul hy)
  have cy1 : ContinuousOn (ky t) (Icc 1 b) := fun ξ hξ => (hy1 ξ hξ).continuousAt.continuousWithinAt
  have cy2 : ContinuousOn (kys t) (Icc 1 b) := fun ξ hξ => (hy2 ξ hξ).continuousAt.continuousWithinAt
  have i1 : IntervalIntegrable (fun ξ => ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (ky t) (ku t) ξ : ℝ) : ℂ))
      MeasureTheory.volume 1 b :=
    (Complex.continuous_ofReal.comp_continuousOn (cont hy1 hv1)).intervalIntegrable_of_Icc hb
  have i2 : IntervalIntegrable (fun ξ => Complex.I
      * ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (kys t) (kus t) ξ : ℝ) : ℂ)) MeasureTheory.volume 1 b :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (cont hy2 hv2))).intervalIntegrable_of_Icc hb
  have j1 : IntervalIntegrable
      (fun ξ => ((psi c g ξ * (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * ky t ξ) : ℝ) : ℂ)) MeasureTheory.volume 1 b :=
    (Complex.continuous_ofReal.comp_continuousOn (contH cy1)).intervalIntegrable_of_Icc hb
  have j2 : IntervalIntegrable (fun ξ => Complex.I
      * ((psi c g ξ * (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * kys t ξ) : ℝ) : ℂ)) MeasureTheory.volume 1 b :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (contH cy2))).intervalIntegrable_of_Icc hb
  have e : (fun ξ => (psi c g ξ : ℂ) * rhoEdge c χ t ξ)
      = fun ξ => ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (ky t) (ku t) ξ : ℝ) : ℂ)
        - Complex.I * ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (kys t) (kus t) ξ : ℝ) : ℂ) := by
    funext ξ; unfold rhoEdge; push_cast; ring
  have eh : (fun ξ => (psi c g ξ : ℂ) * hEdge c χ t ξ)
      = fun ξ => ((psi c g ξ * (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * ky t ξ) : ℝ) : ℂ)
        - Complex.I * ((psi c g ξ * (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * kys t ξ) : ℝ) : ℂ) := by
    funext ξ; unfold hEdge; push_cast; ring
  rw [e, eh, integral_sub i1 i2, integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, integral_sub j1 j2, integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  unfold Cvs.L2a.FarPartDirichletSplit.mellinI greenWC
  rw [hcos, hsin]; push_cast; ring

/-- **The boundary at `ξ = 2` with a mismatch**: the multiplier at `χ ∈ [0, c²]`, the energy at any `χ' ∈ [0, c²]`:
`‖W(2)‖² ≤ E_{χ'}(2)ω₂²/(6c³)`. -/
theorem norm_greenWC_two_sq_le_mis {c χ χ' r t : ℝ} (ψ u : ℝ → ℝ) (hc : 0 < c) (hχ : χ ≤ c ^ 2)
    (hχ'0 : 0 ≤ χ') (hχ' : χ' ≤ c ^ 2) (hr : r < 4) (hw : t ^ 2 + 1 / 4 ≤ r * c ^ 2) :
    ‖greenWC c χ t ψ u 2‖ ^ 2 ≤ energy (aP c χ') ψ u 2 * omega2Sq c r / (6 * c ^ 3) := by
  obtain ⟨w, hwd⟩ : ∃ w, w = t ^ 2 + 1 / 4 := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = DM c χ w 2 := ⟨_, rfl⟩
  obtain ⟨n, hnd⟩ : ∃ n, n = -(3 * betaM c χ w 2) := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : ℂ, P₁ = ((3 / D * ku t 2 - n * ky t 2 : ℝ) : ℂ)
      - Complex.I * ((3 / D * kus t 2 - n * kys t 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : ℂ, Q₁ = ((0 * ku t 2 - -(4 / D) * ky t 2 : ℝ) : ℂ)
      - Complex.I * ((0 * kus t 2 - -(4 / D) * kys t 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hW : greenWC c χ t ψ u 2 = (ψ 2 : ℂ) * P₁ - (u 2 : ℂ) * Q₁ := by
    rw [hP₁, hQ₁, hnd, hDd, hwd]; unfold greenWC greenW pP; push_cast; ring
  have hP2 : ‖P₁‖ ^ 2 = (3 / D) ^ 2 * (2 * w) + 3 / D * n + n ^ 2 / 2 := by
    rw [hP₁, norm_pair_sq t (3 / D) n two_pos, hwd]
  have hQ2 : ‖Q₁‖ ^ 2 = (4 / D) ^ 2 / 2 := by
    rw [hQ₁, norm_pair_sq t 0 (-(4 / D)) two_pos]; ring
  have hT : ‖greenWC c χ t ψ u 2‖ ≤ |ψ 2| * ‖P₁‖ + |u 2| * ‖Q₁‖ := by
    rw [hW]; refine (norm_sub_le _ _).trans_eq ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  -- the amplitude at the rung's `χ'`: `a(2)² = 3(4c² − χ') ∈ [9c², 12c²]`
  have ha2 : aP c χ' 2 ^ 2 = 3 * (4 * c ^ 2 - χ') := by
    unfold aP; rw [Real.sq_sqrt (by unfold pP qP; nlinarith)]; unfold pP qP; ring
  have ha0 : 0 ≤ aP c χ' 2 := Real.sqrt_nonneg _
  have haL : 3 * c ≤ aP c χ' 2 :=
    (pow_le_pow_iff_left₀ (by positivity) ha0 two_ne_zero).mp (by rw [ha2]; nlinarith)
  have hapos : 0 < aP c χ' 2 := by linarith
  have haU : aP c χ' 2 ≤ 2 * √3 * c := by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine (pow_le_pow_iff_left₀ ha0 (by positivity) two_ne_zero).mp ?_
    rw [ha2, mul_pow, mul_pow, h3]; nlinarith
  -- the mismatch `D(2) ≥ 3(4 − r)c²` at the multiplier's `χ`
  have hw4 : 1 / 4 ≤ w := by rw [hwd]; nlinarith [sq_nonneg t]
  have hwr : w ≤ r * c ^ 2 := by rw [hwd]; exact hw
  have hDge : 3 * (4 - r) * c ^ 2 ≤ D := by rw [hDd]; unfold DM qP pP; nlinarith
  have hn : n = 12 * (16 * c ^ 2 - w) / D ^ 2 := by rw [hnd, hDd]; unfold betaM; ring
  have hwc : w ≤ 16 * c ^ 2 := by nlinarith
  have hn0 : 0 ≤ n := by rw [hn]; exact div_nonneg (by linarith) (sq_nonneg _)
  have hnle : n ≤ 192 * c ^ 2 / D ^ 2 := by
    rw [hn]; exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  obtain ⟨m, hmd⟩ : ∃ m, m = √w := ⟨_, rfl⟩
  have hm2 : m ^ 2 = w := by rw [hmd, Real.sq_sqrt (by linarith)]
  have hm : 1 / 2 ≤ m := by
    rw [hmd, show (1 / 2 : ℝ) = √(1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hw4
  have hmr : m ≤ √r * c := by
    rw [hmd, ← Real.sqrt_sq hc.le, ← Real.sqrt_mul' r (sq_nonneg c)]; exact Real.sqrt_le_sqrt hwr
  have hcoef := edge_coeff_le hc hr hDge haL haU hm hmr hn0 hnle
  rw [hm2, ← hP2, ← hQ2] at hcoef
  have hE0 : 0 ≤ energy (aP c χ') ψ u 2 := by unfold energy; positivity
  calc ‖greenWC c χ t ψ u 2‖ ^ 2 ≤ (|ψ 2| * ‖P₁‖ + |u 2| * ‖Q₁‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hT 2
    _ ≤ energy (aP c χ') ψ u 2 * (‖P₁‖ ^ 2 / aP c χ' 2 + aP c χ' 2 * ‖Q₁‖ ^ 2) := sq_add_le_energy_mul hapos
    _ ≤ energy (aP c χ') ψ u 2 * (omega2Sq c r / (6 * c ^ 3)) := mul_le_mul_of_nonneg_left hcoef hE0
    _ = _ := by ring

end Cvs.Prolate.Mellin.EdgeGreenMismatch
