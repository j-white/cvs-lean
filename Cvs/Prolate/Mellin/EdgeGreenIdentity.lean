import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.Prolate.ProlateWindowMassIdentity
import Cvs.WeilForm.OddPoleTermBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge Green identity against the Mellin kernel

For a rung (`ψ' = u/p`, `u' = −qψ`, `u(1) = 0`) and a Mellin pair (`y' = v/ξ²`, `v' = −wy`) with `χ < c²`,
`w ≤ c²`, `W = pψh' − uh`, `h = (ξ²/D)y`, has `W' = ψ(y + ρ)`, `ρ = (pA')'y + (2pA' + 2A/ξ)y'`, `A = ξ²/D`,
and `W(1) = 0`; so `I(1, b; t) = W(b) − ∫₁^b ψρ_t`, and at `b = 2`, `‖W(2)‖² ≤ E(2)ω₂²/(6c³)`.
-/

namespace Cvs.Prolate.Mellin.EdgeGreenIdentity

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.GreenBoundaryBound

/-- `β'` for `β = (ξ²/D)' = −2ξ(c²ξ⁴ − w)/D²`. -/
noncomputable def dbetaM (c χ w ξ : ℝ) : ℝ :=
  -(2 * (5 * c ^ 2 * ξ ^ 4 - w)) / DM c χ w ξ ^ 2
    + 4 * ξ * (c ^ 2 * ξ ^ 4 - w) * dDM c χ w ξ / DM c χ w ξ ^ 3

/-- `g = (pA')'` with `A = ξ²/D`, so `pA' = pβ`. -/
noncomputable def gEdge (c χ w ξ : ℝ) : ℝ := 2 * ξ * betaM c χ w ξ + pP ξ * dbetaM c χ w ξ

/-- `f = 2pA' + 2A/ξ = 2pβ + 2ξ/D`. -/
noncomputable def fEdge (c χ w ξ : ℝ) : ℝ := 2 * pP ξ * betaM c χ w ξ + 2 * ξ / DM c χ w ξ

/-- `W = pψh' − uh`, `h = (ξ²/D)y`, for a Mellin pair `y' = v/ξ²`, `v' = −wy`. -/
noncomputable def greenW (c χ w : ℝ) (ψ u y v : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  pP ξ / DM c χ w ξ * (ψ ξ * v ξ) - ξ ^ 2 / DM c χ w ξ * (u ξ * y ξ) + betaM c χ w ξ * pP ξ * (ψ ξ * y ξ)

/-- `ρ = g y + f y'` for a Mellin pair, `y' = v/ξ²`. -/
noncomputable def greenRho (c χ w : ℝ) (y v : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  gEdge c χ w ξ * y ξ + fEdge c χ w ξ / ξ ^ 2 * v ξ

/-- `W` against `ξ^{−1/2−it}`: `W(y_t, u_t) − i W(ỹ_t, ũ_t)`, `w = t² + ¼`. -/
noncomputable def greenWC (c χ t : ℝ) (ψ u : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  (greenW c χ (t ^ 2 + 1 / 4) ψ u (ky t) (ku t) ξ : ℂ)
    - Complex.I * (greenW c χ (t ^ 2 + 1 / 4) ψ u (kys t) (kus t) ξ : ℂ)

/-- `ρ_t = ρ(y_t, u_t) − i ρ(ỹ_t, ũ_t)`. -/
noncomputable def rhoEdge (c χ t ξ : ℝ) : ℂ :=
  (greenRho c χ (t ^ 2 + 1 / 4) (ky t) (ku t) ξ : ℂ)
    - Complex.I * (greenRho c χ (t ^ 2 + 1 / 4) (kys t) (kus t) ξ : ℂ)

/-- The boundary constant `ω₂² = (2√r/(4 − r) + 64/(3(4 − r)²c))² + 32√3/(3(4 − r)²)`. -/
noncomputable def omega2Sq (c r : ℝ) : ℝ :=
  (2 * √r / (4 - r) + 64 / (3 * (4 - r) ^ 2 * c)) ^ 2 + 32 * √3 / (3 * (4 - r) ^ 2)

theorem hasDerivAt_betaM {c χ w ξ : ℝ} (hD : DM c χ w ξ ≠ 0) :
    HasDerivAt (betaM c χ w) (dbetaM c χ w ξ) ξ := by
  have hn : HasDerivAt (fun r => -(2 * r * (c ^ 2 * r ^ 4 - w))) (-(2 * (5 * c ^ 2 * ξ ^ 4 - w))) ξ := by
    have := (((hasDerivAt_id' ξ).const_mul 2).mul (((hasDerivAt_pow 4 ξ).const_mul (c ^ 2)).sub_const w)).neg
    refine this.congr_deriv ?_; push_cast; ring
  have hd : HasDerivAt (fun r => DM c χ w r ^ 2) (2 * DM c χ w ξ * dDM c χ w ξ) ξ := by
    refine ((hasDerivAt_DM c χ w ξ).pow 2).congr_deriv ?_; push_cast; ring
  refine (hn.div hd (pow_ne_zero 2 hD)).congr_deriv ?_
  unfold dbetaM; field_simp; ring

theorem alphaM_add_eq {c χ w ξ : ℝ} (hD : DM c χ w ξ ≠ 0) (hξ : ξ ≠ 0) :
    alphaM c χ w ξ + pP ξ * betaM c χ w ξ / ξ ^ 2 = fEdge c χ w ξ / ξ ^ 2 := by
  unfold fEdge alphaM betaM; field_simp; unfold DM pP qP; ring

/-- `D = (c² − χ)ξ² + p(c²ξ² − w) > 0` on `ξ ≥ 1` for `χ < c²`, `w ≤ c²`. -/
theorem DM_pos_of_le {c χ w ξ : ℝ} (hχ : χ < c ^ 2) (hw : w ≤ c ^ 2) (hξ : 1 ≤ ξ) : 0 < DM c χ w ξ := by
  have e : DM c χ w ξ = (c ^ 2 - χ) * ξ ^ 2 + pP ξ * (c ^ 2 * ξ ^ 2 - w) := by unfold DM pP qP; ring
  have hξ2 : 1 ≤ ξ ^ 2 := one_le_pow₀ hξ
  have h1 : 0 < (c ^ 2 - χ) * ξ ^ 2 := mul_pos (by linarith) (by linarith)
  have hp : 0 ≤ pP ξ := by unfold pP; linarith
  have h2 : 0 ≤ c ^ 2 * ξ ^ 2 - w := by nlinarith [mul_nonneg (sq_nonneg c) (by linarith : (0 : ℝ) ≤ ξ ^ 2 - 1)]
  rw [e]; nlinarith [mul_nonneg hp h2]

theorem hasDerivAt_greenW {c χ w ξ : ℝ} {ψ u y v : ℝ → ℝ} (hξ : 1 < ξ) (hD : DM c χ w ξ ≠ 0)
    (hψ : HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hy : HasDerivAt y (v ξ / ξ ^ 2) ξ) (hv : HasDerivAt v (-(w * y ξ)) ξ) :
    HasDerivAt (greenW c χ w ψ u y v) (ψ ξ * (y ξ + greenRho c χ w y v ξ)) ξ := by
  have hp : pP ξ ≠ 0 := (pP_pos hξ).ne'
  have hξ0 : ξ ≠ 0 := by positivity
  have hA : HasDerivAt (fun r => pP r / DM c χ w r) (alphaM c χ w ξ) ξ := by
    have := hasDerivAt_pdivD (w := w) hD; simp only [one_mul] at this; exact this
  have hB : HasDerivAt (fun r => r ^ 2 / DM c χ w r) (betaM c χ w ξ) ξ := by
    have := hasDerivAt_sqdivD (w := w) hD; simp only [one_mul] at this; exact this
  have h := ((hA.mul (hψ.mul hv)).sub (hB.mul (hu.mul hy))).add
    (((hasDerivAt_betaM hD).mul (hasDerivAt_pP ξ)).mul (hψ.mul hy))
  refine h.congr_deriv ?_
  have hq : qP c χ ξ = (DM c χ w ξ + pP ξ * w) / ξ ^ 2 := by
    unfold DM; field_simp; ring
  unfold greenRho gEdge
  rw [← alphaM_add_eq hD hξ0, hq]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- `ρ` is continuous on `[1, b]` for `y`, `v` continuous there, `χ < c²`, `w ≤ c²`. -/
theorem continuousOn_greenRho {c χ w b : ℝ} {y v : ℝ → ℝ} (hχ : χ < c ^ 2) (hw : w ≤ c ^ 2)
    (hyc : ContinuousOn y (Icc 1 b)) (hvc : ContinuousOn v (Icc 1 b)) :
    ContinuousOn (greenRho c χ w y v) (Icc 1 b) := by
  have hD : ∀ ξ ∈ Icc (1 : ℝ) b, DM c χ w ξ ≠ 0 := fun ξ hξ => (DM_pos_of_le hχ hw hξ.1).ne'
  have hDc : ContinuousOn (DM c χ w) (Icc 1 b) := (continuous_DM c χ w).continuousOn
  have hdD : ContinuousOn (dDM c χ w) (Icc 1 b) := Continuous.continuousOn (by unfold dDM qP; fun_prop)
  have hp : ContinuousOn pP (Icc 1 b) := Continuous.continuousOn (by unfold pP; fun_prop)
  have hβ : ContinuousOn (betaM c χ w) (Icc 1 b) := by
    unfold betaM
    exact ContinuousOn.div (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun ξ : ℝ => -(2 * ξ * (c ^ 2 * ξ ^ 4 - w))) _) (hDc.pow 2)
      fun ξ hξ => pow_ne_zero 2 (hD ξ hξ)
  have hdβ : ContinuousOn (dbetaM c χ w) (Icc 1 b) := by
    unfold dbetaM
    refine ContinuousOn.add (ContinuousOn.div (Continuous.continuousOn (by fun_prop) :
      ContinuousOn (fun ξ : ℝ => -(2 * (5 * c ^ 2 * ξ ^ 4 - w))) _) (hDc.pow 2)
      fun ξ hξ => pow_ne_zero 2 (hD ξ hξ)) (ContinuousOn.div ?_ (hDc.pow 3) fun ξ hξ => pow_ne_zero 3 (hD ξ hξ))
    exact (Continuous.continuousOn (by fun_prop) :
      ContinuousOn (fun ξ : ℝ => 4 * ξ * (c ^ 2 * ξ ^ 4 - w)) _).mul hdD
  have hsq : ∀ ξ ∈ Icc (1 : ℝ) b, ξ ^ 2 ≠ 0 := fun ξ hξ => pow_ne_zero 2 (by linarith [hξ.1])
  have hg : ContinuousOn (gEdge c χ w) (Icc 1 b) := by
    unfold gEdge
    exact ((continuousOn_const.mul continuousOn_id).mul hβ).add (hp.mul hdβ)
  have hf : ContinuousOn (fEdge c χ w) (Icc 1 b) := by
    unfold fEdge
    exact ((continuousOn_const.mul hp).mul hβ).add ((continuousOn_const.mul continuousOn_id).div hDc hD)
  unfold greenRho
  exact (hg.mul hyc).add ((hf.div (continuousOn_id.pow 2) hsq).mul hvc)

/-- **The edge Green identity**: `∫₁^b ψy = W(b) − ∫₁^b ψρ`, with no boundary term at `1`. -/
theorem integral_mul_eq_greenW {c χ w b : ℝ} {ψ u y v : ℝ → ℝ} (hb : 1 ≤ b) (hχ : χ < c ^ 2)
    (hw : w ≤ c ^ 2) (hψc : ContinuousOn ψ (Icc 1 b)) (huc : ContinuousOn u (Icc 1 b)) (hu1 : u 1 = 0)
    (hψ : ∀ ξ ∈ Ioo 1 b, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioo 1 b, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hy : ∀ ξ ∈ Icc 1 b, HasDerivAt y (v ξ / ξ ^ 2) ξ) (hv : ∀ ξ ∈ Icc 1 b, HasDerivAt v (-(w * y ξ)) ξ) :
    ∫ ξ in (1 : ℝ)..b, ψ ξ * y ξ
      = greenW c χ w ψ u y v b - ∫ ξ in (1 : ℝ)..b, ψ ξ * greenRho c χ w y v ξ := by
  have hD : ∀ ξ ∈ Icc (1 : ℝ) b, 0 < DM c χ w ξ := fun ξ hξ => DM_pos_of_le hχ hw hξ.1
  have hyc : ContinuousOn y (Icc 1 b) := fun ξ hξ => (hy ξ hξ).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc 1 b) := fun ξ hξ => (hv ξ hξ).continuousAt.continuousWithinAt
  have hDc : ContinuousOn (DM c χ w) (Icc 1 b) := (continuous_DM c χ w).continuousOn
  have hDne : ∀ ξ ∈ Icc (1 : ℝ) b, DM c χ w ξ ≠ 0 := fun ξ hξ => (hD ξ hξ).ne'
  have hp : ContinuousOn pP (Icc 1 b) := Continuous.continuousOn (by unfold pP; fun_prop)
  have hβ : ContinuousOn (betaM c χ w) (Icc 1 b) := continuousOn_betaM hD
  have hρ := continuousOn_greenRho hχ hw hyc hvc
  have hWc : ContinuousOn (greenW c χ w ψ u y v) (Icc 1 b) := by
    unfold greenW
    exact (((hp.div hDc hDne).mul (hψc.mul hvc)).sub (((continuousOn_id.pow 2).div hDc hDne).mul
      (huc.mul hyc))).add ((hβ.mul hp).mul (hψc.mul hyc))
  have hW1 : greenW c χ w ψ u y v 1 = 0 := by unfold greenW pP; simp [hu1]
  have i1 : IntervalIntegrable (fun ξ => ψ ξ * y ξ) MeasureTheory.volume 1 b :=
    (hψc.mul hyc).intervalIntegrable_of_Icc hb
  have i2 : IntervalIntegrable (fun ξ => ψ ξ * greenRho c χ w y v ξ) MeasureTheory.volume 1 b :=
    (hψc.mul hρ).intervalIntegrable_of_Icc hb
  have hftc := integral_eq_sub_of_hasDerivAt_of_le hb hWc
    (fun ξ hξ => hasDerivAt_greenW hξ.1 (hDne ξ (Ioo_subset_Icc_self hξ)) (hψ ξ hξ) (hu ξ hξ)
      (hy ξ (Ioo_subset_Icc_self hξ)) (hv ξ (Ioo_subset_Icc_self hξ)))
    ((hψc.mul (hyc.add hρ)).intervalIntegrable_of_Icc hb)
  rw [hW1, sub_zero] at hftc
  have e : ∫ ξ in (1 : ℝ)..b, ψ ξ * (y ξ + greenRho c χ w y v ξ)
      = (∫ ξ in (1 : ℝ)..b, ψ ξ * y ξ) + ∫ ξ in (1 : ℝ)..b, ψ ξ * greenRho c χ w y v ξ := by
    simp_rw [mul_add]; exact integral_add i1 i2
  rw [e] at hftc; linarith

/-- **The edge Green identity against `ξ^{−1/2−it}`**: `I(1, b; t) = W(b) − ∫₁^b ψρ_t` for a rung. -/
theorem mellinI_one_eq {g g₁ g₂ : ℝ → ℝ} {c χ b t : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hb : 1 ≤ b) (hχ : χ < c ^ 2) (hw : t ^ 2 + 1 / 4 ≤ c ^ 2) :
    Cvs.L2a.FarPartDirichletSplit.mellinI (psi c g) 1 b t
      = greenWC c χ t (psi c g) (rungU c g) b - ∫ ξ in (1 : ℝ)..b, (psi c g ξ : ℂ) * rhoEdge c χ t ξ := by
  obtain ⟨hψ, hu, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  have hpos : ∀ ξ ∈ Icc (1 : ℝ) b, 0 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hy1 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (ky t) (ku t ξ / ξ ^ 2) ξ := fun ξ hξ => hasDerivAt_ky (hpos ξ hξ)
  have hv1 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (ku t) (-((t ^ 2 + 1 / 4) * ky t ξ)) ξ :=
    fun ξ hξ => hasDerivAt_ku (hpos ξ hξ)
  have hy2 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (kys t) (kus t ξ / ξ ^ 2) ξ :=
    fun ξ hξ => hasDerivAt_kys (hpos ξ hξ)
  have hv2 : ∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt (kus t) (-((t ^ 2 + 1 / 4) * kys t ξ)) ξ :=
    fun ξ hξ => hasDerivAt_kus (hpos ξ hξ)
  have hcos := integral_mul_eq_greenW hb hχ hw hψc.continuousOn huc.continuousOn (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g)
    (fun ξ hξ => hψ ξ hξ.1) (fun ξ _ => hu ξ) hy1 hv1
  have hsin := integral_mul_eq_greenW hb hχ hw hψc.continuousOn huc.continuousOn (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g)
    (fun ξ hξ => hψ ξ hξ.1) (fun ξ _ => hu ξ) hy2 hv2
  have cont : ∀ {y v : ℝ → ℝ}, (∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt y (v ξ / ξ ^ 2) ξ) →
      (∀ ξ ∈ Icc (1 : ℝ) b, HasDerivAt v (-((t ^ 2 + 1 / 4) * y ξ)) ξ) →
      ContinuousOn (fun ξ => psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) y v ξ) (Icc 1 b) :=
    fun hy hv => hψc.continuousOn.mul (continuousOn_greenRho hχ hw
      (fun ξ hξ => (hy ξ hξ).continuousAt.continuousWithinAt)
      (fun ξ hξ => (hv ξ hξ).continuousAt.continuousWithinAt))
  have i1 : IntervalIntegrable (fun ξ => ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (ky t) (ku t) ξ : ℝ) : ℂ))
      MeasureTheory.volume 1 b :=
    (Complex.continuous_ofReal.comp_continuousOn (cont hy1 hv1)).intervalIntegrable_of_Icc hb
  have i2 : IntervalIntegrable (fun ξ => Complex.I
      * ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (kys t) (kus t) ξ : ℝ) : ℂ)) MeasureTheory.volume 1 b :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (cont hy2 hv2))).intervalIntegrable_of_Icc hb
  have e : (fun ξ => (psi c g ξ : ℂ) * rhoEdge c χ t ξ)
      = fun ξ => ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (ky t) (ku t) ξ : ℝ) : ℂ)
        - Complex.I * ((psi c g ξ * greenRho c χ (t ^ 2 + 1 / 4) (kys t) (kus t) ξ : ℝ) : ℂ) := by
    funext ξ; unfold rhoEdge; push_cast; ring
  rw [e, integral_sub i1 i2, integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  unfold Cvs.L2a.FarPartDirichletSplit.mellinI greenWC
  rw [hcos, hsin]; push_cast; ring

/-- `‖ρ_t‖² = g²/ξ + w f²/ξ³ − g f/ξ²`, `w = t² + ¼` (Cvs.Prolate.Mellin.GreenBoundaryBound.norm_pair_sq at `P = f/ξ²`, `Q = −g`). -/
theorem norm_rhoEdge_sq (c χ t : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖rhoEdge c χ t ξ‖ ^ 2
      = gEdge c χ (t ^ 2 + 1 / 4) ξ ^ 2 / ξ + (t ^ 2 + 1 / 4) * fEdge c χ (t ^ 2 + 1 / 4) ξ ^ 2 / ξ ^ 3
        - gEdge c χ (t ^ 2 + 1 / 4) ξ * fEdge c χ (t ^ 2 + 1 / 4) ξ / ξ ^ 2 := by
  have h := norm_pair_sq t (fEdge c χ (t ^ 2 + 1 / 4) ξ / ξ ^ 2) (-gEdge c χ (t ^ 2 + 1 / 4) ξ) hξ
  have e1 : greenRho c χ (t ^ 2 + 1 / 4) (ky t) (ku t) ξ
      = fEdge c χ (t ^ 2 + 1 / 4) ξ / ξ ^ 2 * ku t ξ - -gEdge c χ (t ^ 2 + 1 / 4) ξ * ky t ξ := by
    unfold greenRho; ring
  have e2 : greenRho c χ (t ^ 2 + 1 / 4) (kys t) (kus t) ξ
      = fEdge c χ (t ^ 2 + 1 / 4) ξ / ξ ^ 2 * kus t ξ - -gEdge c χ (t ^ 2 + 1 / 4) ξ * kys t ξ := by
    unfold greenRho; ring
  unfold rhoEdge; rw [e1, e2, h]; field_simp; ring

/-- The coefficient bound behind `ω₂`: with `D ≥ 3(4 − r)c²`, `a ∈ [3c, 2√3c]`, `½ ≤ m ≤ √r c` and
`0 ≤ n ≤ 192c²/D²`, `((3/D)²·2m² + (3/D)n + n²/2)/a + a(4/D)²/2 ≤ ω₂²/(6c³)`. -/
theorem edge_coeff_le {c r D a m n : ℝ} (hc : 0 < c) (hr : r < 4) (hD : 3 * (4 - r) * c ^ 2 ≤ D)
    (haL : 3 * c ≤ a) (haU : a ≤ 2 * √3 * c) (hm : 1 / 2 ≤ m) (hmr : m ≤ √r * c) (hn0 : 0 ≤ n)
    (hn : n ≤ 192 * c ^ 2 / D ^ 2) :
    ((3 / D) ^ 2 * (2 * m ^ 2) + 3 / D * n + n ^ 2 / 2) / a + a * ((4 / D) ^ 2 / 2)
      ≤ omega2Sq c r / (6 * c ^ 3) := by
  have h4r : 0 < 4 - r := by linarith
  have hD₀ : 0 < 3 * (4 - r) * c ^ 2 := by positivity
  have hDpos : 0 < D := lt_of_lt_of_le hD₀ hD
  have hA0 : 0 ≤ 3 / D := by positivity
  have hm0 : 0 ≤ m := by linarith
  have hmA : 2 * m * (3 / D) ≤ 2 * √r / ((4 - r) * c) := by
    calc 2 * m * (3 / D) = 6 * m / D := by ring
      _ ≤ 6 * m / (3 * (4 - r) * c ^ 2) := div_le_div_of_nonneg_left (by linarith) hD₀ hD
      _ ≤ 6 * (√r * c) / (3 * (4 - r) * c ^ 2) := div_le_div_of_nonneg_right (by linarith) hD₀.le
      _ = _ := by rw [div_eq_div_iff hD₀.ne' (mul_pos h4r hc).ne']; ring
  have hnle : n ≤ 64 / (3 * (4 - r) ^ 2 * c ^ 2) := by
    calc n ≤ 192 * c ^ 2 / D ^ 2 := hn
      _ ≤ 192 * c ^ 2 / (3 * (4 - r) * c ^ 2) ^ 2 := by gcongr
      _ = _ := by rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  obtain ⟨X, hX⟩ : ∃ X, X = 2 * √r / (4 - r) + 64 / (3 * (4 - r) ^ 2 * c) := ⟨_, rfl⟩
  have hsum : 2 * m * (3 / D) + n ≤ X / c := by
    have : X / c = 2 * √r / ((4 - r) * c) + 64 / (3 * (4 - r) ^ 2 * c ^ 2) := by
      rw [hX]; field_simp
    rw [this]; linarith
  have hP : (3 / D) ^ 2 * (2 * m ^ 2) + 3 / D * n + n ^ 2 / 2 ≤ (X / c) ^ 2 / 2 := by
    have h0 : 0 ≤ 3 / D * n * (2 * m - 1) := mul_nonneg (mul_nonneg hA0 hn0) (by linarith)
    have h1 : (3 / D) ^ 2 * (2 * m ^ 2) + 3 / D * n + n ^ 2 / 2 ≤ (2 * m * (3 / D) + n) ^ 2 / 2 := by
      nlinarith only [h0]
    have h2 : (2 * m * (3 / D) + n) ^ 2 ≤ (X / c) ^ 2 :=
      pow_le_pow_left₀ (by have := mul_nonneg hm0 hA0; linarith) hsum 2
    linarith
  have hP0 : 0 ≤ (3 / D) ^ 2 * (2 * m ^ 2) + 3 / D * n + n ^ 2 / 2 := by positivity
  have hPa : ((3 / D) ^ 2 * (2 * m ^ 2) + 3 / D * n + n ^ 2 / 2) / a ≤ X ^ 2 / (6 * c ^ 3) := by
    calc _ ≤ ((3 / D) ^ 2 * (2 * m ^ 2) + 3 / D * n + n ^ 2 / 2) / (3 * c) :=
          div_le_div_of_nonneg_left hP0 (by positivity) haL
      _ ≤ (X / c) ^ 2 / 2 / (3 * c) := by gcongr
      _ = _ := by ring
  have hQa : a * ((4 / D) ^ 2 / 2) ≤ 32 * √3 / (3 * (4 - r) ^ 2) / (6 * c ^ 3) := by
    calc a * ((4 / D) ^ 2 / 2) = 8 * a / D ^ 2 := by ring
      _ ≤ 8 * (2 * √3 * c) / (3 * (4 - r) * c ^ 2) ^ 2 := by gcongr
      _ = _ := by rw [div_div, div_eq_div_iff (by positivity) (by positivity)]; ring
  have e : omega2Sq c r / (6 * c ^ 3) = X ^ 2 / (6 * c ^ 3) + 32 * √3 / (3 * (4 - r) ^ 2) / (6 * c ^ 3) := by
    unfold omega2Sq; rw [hX]; ring
  rw [e]; linarith

/-- Cauchy–Schwarz against the energy: `(|ψ|P + |u|Q)² ≤ (aψ² + u²/a)(P²/a + aQ²)` for `a > 0`. -/
theorem sq_add_le_energy_mul {a ψ u P Q : ℝ} (ha : 0 < a) :
    (|ψ| * P + |u| * Q) ^ 2 ≤ (a * ψ ^ 2 + u ^ 2 / a) * (P ^ 2 / a + a * Q ^ 2) := by
  have key : (a * ψ ^ 2 + u ^ 2 / a) * (P ^ 2 / a + a * Q ^ 2) - (|ψ| * P + |u| * Q) ^ 2
      = (a * |ψ| * Q - |u| * P / a) ^ 2 := by
    rw [← sq_abs ψ, ← sq_abs u]; field_simp; ring
  nlinarith only [key, sq_nonneg (a * |ψ| * Q - |u| * P / a)]

/-- **The boundary at `ξ = 2`**: `‖W(2)‖² ≤ E(2)ω₂²/(6c³)` for `0 ≤ χ ≤ c²`, `t² + ¼ ≤ r c²`, `r < 4`. -/
theorem norm_greenWC_two_sq_le {c χ r t : ℝ} (ψ u : ℝ → ℝ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hr : r < 4) (hw : t ^ 2 + 1 / 4 ≤ r * c ^ 2) :
    ‖greenWC c χ t ψ u 2‖ ^ 2 ≤ energy (aP c χ) ψ u 2 * omega2Sq c r / (6 * c ^ 3) := by
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
  -- the amplitude `a(2)² = 3(4c² − χ) ∈ [9c², 12c²]`
  have ha2 : aP c χ 2 ^ 2 = 3 * (4 * c ^ 2 - χ) := by
    unfold aP; rw [Real.sq_sqrt (by unfold pP qP; nlinarith)]; unfold pP qP; ring
  have ha0 : 0 ≤ aP c χ 2 := Real.sqrt_nonneg _
  have haL : 3 * c ≤ aP c χ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) ha0 two_ne_zero).mp (by rw [ha2]; nlinarith)
  have hapos : 0 < aP c χ 2 := by linarith
  have haU : aP c χ 2 ≤ 2 * √3 * c := by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine (pow_le_pow_iff_left₀ ha0 (by positivity) two_ne_zero).mp ?_
    rw [ha2, mul_pow, mul_pow, h3]; nlinarith
  -- the mismatch `D(2) = 4(4c² − χ) − 3w ≥ 3(4 − r)c²` and `n = −3β(2) = 12(16c² − w)/D²`
  have hw4 : 1 / 4 ≤ w := by rw [hwd]; nlinarith [sq_nonneg t]
  have hwr : w ≤ r * c ^ 2 := by rw [hwd]; exact hw
  have hDge : 3 * (4 - r) * c ^ 2 ≤ D := by rw [hDd]; unfold DM qP pP; nlinarith
  have hn : n = 12 * (16 * c ^ 2 - w) / D ^ 2 := by rw [hnd, hDd]; unfold betaM; ring
  have hwc : w ≤ 16 * c ^ 2 := by nlinarith
  have hn0 : 0 ≤ n := by rw [hn]; exact div_nonneg (by linarith) (sq_nonneg _)
  have hnle : n ≤ 192 * c ^ 2 / D ^ 2 := by
    rw [hn]; exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  -- `m = √w ∈ [½, √r c]`
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
  have hE0 : 0 ≤ energy (aP c χ) ψ u 2 := by unfold energy; positivity
  calc ‖greenWC c χ t ψ u 2‖ ^ 2 ≤ (|ψ 2| * ‖P₁‖ + |u 2| * ‖Q₁‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hT 2
    _ ≤ energy (aP c χ) ψ u 2 * (‖P₁‖ ^ 2 / aP c χ 2 + aP c χ 2 * ‖Q₁‖ ^ 2) := sq_add_le_energy_mul hapos
    _ ≤ energy (aP c χ) ψ u 2 * (omega2Sq c r / (6 * c ^ 3)) := mul_le_mul_of_nonneg_left hcoef hE0
    _ = _ := by ring
/-- **The edge Mellin bound**: `‖I(1, 2; t)‖ ≤ √m(ω₂/c + ‖ρ_t‖_{L²[1,2]})`, `m = ∫₁^X ψ²`, for a rung with
`c ≥ 80`, `X ≥ 2`, `t² + ¼ ≤ r c²`, `r ≤ 1`. -/
theorem norm_mellinI_one_two_le {g g₁ g₂ : ℝ → ℝ} {c χ r t X : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hX : 2 ≤ X) (hr : r ≤ 1)
    (hw : t ^ 2 + 1 / 4 ≤ r * c ^ 2) :
    ‖Cvs.L2a.FarPartDirichletSplit.mellinI (psi c g) 1 2 t‖
      ≤ √(∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2)
        * (√(omega2Sq c r) / c + √(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χ t ξ‖ ^ 2)) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hc0 : 0 < c := by linarith
  have hwc : t ^ 2 + 1 / 4 ≤ c ^ 2 := hw.trans (mul_le_of_le_one_left (sq_nonneg c) hr)
  have heq := mellinI_one_eq (b := 2) (t := t) hg hg₁ hg₂c hang (by norm_num) hχ hwc
  set m := ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 with hmd
  have hm0 : 0 ≤ m := integral_nonneg (by linarith) fun ξ _ => sq_nonneg _
  have hω0 : 0 ≤ omega2Sq c r := by unfold omega2Sq; positivity
  -- the boundary term
  have hE := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le_rung hg hg₁ hg₂c hang hc hχ0 hχ hX 2 ⟨by norm_num, hX⟩
  have hWsq := norm_greenWC_two_sq_le (psi c g) (rungU c g) hc0 hχ0 hχ.le (by linarith) hw
  have hW : ‖greenWC c χ t (psi c g) (rungU c g) 2‖ ≤ √m * √(omega2Sq c r) / c := by
    have h2 : ‖greenWC c χ t (psi c g) (rungU c g) 2‖ ^ 2 ≤ m * omega2Sq c r / c ^ 2 := by
      refine hWsq.trans ?_
      calc energy (aP c χ) (psi c g) (rungU c g) 2 * omega2Sq c r / (6 * c ^ 3)
          ≤ 6 * c * m * omega2Sq c r / (6 * c ^ 3) := by gcongr
        _ = m * omega2Sq c r / c ^ 2 := by field_simp
    have h := Real.abs_le_sqrt h2
    rw [abs_of_nonneg (norm_nonneg _), Real.sqrt_div (mul_nonneg hm0 hω0), Real.sqrt_mul hm0,
      Real.sqrt_sq hc0.le] at h
    exact h
  -- the bulk term, by Cauchy–Schwarz on `[1, 2]`
  have hpos : ∀ ξ ∈ Icc (1 : ℝ) 2, 0 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hk : ∀ {y v : ℝ → ℝ}, (∀ ξ, 0 < ξ → HasDerivAt y (v ξ / ξ ^ 2) ξ) →
      (∀ ξ, 0 < ξ → HasDerivAt v (-((t ^ 2 + 1 / 4) * y ξ)) ξ) →
      ContinuousOn (fun ξ => (greenRho c χ (t ^ 2 + 1 / 4) y v ξ : ℂ)) (Icc 1 2) :=
    fun hy hv => Complex.continuous_ofReal.comp_continuousOn (continuousOn_greenRho hχ hwc
      (fun ξ hξ => (hy ξ (hpos ξ hξ)).continuousAt.continuousWithinAt)
      (fun ξ hξ => (hv ξ (hpos ξ hξ)).continuousAt.continuousWithinAt))
  have hρ : ContinuousOn (rhoEdge c χ t) (Icc 1 2) := by
    unfold rhoEdge
    exact (hk (fun ξ h => hasDerivAt_ky h) (fun ξ h => hasDerivAt_ku h)).sub
      (continuousOn_const.mul (hk (fun ξ h => hasDerivAt_kys h) (fun ξ h => hasDerivAt_kus h)))
  have hψ2 : ContinuousOn (fun ξ => |psi c g ξ|) (Icc 1 2) := hψc.continuousOn.abs
  have hρn : ContinuousOn (fun ξ => ‖rhoEdge c χ t ξ‖) (Icc 1 2) := hρ.norm
  have hnorm : ‖∫ ξ in (1 : ℝ)..2, (psi c g ξ : ℂ) * rhoEdge c χ t ξ‖
      ≤ ∫ ξ in (1 : ℝ)..2, |psi c g ξ| * ‖rhoEdge c χ t ξ‖ := by
    refine (norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
    congr 1; funext ξ; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcs := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (a := 1) (b := 2) (by norm_num)
    (f := fun ξ => |psi c g ξ|) (w := fun ξ => ‖rhoEdge c χ t ξ‖)
    ((hψ2.pow 2).intervalIntegrable_of_Icc (by norm_num))
    ((hρn.pow 2).intervalIntegrable_of_Icc (by norm_num))
    ((hψ2.mul hρn).intervalIntegrable_of_Icc (by norm_num))
  simp only [sq_abs] at hcs
  have hmono : ∫ ξ in (1 : ℝ)..2, psi c g ξ ^ 2 ≤ m :=
    integral_mono_interval le_rfl (by norm_num) hX
      (Filter.Eventually.of_forall fun ξ => sq_nonneg (psi c g ξ))
      ((hψc.pow 2).continuousOn.intervalIntegrable_of_Icc (by linarith))
  have hρ0 : 0 ≤ ∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χ t ξ‖ ^ 2 :=
    integral_nonneg (by norm_num) fun ξ _ => sq_nonneg _
  have hbulk : ‖∫ ξ in (1 : ℝ)..2, (psi c g ξ : ℂ) * rhoEdge c χ t ξ‖
      ≤ √m * √(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χ t ξ‖ ^ 2) := by
    refine hnorm.trans ((le_abs_self _).trans ?_)
    refine (Real.abs_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_right hmono hρ0))).trans_eq ?_
    exact Real.sqrt_mul hm0 _
  rw [heq]
  calc _ ≤ ‖greenWC c χ t (psi c g) (rungU c g) 2‖
        + ‖∫ ξ in (1 : ℝ)..2, (psi c g ξ : ℂ) * rhoEdge c χ t ξ‖ := norm_sub_le _ _
    _ ≤ √m * √(omega2Sq c r) / c + √m * √(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χ t ξ‖ ^ 2) := add_le_add hW hbulk
    _ = _ := by ring

end Cvs.Prolate.Mellin.EdgeGreenIdentity
