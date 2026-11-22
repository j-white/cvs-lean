import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandEdgeLowMass
import Cvs.L2a.EdgeCountSSums
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanLowMass
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.SelfConvolutionCosine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# LOW′ on the full span, with no spectral-gap hypothesis

The span splits at `c² − χᵢ = 5c`: deep rungs keep `RungSpanLowMass`'s per-rung edge bound, band rungs take `BandEdgeLowMass`'s Bessel form
with one multiplier at `χ_r = c² − 5c` and mismatch `Δ = 5c`. Only `χᵢ < c²` is assumed, and
`specMass (posTail Φ X)(c/K0) ≤ η_P^full·P` with `η_P^full = (√Far + 2√Wb + √ℛ + √Bnd)²/(πK0)`.
-/

namespace Cvs.L2a.FullSpanLowMass

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.SpectralMassLevelLeak Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.L2a.RungSpanLowMass Cvs.L2a.BandEdgeLowMass
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- The band constant `Bnd(c, r, X) = C_M(c, X)(√(c·LE(c, r, 5)) + √(5/(2(1 − r))))²`. -/
noncomputable def Bnd (c r X : ℝ) : ℝ :=
  CM c X * (√(c * Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r 5) + √(5 / (2 * (1 - r)))) ^ 2

/-- `η_P` on the full span: `(√Far + 2√Wb + √ℛ + √Bnd)²/(πK0)`. -/
noncomputable def etaPfull (c K0 J X : ℝ) : ℝ :=
  (√(Cvs.L2a.RungSpanLowMass.Far c K0 J) + 2 * √(Cvs.L2a.RungSpanLowMass.Wb c K0 J)
    + √(Cvs.L2a.EdgeCountSSums.Rcal c (Cvs.L2a.RungSpanLowMass.rLow c K0) J)
    + √(Bnd c (Cvs.L2a.RungSpanLowMass.rLow c K0) X)) ^ 2 / (π * K0)

/-- `ℛ(c, r, J)` is monotone in `J`. -/
theorem Rcal_mono_J {c r J J' : ℝ} (hc : 80 ≤ c) (hr0 : 0 ≤ r) (hr : r < 1) (hJ : J ≤ J') :
    Cvs.L2a.EdgeCountSSums.Rcal c r J ≤ Cvs.L2a.EdgeCountSSums.Rcal c r J' := by
  have hc0 : 0 < c := by linarith
  have h1r : 0 < 1 - r := by linarith
  have he := Cvs.Prolate.Mellin.EdgeRemainderClosedForm.e1_nonneg hr0 hr
  have hL := Cvs.L2a.LowConstantUniform.Lc_nonneg hc
  unfold Cvs.L2a.EdgeCountSSums.Rcal Cvs.L2a.EdgeCountSSums.RcalS
  have hJc : J / c ≤ J' / c := div_le_div_of_nonneg_right hJ hc0.le
  gcongr

/-- `0 ≤ C_M(c, X)` for `c ≥ 80`, `X ≥ 2`. -/
theorem CM_nonneg {c X : ℝ} (hc : 80 ≤ c) (hX : 2 ≤ X) : 0 ≤ CM c X := by
  have hc0 : 0 < c := by linarith
  unfold CM
  have hp : 0 < X ^ 2 - 1 := by nlinarith
  have hWb1 : 2 * X / (c * (X ^ 2 - 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ X), hc]
  have hL0 : 0 ≤ Real.log ((X + 1) / (X - 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have : 0 ≤ (1 + X / (c * (X ^ 2 - 1))) / (1 - 2 * X / (c * (X ^ 2 - 1))) :=
    div_nonneg (by positivity) (by linarith)
  positivity

/-- `0 ≤ LE(c, r, s)` for `c ≥ 80`, `0 ≤ r < 1`, `s > 0`. -/
theorem lemmaEBound_nonneg {c r s : ℝ} (hc : 80 ≤ c) (hr0 : 0 ≤ r) (hr : r < 1) (hs : 0 < s) :
    0 ≤ Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r s := by
  have hc0 : 0 < c := by linarith
  have := Cvs.Prolate.Mellin.EdgeRemainderClosedForm.e1_nonneg hr0 hr
  have hL := Cvs.L2a.LowConstantUniform.Lc_nonneg hc
  have h1r : 0 < 1 - r := by linarith
  unfold Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound
  positivity

/-- `0 ≤ ℛ(c, r, J)` for `c ≥ 80`, `0 ≤ r < 1`, `J ≥ 0`. -/
theorem Rcal_nonneg {c r J : ℝ} (hc : 80 ≤ c) (hr0 : 0 ≤ r) (hr : r < 1) (hJ : 0 ≤ J) :
    0 ≤ Cvs.L2a.EdgeCountSSums.Rcal c r J := by
  have hc0 : 0 < c := by linarith
  have := Cvs.Prolate.Mellin.EdgeRemainderClosedForm.e1_nonneg hr0 hr
  have hL := Cvs.L2a.LowConstantUniform.Lc_nonneg hc
  have hA : 0 ≤ Cvs.Prolate.EdgeBesselCount.Ac c := by
    unfold Cvs.Prolate.EdgeBesselCount.Ac Cvs.Prolate.EdgeBesselCount.Kbar Cvs.Prolate.EdgeBesselCount.betaEdge
    have : 0 ≤ Real.log (12 * c / 5) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
    positivity
  have hl5 : 0 ≤ Real.log (c / 5) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have h1r : 0 < 1 - r := by linarith
  unfold Cvs.L2a.EdgeCountSSums.Rcal Cvs.L2a.EdgeCountSSums.RcalS
  positivity

variable {ι : Type} [Fintype ι]

set_option maxHeartbeats 1600000 in
/-- **THEOREM LOW′ on the full span (rungs below the turning point)**: the plunge band `c² − χᵢ < 5c` in Bessel
form (one multiplier at `χ_r = c² − 5c`), the deep rungs by Cvs.L2a.RungSpanLowMass: `specMass (posTail Φ X)(c/K0) ≤ η_P^full·P`. -/
theorem low_le_full (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} {X K0 : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hK0 : 0 < K0)
    (hr : Cvs.L2a.RungSpanLowMass.rLow c K0 < 1) :
    Cvs.L2a.SpectralMassLevelLeak.specMass
        (Cvs.L2a.PositionTruncatedTail.posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0)
      ≤ etaPfull c K0 (Fintype.card ι) X * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 := by
  classical
  have hc0 : 0 < c := by linarith
  set r := rLow c K0 with hrd
  have hr0 : 0 ≤ r := by rw [hrd]; unfold rLow; positivity
  set p : ι → Prop := fun i => 5 * c ≤ c ^ 2 - χ i with hpd
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  set m : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hmd
  set P := ∑ i, a i ^ 2 * m i with hPd
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦd
  set ΦD : ℝ → ℝ := fun ξ => ∑ i : {i // p i}, a i * psi c (g i) ξ with hΦD
  set ΦB : ℝ → ℝ := fun ξ => ∑ i : {i // ¬ p i}, a i * psi c (g i) ξ with hΦB
  -- the split of the profile and of its edge
  have hΦsplit : Φ = ΦD + ΦB := by
    funext ξ
    exact (Fintype.sum_subtype_add_sum_subtype p (fun i => a i * psi c (g i) ξ)).symm
  have hedge : posTail Φ 2 = posTail ΦD 2 + posTail ΦB 2 := by
    funext θ
    simp only [Pi.add_apply, hΦd, hΦD, hΦB]
    rw [Cvs.L2a.PositionTailSpanAdapters.posTail_sum Finset.univ a (fun i => psi c (g i)),
      Cvs.L2a.PositionTailSpanAdapters.posTail_sum Finset.univ (fun i : {i // p i} => a i) (fun i => psi c (g i)),
      Cvs.L2a.PositionTailSpanAdapters.posTail_sum Finset.univ (fun i : {i // ¬ p i} => a i) (fun i => psi c (g i))]
    exact (Fintype.sum_subtype_add_sum_subtype p (fun i => a i * posTail (psi c (g i)) 2 θ)).symm
  have hPsplit : P = (∑ i : {i // p i}, a i ^ 2 * m i) + ∑ i : {i // ¬ p i}, a i ^ 2 * m i :=
    (Fintype.sum_subtype_add_sum_subtype p (fun i => a i ^ 2 * m i)).symm
  have hPD0 : 0 ≤ ∑ i : {i // p i}, a i ^ 2 * m i := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hPB0 : 0 ≤ ∑ i : {i // ¬ p i}, a i ^ 2 * m i := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hPD : ∑ i : {i // p i}, a i ^ 2 * m i ≤ P := by rw [hPsplit]; linarith
  have hPB : ∑ i : {i // ¬ p i}, a i ^ 2 * m i ≤ P := by rw [hPsplit]; linarith
  have hJD : (Fintype.card {i // p i} : ℝ) ≤ J := by
    rw [hJd]; exact_mod_cast Fintype.card_subtype_le p
  have hJB : (Fintype.card {i // ¬ p i} : ℝ) ≤ J := by
    rw [hJd]; exact_mod_cast Fintype.card_subtype_le _
  have hπK : 0 < π * K0 := by positivity
  -- admissibility of the three pieces
  have hΦc := Cvs.L2a.PositionTailSpanAdapters.contDiffOn_span a hg hg₁ hg₂c hang
  have hΦDc := Cvs.L2a.PositionTailSpanAdapters.contDiffOn_span (fun i : {i // p i} => a i) (fun i => hg i)
    (fun i => hg₁ i) (fun i => hg₂c i) (fun i => hang i)
  have hΦBc := Cvs.L2a.PositionTailSpanAdapters.contDiffOn_span (fun i : {i // ¬ p i} => a i) (fun i => hg i)
    (fun i => hg₁ i) (fun i => hg₂c i) (fun i => hang i)
  have hadX := Cvs.L2a.PositionTailAdmissible.admissible_posTail (by linarith : (1 : ℝ) ≤ X) (hΦc X)
  have had2 := Cvs.L2a.PositionTailAdmissible.admissible_posTail (by norm_num : (1 : ℝ) ≤ 2) (hΦc 2)
  have hadD := Cvs.L2a.PositionTailAdmissible.admissible_posTail (by norm_num : (1 : ℝ) ≤ 2) (hΦDc 2)
  have hadB := Cvs.L2a.PositionTailAdmissible.admissible_posTail (by norm_num : (1 : ℝ) ≤ 2) (hΦBc 2)
  -- far + edge, then deep edge + band edge
  have hs1 := sqrt_specMass_add_le (G := posTail Φ X - posTail Φ 2) (H := posTail Φ 2)
    (by rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact hadX.1.sub had2.1)
    (by rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact hadX.2.1.sub had2.2.1) had2.1 had2.2.1 (c / K0)
  rw [sub_add_cancel] at hs1
  have hs2 := sqrt_specMass_add_le (G := posTail ΦD 2) (H := posTail ΦB 2) hadD.1 hadD.2.1 hadB.1 hadB.2.1 (c / K0)
  rw [← hedge] at hs2
  -- the far part (Cvs.L2a.RungSpanLowMass, χ < c² only)
  have hrf : 1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2) < 1 := by
    have : 1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2) = r / 4 := by rw [hrd]; unfold rLow; field_simp; ring
    rw [this]; linarith
  have hF := specMass_far_span_le a hg hg₁ hg₂c hang hX hc hχ0 hχc hM hK0 hrf
  -- the deep edge (Cvs.L2a.RungSpanLowMass on the deep subfamily)
  have hE := specMass_edge_span_le (fun i : {i // p i} => a i) (fun i => hg i) (fun i => hg₁ i) (fun i => hg₂c i)
    (fun i => hang i) hX hc (fun i => hχ0 i) (fun i => i.2) (hχinj.comp Subtype.val_injective) (fun i => hM i)
    hK0 hr
  -- the band edge (Bessel form, multiplier at χ_r = c² − 5c, Δ = 5c)
  have hBd := Cvs.L2a.BandEdgeLowMass.specMass_band_edge_le (fun i : {i // ¬ p i} => a i) (fun i => hg i) (fun i => hg₁ i)
    (fun i => hg₂c i) (fun i => hang i) (χr := c ^ 2 - 5 * c) (Δ := 5 * c) hc (by nlinarith) (by linarith)
    (fun i => hχ0 i) (fun i => hχc i) (hχinj.comp Subtype.val_injective) hX (fun i => hM i) hK0 hr
    (by positivity) (fun i => by
      have h1 : c ^ 2 - χ i < 5 * c := lt_of_not_ge i.2
      have h2 := hχc i
      rw [abs_le]; constructor <;> linarith)
  -- monotone constants
  have hω0 : 0 ≤ omega2Sq c r := by unfold omega2Sq; positivity
  have hWbD : Wb c K0 (Fintype.card {i // p i}) ≤ Wb c K0 J := by
    unfold Wb; rw [← hrd]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hJD hc0.le) hω0
  have hWbB : (Fintype.card {i // ¬ p i} : ℝ) / c * omega2Sq c r ≤ Wb c K0 J := by
    unfold Wb; rw [← hrd]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hJB hc0.le) hω0
  have hRD : Cvs.L2a.EdgeCountSSums.Rcal c r (Fintype.card {i // p i}) ≤ Cvs.L2a.EdgeCountSSums.Rcal c r J :=
    Rcal_mono_J hc hr0 hr hJD
  -- each piece as `√P · (const)/√(πK0)`
  have hsq : ∀ {A Y : ℝ}, 0 ≤ Y → A ≤ P * (Y ^ 2 / (π * K0)) → √A ≤ √P * Y / √(π * K0) := by
    intro A Y hY h
    refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hP0, Real.sqrt_div' _ hπK.le, Real.sqrt_sq hY]; ring
  have hFar0 : 0 ≤ Far c K0 J := by unfold Far; positivity
  have h1 : √(specMass (posTail Φ X - posTail Φ 2) (c / K0)) ≤ √P * √(Far c K0 J) / √(π * K0) := by
    refine hsq (Real.sqrt_nonneg _) (hF.trans (le_of_eq ?_))
    rw [Real.sq_sqrt hFar0]
  have hR0 : 0 ≤ Cvs.L2a.EdgeCountSSums.Rcal c r J := Rcal_nonneg hc hr0 hr (Nat.cast_nonneg _)
  have h2 : √(specMass (posTail ΦD 2) (c / K0))
      ≤ √P * (√(Wb c K0 J) + √(Cvs.L2a.EdgeCountSSums.Rcal c r J)) / √(π * K0) := by
    refine hsq (by positivity) (hE.trans ?_)
    have hY : √(Wb c K0 (Fintype.card {i // p i})) + √(Cvs.L2a.EdgeCountSSums.Rcal c (rLow c K0) (Fintype.card {i // p i}))
        ≤ √(Wb c K0 J) + √(Cvs.L2a.EdgeCountSSums.Rcal c r J) :=
      add_le_add (Real.sqrt_le_sqrt hWbD) (Real.sqrt_le_sqrt hRD)
    exact mul_le_mul hPD (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hY 2) hπK.le)
      (by positivity) hP0
  -- the band piece: `√c·Z ≤ √Wb + √Bnd`
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = √(Fintype.card {i // ¬ p i} : ℝ) * √(omega2Sq c r) / c
      + √(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r ((c ^ 2 - (c ^ 2 - 5 * c)) / c))
        + 5 * c * √(1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - (c ^ 2 - 5 * c))))) := ⟨_, rfl⟩
  have h5 : (c ^ 2 - (c ^ 2 - 5 * c)) / c = 5 := by field_simp; ring
  have h1r : 0 < 1 - r := by linarith
  have hcZ : √c * Z ≤ √(Wb c K0 J) + √(Bnd c r X) := by
    have e1 : √c * (√(Fintype.card {i // ¬ p i} : ℝ) * √(omega2Sq c r) / c)
        = √((Fintype.card {i // ¬ p i} : ℝ) / c * omega2Sq c r) := by
      rw [Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hc0.le), Real.sqrt_div' _ hc0.le]
      have hsc : √c ^ 2 = c := Real.sq_sqrt hc0.le
      have hsc0 : 0 < √c := Real.sqrt_pos.mpr hc0
      field_simp
      rw [hsc]; ring
    have e2 : √c * (√(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r ((c ^ 2 - (c ^ 2 - 5 * c)) / c))
        + 5 * c * √(1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - (c ^ 2 - 5 * c))))))
        = √(Bnd c r X) := by
      have hCM : 0 ≤ CM c X := CM_nonneg hc hX
      have hLE0 : 0 ≤ Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r 5 := lemmaEBound_nonneg hc hr0 hr (by norm_num)
      rw [h5]
      unfold Bnd
      rw [Real.sqrt_mul hCM, Real.sqrt_sq (by positivity)]
      have hsc : √c ^ 2 = c := Real.sq_sqrt hc0.le
      have hsc0 : 0 < √c := Real.sqrt_pos.mpr hc0
      have ea : √c * √(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r 5) = √(c * Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r 5) :=
        (Real.sqrt_mul hc0.le _).symm
      have eb : √c * (5 * c * √(1 / (2 * (1 - r) * c ^ 2 * (5 * c)))) = √(5 / (2 * (1 - r))) := by
        have : 1 / (2 * (1 - r) * c ^ 2 * (5 * c)) = (5 / (2 * (1 - r))) / (25 * c ^ 3) := by
          field_simp; ring
        rw [this, Real.sqrt_div' _ (by positivity)]
        have : √(25 * c ^ 3) = 5 * c * √c := by
          rw [show 25 * c ^ 3 = (5 * c) ^ 2 * c by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        rw [this]
        field_simp
      have e3 : c ^ 2 - (c ^ 2 - 5 * c) = 5 * c := by ring
      rw [e3]
      calc √c * (√(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r 5)
            + 5 * c * √(1 / (2 * (1 - r) * c ^ 2 * (5 * c)))))
          = √(CM c X) * (√c * √(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r 5)
            + √c * (5 * c * √(1 / (2 * (1 - r) * c ^ 2 * (5 * c))))) := by ring
        _ = _ := by rw [ea, eb]
    rw [hZd, mul_add, e1, e2]
    exact add_le_add (Real.sqrt_le_sqrt hWbB) le_rfl
  have h3 : √(specMass (posTail ΦB 2) (c / K0)) ≤ √P * (√(Wb c K0 J) + √(Bnd c r X)) / √(π * K0) := by
    rw [← hrd, ← hZd] at hBd
    refine hsq (by positivity) (hBd.trans ?_)
    have hZ0 : 0 ≤ Z := by
      rw [hZd]
      have := CM_nonneg hc hX
      positivity
    have hcZ2 : c * Z ^ 2 ≤ (√(Wb c K0 J) + √(Bnd c r X)) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hcZ 2
      rw [mul_pow, Real.sq_sqrt hc0.le] at this
      exact this
    calc c / K0 / π * ((∑ i : {i // ¬ p i}, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) * Z ^ 2)
        = (∑ i : {i // ¬ p i}, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) * (c * Z ^ 2) / (π * K0) := by
          field_simp; try ring
      _ ≤ P * (√(Wb c K0 J) + √(Bnd c r X)) ^ 2 / (π * K0) :=
          div_le_div_of_nonneg_right (mul_le_mul hPB hcZ2 (by positivity) hP0) hπK.le
      _ = P * ((√(Wb c K0 J) + √(Bnd c r X)) ^ 2 / (π * K0)) := by ring
  -- assemble
  have hm0 := specMass_nonneg (posTail Φ X) (c / K0)
  have htot : √(specMass (posTail Φ X) (c / K0))
      ≤ √P * (√(Far c K0 J) + 2 * √(Wb c K0 J) + √(Cvs.L2a.EdgeCountSSums.Rcal c r J) + √(Bnd c r X))
        / √(π * K0) := by
    refine hs1.trans ((add_le_add h1 (hs2.trans (add_le_add h2 h3))).trans_eq ?_)
    ring
  have hY0 : 0 ≤ √(Far c K0 J) + 2 * √(Wb c K0 J) + √(Cvs.L2a.EdgeCountSSums.Rcal c r J) + √(Bnd c r X) := by
    positivity
  calc specMass (posTail Φ X) (c / K0) = √(specMass (posTail Φ X) (c / K0)) ^ 2 := (Real.sq_sqrt hm0).symm
    _ ≤ (√P * (√(Far c K0 J) + 2 * √(Wb c K0 J) + √(Cvs.L2a.EdgeCountSSums.Rcal c r J) + √(Bnd c r X))
          / √(π * K0)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) htot 2
    _ = etaPfull c K0 J X * P := by
        unfold etaPfull
        rw [← hrd, div_pow, mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hπK.le]
        ring

/-- `0 ≤ η_P^full`. -/
theorem etaPfull_nonneg {c K0 J X : ℝ} (hK0 : 0 < K0) : 0 ≤ etaPfull c K0 J X := by
  unfold etaPfull; positivity

/-- LOW′ on the full span under the frame floor `κ_F P ≤ ∫₁^∞ (posTail Φ X)²`: `PositionTailFullTail`'s `hlow` with
`η = η_P^full/κ_F`, assuming only `χᵢ < c²`. -/
theorem hlow_of_FF_full (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} {X K0 κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hK0 : 0 < K0)
    (hr : rLow c K0 < 1) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    ∫ t in {t : ℝ | |t| < c / K0}, specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ etaPfull c K0 (Fintype.card ι) X / κF
        * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 := by
  have h := low_le_full a hg hg₁ hg₂c hang hX hc hχ0 hχc hχinj hM hK0 hr
  set N := ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 with hN
  set P := ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hPd
  have hP : P ≤ N / κF := by rw [le_div_iff₀ hκ, mul_comm]; exact hFF
  have he := etaPfull_nonneg (c := c) (J := (Fintype.card ι : ℝ)) (X := X) hK0
  calc _ = specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0) := rfl
    _ ≤ etaPfull c K0 (Fintype.card ι) X * P := h
    _ ≤ etaPfull c K0 (Fintype.card ι) X * (N / κF) := mul_le_mul_of_nonneg_left hP he
    _ = etaPfull c K0 (Fintype.card ι) X / κF * N := by ring

end Cvs.L2a.FullSpanLowMass
