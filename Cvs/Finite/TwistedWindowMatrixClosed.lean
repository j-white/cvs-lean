import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.CutModeLevySeries
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.GeneratorClosedForm
import Cvs.Finite.LevyKernelIncrement
import Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The twisted window matrix in closed form

For abscissa `σ`, conductor `q` and prime weights `w`, the pole-free window pairing has every
entry in terms of `Im ψ`, `Re ψ − ψ(σ)` and `Re ψ'` at `σ + iπm/L`, a finite weighted sum, and
series geometric in `e^{−2L}`.
-/

namespace Cvs.Finite.TwistedWindowMatrixClosed

open Real MeasureTheory Set
open Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa (densityS zs imTermS deficitS cutTermS)
open Cvs.Finite.DiagonalCutSymbol (sinCut cosCut vcosCut)

/-- The twisted archimedean constant `ψ(σ) − log π + log q`. -/
noncomputable def archS0 (σ q : ℝ) : ℝ :=
  (Complex.digamma (σ : ℂ)).re - Real.log π + Real.log q

/-- The weighted sum over `2 ≤ n ≤ P` at lags `log n`. -/
noncomputable def primeSumS (w : ℕ → ℝ) (P : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 P, w n * (2 * h (Real.log n))

/-- The pole-free pairing at abscissa `σ`, conductor `q`, weights `w`. -/
noncomputable def PairS (σ q : ℝ) (w : ℕ → ℝ) (P : ℕ) (h : ℝ → ℝ) : ℝ :=
  archS0 σ q * h 0 + (∫ u in Ioi (0:ℝ), densityS σ u * (h 0 - h (u / 2))) - primeSumS w P h

/-- The tail factor `e^{−(σ+k)·2L}`. -/
noncomputable def tailS (σ L : ℝ) (k : ℕ) : ℝ := Real.exp (-((σ + (k : ℝ)) * (2 * L)))

/-- The cosine remainder term `e^{−(σ+k)2L}(σ+k)/((σ+k)² + b²)`. -/
noncomputable def rcS (σ L b : ℝ) (k : ℕ) : ℝ :=
  tailS σ L k * ((σ + (k : ℝ)) / ((σ + (k : ℝ)) ^ 2 + b ^ 2))

theorem tailS_nonneg (σ L : ℝ) (k : ℕ) : 0 ≤ tailS σ L k := (Real.exp_pos _).le

theorem tailS_le_one {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) (k : ℕ) : tailS σ L k ≤ 1 := by
  unfold tailS
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ (σ + (k : ℝ)) * (2 * L) := by positivity
  linarith

theorem tailS_eq (σ L : ℝ) (k : ℕ) :
    tailS σ L k = Real.exp (-(σ * (2 * L))) * Real.exp (-(2 * L)) ^ k := by
  unfold tailS
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem summable_tailS (σ : ℝ) {L : ℝ} (hL : 0 < L) : Summable (tailS σ L) := by
  have hr1 : Real.exp (-(2 * L)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have := (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left (Real.exp (-(σ * (2 * L))))
  exact this.congr fun k => (tailS_eq σ L k).symm

theorem summable_tailS_mul {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 < L) {f : ℕ → ℝ} (hf : Summable f) :
    Summable fun k => tailS σ L k * f k := by
  refine Summable.of_norm_bounded hf.norm fun k => ?_
  rw [norm_mul, Real.norm_of_nonneg (tailS_nonneg σ L k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (tailS_le_one hσ hL.le k)

theorem summable_rcS {σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L) (b : ℝ) : Summable (rcS σ L b) := by
  refine Summable.of_norm_bounded ((summable_tailS σ hL).mul_right (1 / σ)) fun k => ?_
  unfold rcS
  have hc : 0 < σ + (k : ℝ) := by positivity
  have hD : 0 < (σ + (k : ℝ)) ^ 2 + b ^ 2 := by positivity
  rw [norm_mul, Real.norm_of_nonneg (tailS_nonneg σ L k), Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (tailS_nonneg σ L k)
  rw [div_le_div_iff₀ hD hσ]
  nlinarith [sq_nonneg b, sq_nonneg (σ + (k : ℝ)), (Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-! ### The three cut pairings -/

theorem hasSum_levyS_sinCut {σ L ω : ℝ} (hσ : 1 / 4 ≤ σ) (hL : 0 < L)
    (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    HasSum (fun k : ℕ => -(ω / 2) * (1 - tailS σ L k) / ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2))
      (∫ u in Ioi (0:ℝ), densityS σ u * (sinCut L ω 0 - sinCut L ω (u / 2))) := by
  have h := Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.hasSum_levyS σ (Cvs.Finite.DiagonalCutSymbol.measurable_sinCut L ω)
    (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.integrableOn_densityS_mul hσ
      (Cvs.Finite.DiagonalCutSymbol.measurable_sinCut L ω)
      (Cvs.Finite.CutModeLevySeries.integrableOn_levy_sinCut hL ω))
  refine h.congr_fun fun k => ?_
  have hck : 0 < σ + (k : ℝ) := by positivity
  rw [Cvs.Finite.CutModeLevySeries.levyTerm_sinCut hL hck hs hc]
  rfl

theorem hasSum_levyS_cosCut {σ L ω : ℝ} (hσ : 1 / 4 ≤ σ) (hL : 0 < L)
    (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    HasSum (fun k : ℕ => 1 / (σ + (k : ℝ))
        - (σ + (k : ℝ)) * (1 - tailS σ L k) / ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2))
      (∫ u in Ioi (0:ℝ), densityS σ u * (cosCut L ω 0 - cosCut L ω (u / 2))) := by
  have h := Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.hasSum_levyS σ (Cvs.Finite.DiagonalCutSymbol.measurable_cosCut L ω)
    (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.integrableOn_densityS_mul hσ
      (Cvs.Finite.DiagonalCutSymbol.measurable_cosCut L ω)
      (Cvs.Finite.CutModeLevySeries.integrableOn_levy_cosCut hL ω))
  refine h.congr_fun fun k => ?_
  have hck : 0 < σ + (k : ℝ) := by positivity
  rw [Cvs.Finite.CutModeLevySeries.levyTerm_cosCut hL hck hs hc]
  rfl

theorem hasSum_levyS_vcosCut {σ L ω : ℝ} (hσ : 1 / 4 ≤ σ) (hL : 0 < L)
    (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    HasSum (fun k : ℕ => L * (σ + (k : ℝ)) * tailS σ L k / ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2)
        - ((σ + (k : ℝ)) ^ 2 - (ω / 2) ^ 2) * (1 - tailS σ L k)
          / (2 * ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2) ^ 2))
      (∫ u in Ioi (0:ℝ), densityS σ u * (vcosCut L ω 0 - vcosCut L ω (u / 2))) := by
  have h := Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.hasSum_levyS σ (Cvs.Finite.DiagonalCutSymbol.measurable_vcosCut L ω)
    (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.integrableOn_densityS_mul hσ
      (Cvs.Finite.DiagonalCutSymbol.measurable_vcosCut L ω)
      (Cvs.Finite.CutModeLevySeries.integrableOn_levy_vcosCut hL ω))
  refine h.congr_fun fun k => ?_
  have hck : 0 < σ + (k : ℝ) := by positivity
  rw [Cvs.Finite.CutModeLevySeries.levyTerm_vcosCut hL hck hs hc]
  rfl

/-- **The sine pairing**: `−Im ψ(σ + iω/2)` plus a geometric remainder, less the weighted sum. -/
theorem PairS_sinCut {σ L ω : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (hσ : 1 / 4 ≤ σ) (hL : 0 < L)
    (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    PairS σ q w P (sinCut L ω)
      = -(Complex.digamma (zs σ (ω / 2))).im
        + ∑' k, tailS σ L k * imTermS σ (ω / 2) k - primeSumS w P (sinCut L ω) := by
  have hσ0 : 0 < σ := by linarith
  unfold PairS
  rw [← (hasSum_levyS_sinCut hσ hL hs hc).tsum_eq, Cvs.Finite.DiagonalCutSymbol.sinCut_zero L ω hL.le,
    mul_zero, zero_add]
  have hterm : ∀ k : ℕ, -(ω / 2) * (1 - tailS σ L k) / ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2)
      = -imTermS σ (ω / 2) k + tailS σ L k * imTermS σ (ω / 2) k := by
    intro k; unfold imTermS; ring
  rw [tsum_congr hterm, Summable.tsum_add (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.summable_imTermS hσ0 _).neg
    (summable_tailS_mul hσ0.le hL (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.summable_imTermS hσ0 _)), tsum_neg,
    (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.hasSum_imTermS hσ0 _).tsum_eq]

/-- **The cosine pairing**: `ψ(σ) − log π + log q`, the deficit `Re ψ − ψ(σ)`, a remainder. -/
theorem PairS_cosCut {σ L ω : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (hσ : 1 / 4 ≤ σ) (hL : 0 < L)
    (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    PairS σ q w P (cosCut L ω)
      = archS0 σ q + ((Complex.digamma (zs σ (ω / 2))).re - (Complex.digamma (σ : ℂ)).re)
        + ∑' k, rcS σ L (ω / 2) k - primeSumS w P (cosCut L ω) := by
  have hσ0 : 0 < σ := by linarith
  unfold PairS
  rw [← (hasSum_levyS_cosCut hσ hL hs hc).tsum_eq, Cvs.Finite.DiagonalCutSymbol.cosCut_zero L ω hL.le,
    mul_one]
  have hterm : ∀ k : ℕ, 1 / (σ + (k : ℝ))
        - (σ + (k : ℝ)) * (1 - tailS σ L k) / ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2)
      = deficitS σ (ω / 2) k + rcS σ L (ω / 2) k := by
    intro k; unfold deficitS rcS; ring
  rw [tsum_congr hterm, Summable.tsum_add (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.summable_deficitS hσ0 _)
    (summable_rcS hσ0 hL _), (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.hasSum_deficitS hσ0 _).tsum_eq]
  ring

/-- **The `v cos` pairing**: `L` times the cosine remainder, `−½ Re ψ'`, and a remainder. -/
theorem PairS_vcosCut {σ L ω : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (hσ : 1 / 4 ≤ σ) (hσ1 : σ < 1)
    (hL : 0 < L) (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    PairS σ q w P (vcosCut L ω)
      = L * ∑' k, rcS σ L (ω / 2) k
        - 1 / 2 * (deriv Complex.digamma (zs σ (ω / 2))).re
        + 1 / 2 * ∑' k, tailS σ L k * cutTermS σ (ω / 2) k
        - primeSumS w P (vcosCut L ω) := by
  have hσ0 : 0 < σ := by linarith
  unfold PairS
  rw [← (hasSum_levyS_vcosCut hσ hL hs hc).tsum_eq, Cvs.Finite.DiagonalCutSymbol.vcosCut_zero L ω hL.le,
    mul_zero, zero_add]
  have hterm : ∀ k : ℕ, L * (σ + (k : ℝ)) * tailS σ L k / ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2)
        - ((σ + (k : ℝ)) ^ 2 - (ω / 2) ^ 2) * (1 - tailS σ L k)
          / (2 * ((σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2) ^ 2)
      = L * rcS σ L (ω / 2) k + (-(1 / 2) * cutTermS σ (ω / 2) k
          + 1 / 2 * (tailS σ L k * cutTermS σ (ω / 2) k)) := by
    intro k
    unfold rcS cutTermS
    have hD : (σ + (k : ℝ)) ^ 2 + (ω / 2) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hcut := Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.summable_cutTermS hσ0 hσ1 (ω / 2)
  rw [tsum_congr hterm, Summable.tsum_add ((summable_rcS hσ0 hL _).mul_left L)
    ((hcut.mul_left _).add ((summable_tailS_mul hσ0.le hL hcut).mul_left _)),
    tsum_mul_left, Summable.tsum_add (hcut.mul_left _) ((summable_tailS_mul hσ0.le hL hcut).mul_left _),
    tsum_mul_left, tsum_mul_left, (Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.hasSum_cutTermS hσ0 hσ1 _).tsum_eq]
  ring

/-! ### Linearity, and the kernel's two shapes -/

theorem PairS_add_smul {σ : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (a b : ℝ) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun u => densityS σ u * (f 0 - f (u / 2))) (Ioi 0))
    (hg : IntegrableOn (fun u => densityS σ u * (g 0 - g (u / 2))) (Ioi 0)) :
    PairS σ q w P (fun v => a * f v + b * g v) = a * PairS σ q w P f + b * PairS σ q w P g := by
  unfold PairS primeSumS
  have hint : (∫ u in Ioi (0:ℝ), densityS σ u * ((a * f 0 + b * g 0) - (a * f (u / 2) + b * g (u / 2))))
      = a * (∫ u in Ioi (0:ℝ), densityS σ u * (f 0 - f (u / 2)))
        + b * (∫ u in Ioi (0:ℝ), densityS σ u * (g 0 - g (u / 2))) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul a) (hg.const_mul b)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  have hps : ∑ n ∈ Finset.Icc 2 P, w n * (2 * (a * f (Real.log n) + b * g (Real.log n)))
      = a * ∑ n ∈ Finset.Icc 2 P, w n * (2 * f (Real.log n))
        + b * ∑ n ∈ Finset.Icc 2 P, w n * (2 * g (Real.log n)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hint]
  beta_reduce
  rw [hps]
  ring

theorem integrableOn_sinCut {σ L : ℝ} (hσ : 1 / 4 ≤ σ) (hL : 0 < L) (ω : ℝ) :
    IntegrableOn (fun u => densityS σ u * (sinCut L ω 0 - sinCut L ω (u / 2))) (Ioi 0) :=
  Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.integrableOn_densityS_mul hσ (Cvs.Finite.DiagonalCutSymbol.measurable_sinCut L ω)
    (Cvs.Finite.CutModeLevySeries.integrableOn_levy_sinCut hL ω)

theorem integrableOn_cosCut {σ L : ℝ} (hσ : 1 / 4 ≤ σ) (hL : 0 < L) (ω : ℝ) :
    IntegrableOn (fun u => densityS σ u * (cosCut L ω 0 - cosCut L ω (u / 2))) (Ioi 0) :=
  Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.integrableOn_densityS_mul hσ (Cvs.Finite.DiagonalCutSymbol.measurable_cosCut L ω)
    (Cvs.Finite.CutModeLevySeries.integrableOn_levy_cosCut hL ω)

theorem integrableOn_vcosCut {σ L : ℝ} (hσ : 1 / 4 ≤ σ) (hL : 0 < L) (ω : ℝ) :
    IntegrableOn (fun u => densityS σ u * (vcosCut L ω 0 - vcosCut L ω (u / 2))) (Ioi 0) :=
  Cvs.WeilForm.Archimedean.LevyDensityGeneralAbscissa.integrableOn_densityS_mul hσ (Cvs.Finite.DiagonalCutSymbol.measurable_vcosCut L ω)
    (Cvs.Finite.CutModeLevySeries.integrableOn_levy_vcosCut hL ω)

theorem Kc_off_eq {L : ℝ} {m n : ℤ} (hmn : m ≠ n) :
    Cvs.Finite.LevyKernelIncrement.Kc L m n
      = fun v => (1 / (π * ((n : ℝ) - m))) * sinCut L (2 * π * m / L) v
        + (-(1 / (π * ((n : ℝ) - m)))) * sinCut L (2 * π * n / L) v := by
  funext v
  unfold Cvs.Finite.LevyKernelIncrement.Kc Cvs.Finite.CosineModeOverlap.K sinCut
  by_cases hv : v ≤ L
  · rw [if_pos hv, if_pos hv, if_pos hv, if_neg hmn]
    have e1 : 2 * π * m * v / L = 2 * π * m / L * v := by ring
    have e2 : 2 * π * n * v / L = 2 * π * n / L * v := by ring
    rw [e1, e2]
    ring
  · rw [if_neg hv, if_neg hv, if_neg hv]
    ring

/-- The twisted pair value and matrix, in the shape of `Cvs.Finite.ModeSumPairValues.pairQ` and `Cvs.Finite.TruncationQuadraticForm.M`. -/
noncomputable def pairQS (σ q : ℝ) (w : ℕ → ℝ) (P : ℕ) (L : ℝ) (m n : ℤ) : ℝ :=
  PairS σ q w P (Cvs.Finite.LevyKernelIncrement.Kc L m n)

/-- cvsnum's twisted off-diagonal generator `F`. -/
noncomputable def genS (σ q : ℝ) (w : ℕ → ℝ) (P : ℕ) (L : ℝ) (m : ℤ) : ℝ :=
  -(Complex.digamma (zs σ (π * m / L))).im
    + ∑' k, tailS σ L k * imTermS σ (π * m / L) k - primeSumS w P (sinCut L (2 * π * m / L))

/-- cvsnum's twisted diagonal entry `Diag`. -/
noncomputable def diagS (σ q : ℝ) (w : ℕ → ℝ) (P : ℕ) (L : ℝ) (m : ℤ) : ℝ :=
  (2 * (archS0 σ q + ((Complex.digamma (zs σ (π * m / L))).re - (Complex.digamma (σ : ℂ)).re)
        - primeSumS w P (cosCut L (2 * π * m / L)))
    + 1 / L * (deriv Complex.digamma (zs σ (π * m / L))).re
    - 1 / L * ∑' k, tailS σ L k * cutTermS σ (π * m / L) k
    + 2 / L * primeSumS w P (vcosCut L (2 * π * m / L))) / 2

theorem half_freq (L : ℝ) (m : ℤ) : 2 * π * m / L / 2 = π * m / L := by ring

/-- **Off the diagonal, the twisted matrix is the Loewner matrix of `genS`.** -/
theorem pairQS_off {σ L : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (hσ : 1 / 4 ≤ σ) (hL : 0 < L)
    {m n : ℤ} (hmn : m ≠ n) :
    pairQS σ q w P L m n / 2
      = (genS σ q w P L m - genS σ q w P L n) / (2 * π * ((n : ℝ) - m)) := by
  unfold pairQS
  rw [Kc_off_eq hmn, PairS_add_smul q w P _ _ (integrableOn_sinCut hσ hL _)
    (integrableOn_sinCut hσ hL _),
    PairS_sinCut q w P hσ hL (Cvs.Finite.GeneratorClosedForm.sin_lattice hL m)
      (Cvs.Finite.GeneratorClosedForm.cos_lattice hL m),
    PairS_sinCut q w P hσ hL (Cvs.Finite.GeneratorClosedForm.sin_lattice hL n)
      (Cvs.Finite.GeneratorClosedForm.cos_lattice hL n), half_freq, half_freq]
  unfold genS
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hnm : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  field_simp
  ring

/-- **On the diagonal, the twisted matrix is `diagS`.** -/
theorem pairQS_diag {σ L : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (hσ : 1 / 4 ≤ σ) (hσ1 : σ < 1)
    (hL : 0 < L) (m : ℤ) :
    pairQS σ q w P L m m / 2 = diagS σ q w P L m := by
  unfold pairQS
  rw [Cvs.Finite.DiagonalCutSymbol.Kc_diag_eq, PairS_add_smul q w P _ _ (integrableOn_cosCut hσ hL _)
    (integrableOn_vcosCut hσ hL _),
    PairS_cosCut q w P hσ hL (Cvs.Finite.GeneratorClosedForm.sin_lattice hL m)
      (Cvs.Finite.GeneratorClosedForm.cos_lattice hL m),
    PairS_vcosCut q w P hσ hσ1 hL (Cvs.Finite.GeneratorClosedForm.sin_lattice hL m)
      (Cvs.Finite.GeneratorClosedForm.cos_lattice hL m), half_freq]
  unfold diagS
  have hL' : L ≠ 0 := hL.ne'
  field_simp
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The twisted CvS matrix on a mode set. -/
noncomputable def MS (σ q : ℝ) (w : ℕ → ℝ) (P : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => pairQS σ q w P L (mode i) (mode j) / 2

/-- **The twisted CvS matrix in closed form**, entry by entry: `hpform.py`'s entries. -/
theorem MS_apply_closed {σ L : ℝ} (q : ℝ) (w : ℕ → ℝ) (P : ℕ) (hσ : 1 / 4 ≤ σ) (hσ1 : σ < 1)
    (hL : 0 < L) {mode : ι → ℤ} (hinj : Function.Injective mode) (i j : ι) :
    MS σ q w P L mode i j
      = if i = j then diagS σ q w P L (mode i)
        else (genS σ q w P L (mode i) - genS σ q w P L (mode j))
          / (2 * π * ((mode j : ℝ) - mode i)) := by
  unfold MS
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, pairQS_diag q w P hσ hσ1 hL]
  · rw [if_neg hij]
    exact pairQS_off q w P hσ hL (fun h => hij (hinj h))

end Cvs.Finite.TwistedWindowMatrixClosed
