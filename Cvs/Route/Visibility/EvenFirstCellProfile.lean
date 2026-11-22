import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.TameCouplingBulkFloor
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even first cell

Write `e = (k_G + R_a k_G)/2` for the even window and `H = G + E_G/√a`. On the first cell `[a, 2a)` the even window is
`(a/θ)H(a/θ)/2`, and on its reciprocal image `(1/2, 1]` it is `√a H(θ)/2`; each cell carries `(a/4)∫_{(1/2,1]} H²`.
The cells are disjoint exactly when `a ≤ 1/4`, giving `(a/2)∫_{(1/2,1]} H² ≤ ‖e‖²`; for `a ≤ 1/2` one cell gives
`(a/4)∫_{(1/2,1]} H² ≤ ‖e‖²`. At the spine scale `a = 1/x` with `80 ≤ 2πx` this bounds the even part of a spine class.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Route.Visibility.EvenFirstCellProfile
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (window eimage)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)

/-- The even first-cell profile `H = G + E_G/√a`. -/
def cellProfile (a : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ := G u + eimage a G u / √a

/-- The even window on the first cell is `(a/θ)H(a/θ)/2`. -/
theorem even_first_cell_apply {a θ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hθ : θ ∈ Ico a (2 * a))
    (G : ℝ → ℝ) :
    (window a G θ + reciprocal a (window a G) θ) / 2 = a / θ * (cellProfile a G (a / θ) / 2) := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hθ1 : θ ∈ Icc a 1 := ⟨hθ.1, by linarith [hθ.2]⟩
  have hs : 0 < √a := sqrt_pos.mpr ha
  rw [Cvs.L2a.SpineProfileWindowNormPos.window_first_cell ha ha2 hθ, Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply ha hθ1, window,
    indicator_of_mem (Cvs.Xi.PhysicalReciprocalReflection.recip_mem_Icc ha hθ1), cellProfile]
  have hsa : √a * √a = a := mul_self_sqrt ha.le
  have key : √a / θ = a / θ / √a := by rw [eq_div_iff hs.ne', div_mul_eq_mul_div, hsa]
  rw [key]
  ring

/-- The even window on the reflected cell `(1/2, 1]` is `√a H(θ)/2`. -/
theorem even_reflected_cell_apply {a θ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hθ : θ ∈ Ioc (1 / 2) 1)
    (G : ℝ → ℝ) :
    (window a G θ + reciprocal a (window a G) θ) / 2 = √a * cellProfile a G θ / 2 := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθ1 : θ ∈ Icc a 1 := ⟨by linarith [hθ.1], hθ.2⟩
  have hc : a / θ ∈ Ico a (2 * a) := by
    refine ⟨(le_div_iff₀ hθ0).mpr (by nlinarith [hθ.2]), (div_lt_iff₀ hθ0).mpr (by nlinarith [hθ.1])⟩
  have hs : 0 < √a := sqrt_pos.mpr ha
  rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply ha hθ1, Cvs.L2a.SpineProfileWindowNormPos.window_first_cell ha ha2 hc, window, indicator_of_mem hθ1,
    cellProfile, show a / (a / θ) = θ by field_simp]
  have hsa : √a * √a = a := mul_self_sqrt ha.le
  field_simp
  rw [← hsa]
  ring

/-- The even window is square integrable for `a > 0` and `G` continuous on `[0, 1]`. -/
theorem integrable_even_sq {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1)) :
    Integrable (fun θ => ((window a G θ + reciprocal a (window a G) θ) / 2) ^ 2) := by
  have hmeas : Measurable (window a G) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).indicator measurableSet_Icc
  have hk : MemLp (window a G) 2 volume :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr (Cvs.L2a.SpineProfileWindowNormPos.integrable_window_sq ha hGc)
  have he : MemLp (fun θ => (window a G θ + reciprocal a (window a G) θ) / 2) 2 volume := by
    convert (hk.add (Cvs.Xi.PhysicalReciprocalReflection.memLp_reciprocal ha hk)).const_mul (1 / 2 : ℝ) using 1
    funext θ
    simp only [Pi.add_apply]
    ring
  exact he.integrable_sq

/-- Each cell carries `(a/4)∫_{(1/2,1]} H²`: the first cell. -/
theorem integral_first_cell_even {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (G : ℝ → ℝ) :
    ∫ θ in Ico a (2 * a), ((window a G θ + reciprocal a (window a G) θ) / 2) ^ 2
      = a / 4 * ∫ u in Ioc (1 / 2 : ℝ) 1, cellProfile a G u ^ 2 := by
  have h := Cvs.L2a.SpineProfileWindowNormPos.integral_first_cell ha (fun u => cellProfile a G u / 2)
  rw [setIntegral_congr_fun measurableSet_Ico fun θ hθ => by
    rw [even_first_cell_apply ha ha2 hθ G, mul_pow]]
  rw [h, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext u
  ring

/-- Each cell carries `(a/4)∫_{(1/2,1]} H²`: the reflected cell. -/
theorem integral_reflected_cell_even {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (G : ℝ → ℝ) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, ((window a G θ + reciprocal a (window a G) θ) / 2) ^ 2
      = a / 4 * ∫ u in Ioc (1 / 2 : ℝ) 1, cellProfile a G u ^ 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ hθ => by
    rw [even_reflected_cell_apply ha ha2 hθ G], ← integral_const_mul]
  congr 1
  funext u
  rw [div_pow, mul_pow, sq_sqrt ha.le]
  ring

/-- **The even first cell and its reflection**: `(a/2)∫_{(1/2,1]} (G + E_G/√a)² ≤ ‖(k_G + R_a k_G)/2‖²`
for `0 < a ≤ 1/4`, where `[a, 2a)` and `(1/2, 1]` are disjoint. -/
theorem even_first_cell_le {a : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) {G : ℝ → ℝ}
    (hGc : ContinuousOn G (Icc 0 1)) :
    a / 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, (G u + eimage a G u / √a) ^ 2
      ≤ ∫ θ, ((window a G θ + reciprocal a (window a G) θ) / 2) ^ 2 := by
  have ha2 : a ≤ 1 / 2 := by linarith
  set e : ℝ → ℝ := fun θ => ((window a G θ + reciprocal a (window a G) θ) / 2) ^ 2 with he
  have hint := integrable_even_sq ha hGc
  have hdisj : Disjoint (Ico a (2 * a)) (Ioc (1 / 2 : ℝ) 1) := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    linarith [h1.2, h2.1]
  have hU : ∫ θ in Ico a (2 * a) ∪ Ioc (1 / 2 : ℝ) 1, e θ
      = a / 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, (G u + eimage a G u / √a) ^ 2 := by
    rw [setIntegral_union hdisj measurableSet_Ioc hint.integrableOn hint.integrableOn,
      integral_first_cell_even ha ha2 G, integral_reflected_cell_even ha ha2 G]
    simp only [cellProfile]
    ring
  rw [← hU]
  exact setIntegral_le_integral hint (ae_of_all _ fun _ => sq_nonneg _)

/-- `80 ≤ 2πx` puts the spine scale `1/x` below `1/4`. -/
theorem inv_le_quarter {x : ℕ} (hx : 80 ≤ 2 * π * x) : 1 / (x : ℝ) ≤ 1 / 4 := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx4 : (4 : ℝ) ≤ x := by nlinarith [Real.pi_lt_four]
  rw [div_le_div_iff₀ hx0 (by norm_num)]
  linarith

/-- **The even part of a spine class bounds its even first cell**: for `80 ≤ 2πx`, `G` the spine profile of `a` and
`E_G` its E-image at scale `1/x`, `(1/(2x))∫_{(1/2,1]} (G + √x E_G)² ≤ ‖even part of the spine class‖²`. -/
theorem norm_evenPart_spineMap_ge {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    1 / (x : ℝ) / 2 * ∫ u in Ioc (1 / 2 : ℝ) 1,
        (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a u
          + eimage (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) u / √(1 / (x : ℝ))) ^ 2
      ≤ ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2 := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hGc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (Icc 0 1) :=
    (Cvs.L2a.SpineProfileWindowNormPos.continuousOn_spineG _ a).mono (Icc_subset_Icc (by norm_num) le_rfl)
  rw [Cvs.StepA.LowEigenvalueCountSpine.evenPart_spineMap_eq_wv hx a, Cvs.Route.TameCouplingBulkFloor.norm_wv hx0,
    sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  exact even_first_cell_le (one_div_pos.mpr hx0) (inv_le_quarter hx) hGc

end Cvs.Route.Visibility.EvenFirstCellProfile
