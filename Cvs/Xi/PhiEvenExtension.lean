import Mathlib
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even extension of `Φ` to the line

Reflecting `Φ` through the origin gives a function on the whole line, and reflection preserves
Lebesgue measure, so integrability on the half line carries across. The two halves then cover the
line, and the extension is integrable on it.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Xi.PhiEvenExtension

open Cvs.Xi.RiemannPhiKernel

/-- The even extension of `Φ` to the line. -/
def phiEven (u : ℝ) : ℂ := ((riemannPhi |u| : ℝ) : ℂ)

theorem phiEven_neg (u : ℝ) : phiEven (-u) = phiEven u := by
  simp only [phiEven, abs_neg]

theorem phiEven_of_pos {u : ℝ} (hu : 0 < u) : phiEven u = ((riemannPhi u : ℝ) : ℂ) := by
  simp only [phiEven, abs_of_pos hu]

theorem integrableOn_phiEven_Ioi : IntegrableOn phiEven (Ioi (0 : ℝ)) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    (Cvs.Xi.XiValueAtOrigin.integrableOn_riemannPhi.ofReal (𝕜 := ℂ))
    (fun u hu => ?_) measurableSet_Ioi
  exact (phiEven_of_pos hu).symm

theorem integrableOn_phiEven_Ici : IntegrableOn phiEven (Ici (0 : ℝ)) :=
  Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi integrableOn_phiEven_Ioi

/-- **Reflection carries integrability to the negative half line.** -/
theorem integrableOn_phiEven_Iic : IntegrableOn phiEven (Iic (0 : ℝ)) := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := phiEven) (s := Ici (0 : ℝ))).2
    integrableOn_phiEven_Ici
  have hset : (fun x : ℝ => -x) ⁻¹' (Ici (0 : ℝ)) = Iic (0 : ℝ) := by
    ext x
    simp
  have hfun : phiEven ∘ (fun x : ℝ => -x) = phiEven := funext phiEven_neg
  rwa [hset, hfun] at h

/-- **The even extension is integrable on the line.** -/
theorem integrable_phiEven : Integrable phiEven := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact integrableOn_phiEven_Iic.union integrableOn_phiEven_Ioi

end Cvs.Xi.PhiEvenExtension
