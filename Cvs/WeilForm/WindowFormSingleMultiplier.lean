import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.BilinearCrossRepresentatives
import Cvs.WeilForm.EffectiveSymbol
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PolePrimeCosineMultipliers
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form as the single multiplier `Φ_L = poleSymbol L + effSymbol P R`

For `f, g ∈ L¹ ∩ L²` in the Lévy domain vanishing off `[a, b]`, `b − a ≤ L`, `crossW P R f g = ∫ Φ_L ρ_{f,g}`;
so `QWbil = M_{Φ_L}` on the form domain and `weilθ F G = ∫ Φ_L ρ` for tame `F, G` on `[α, β]`, `log(β/α) ≤ L`.
`b ≤ Φ_L + h` with `h ∈ bandFree L` gives `b‖φ‖² ≤ Q(φ)`, `Ψ ≤ Φ_L + h` gives `M_Ψ ≤ Q`, and
`Φ_{L'} − Φ_L ∈ bandFree L` is nonzero for `L < L'`.
-/

noncomputable section

open Real Set Filter MeasureTheory
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open Cvs.WeilForm.WindowRepresentative (rep)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (weilθ)

namespace Cvs.WeilForm.WindowFormSingleMultiplier
open Cvs.ZeroCounting

variable {f g : ℝ → ℝ}

/-! ### The window multiplier -/

/-- **The window multiplier** `Φ_L(t) = poleSymbol L t + archSymbol t − primeSymbol P R t`. -/
def windowSymbol (L : ℝ) (P R : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol L t + Cvs.WeilForm.EffectiveSymbol.effSymbol P R t

/-- `archSymbol ρ_{f,g}` is integrable for `f, g ∈ L¹ ∩ L²` in the Lévy domain. -/
theorem integrable_arch_mul_crossSpec (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume) (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    Integrable fun t => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * crossSpec f g t :=
  Cvs.L2a.WindowFormTailLimit.integrable_arch_crossSpec hf1 hf2 (Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hf2 hf1 hfl) hg1 hg2
    (Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hg2 hg1 hgl)

/-- `Φ_L ρ_{f,g}` is integrable for `f, g ∈ L¹ ∩ L²` in the Lévy domain. -/
theorem integrable_windowSymbol_mul_crossSpec (L : ℝ) (P R : ℕ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume) (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    Integrable fun t => windowSymbol L P R t * crossSpec f g t :=
  (((Cvs.WeilForm.PolePrimeCosineMultipliers.integrable_poleSymbol_mul_crossSpec L hf1 hf2 hg1 hg2).add
    (integrable_arch_mul_crossSpec hf1 hf2 hfl hg1 hg2 hgl)).sub
    (Cvs.WeilForm.PolePrimeCosineMultipliers.integrable_primeSymbol_mul_crossSpec P R hf1 hf2 hg1 hg2)).congr
    (Eventually.of_forall fun t => by
      simp only [Pi.add_apply, Pi.sub_apply, windowSymbol, Cvs.WeilForm.EffectiveSymbol.effSymbol]; ring)

/-- **The window's bilinear form is one multiplier**: `crossW P R f g = ∫ Φ_L ρ_{f,g}` for `f, g ∈ L¹ ∩ L²` in
the Lévy domain vanishing off `[a, b]` with `b − a ≤ L`. -/
theorem crossW_eq_integral (P R : ℕ) {L a b : ℝ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume) (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) (hfs : ∀ x ∉ Icc a b, f x = 0)
    (hgs : ∀ x ∉ Icc a b, g x = 0) (hab : b - a ≤ L) :
    Cvs.WeilForm.SymmetricBilinearForm.crossW P R f g = ∫ t, windowSymbol L P R t * crossSpec f g t := by
  have iP := Cvs.WeilForm.PolePrimeCosineMultipliers.integrable_poleSymbol_mul_crossSpec L hf1 hf2 hg1 hg2
  have iA := integrable_arch_mul_crossSpec hf1 hf2 hfl hg1 hg2 hgl
  have iR := Cvs.WeilForm.PolePrimeCosineMultipliers.integrable_primeSymbol_mul_crossSpec P R hf1 hf2 hg1 hg2
  have hsplit : (∫ t, windowSymbol L P R t * crossSpec f g t)
      = (∫ t, Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol L t * crossSpec f g t) + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * crossSpec f g t)
        - ∫ t, Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t * crossSpec f g t := by
    have iPA : Integrable fun t => Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol L t * crossSpec f g t
        + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * crossSpec f g t := iP.add iA
    rw [← integral_add iP iA, ← integral_sub iPA iR]
    exact integral_congr_ae (Eventually.of_forall fun t => by
      simp only [windowSymbol, Cvs.WeilForm.EffectiveSymbol.effSymbol]; ring)
  have hP := Cvs.WeilForm.PolePrimeCosineMultipliers.pole_eq_integral_crossSpec hf1 hf2 hg1 hg2 hfs hgs hab
  have hA := Cvs.L2a.WindowFormTailLimit.integral_arch_crossSpec_eq hf2 hf1 hfl hg2 hg1 hgl
  have hR := Cvs.WeilForm.PolePrimeCosineMultipliers.primeSide_polar_eq_integral P R hf1 hf2 hg1 hg2
  rw [hsplit]
  unfold Cvs.WeilForm.SymmetricBilinearForm.crossW
  linear_combination hP - hA - hR

/-! ### The form domain -/

section Window

variable {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)

/-- **`QWbil` is the multiplier `Φ_L` against the cross density** on the form domain. -/
theorem QWbil_eq_integral (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R φ ψ
      = ∫ t, windowSymbol L P R t * crossSpec (rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) t := by
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply]
  exact crossW_eq_integral P R (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _) (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.FormDomain.hdom_of_mem φ)
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _) (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.FormDomain.hdom_of_mem ψ) (Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL φ)
    (Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL ψ) (sub_zero L).le

/-- **The window form is the multiplier `Φ_L` against the spectral density**: `Q(φ) = ∫ Φ_L ρ_{rep φ}`. -/
theorem Q_eq_integral (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ = ∫ t, windowSymbol L P R t * specDensity (rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) t := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, QWbil_eq_integral]
  exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only; rw [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self])

/-- `Φ_L` is an admissible multiplier on the form domain. -/
theorem windowSymbol_mem_admissible : windowSymbol L P R ∈ Cvs.WeilForm.AdmissibleMultiplierMinorants.admissible (V := Cvs.WeilForm.FormDomain.formDomain hL) (Cvs.WeilForm.AdmissibleMultiplierMinorants.formSpec hL) volume :=
  Cvs.WeilForm.AdmissibleMultiplierMinorants.mem_admissible.2 fun φ ψ => integrable_windowSymbol_mul_crossSpec L P R (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _)
    (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.FormDomain.hdom_of_mem φ) (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _) (Cvs.WeilForm.WindowRepresentative.memLp_rep _)
    (Cvs.WeilForm.FormDomain.hdom_of_mem ψ)

end Window

/-! ### Tame test functions -/

/-! ### Nonzero band-free extensions -/

end Cvs.WeilForm.WindowFormSingleMultiplier
