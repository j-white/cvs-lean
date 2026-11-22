import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ParallelogramLaw
import Cvs.WeilForm.PrimeShiftOperator
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WeilFormReflection
import Cvs.WeilForm.WindowMomentsTranslationInvariant
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# Nesting the windows: the centred embedding and the monotone bottom

The window at scale `L` embeds isometrically into the window at scale `L' ≥ L` by translation to
the common centre. The Weil form is unchanged once the prime side is complete at the smaller
scale, the form domain is carried along, and the bottom is antitone in the scale.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.NestedWindowsMonotoneBottom

variable {L L' : ℝ}

/-- The centring shift. -/
def shift (L L' : ℝ) : ℝ := (L' - L) / 2

/-- **The centred embedding** of the window at `L` into the window at `L'`. -/
def embed (L L' : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Cvs.WeilForm.WeilFormOnWindowL2.window L' :=
  Cvs.WeilForm.PrimeShiftOperator.cutLp L' (Cvs.WeilForm.PrimeShiftOperator.transLp (shift L L') φ)

/-- The translate of the representative vanishes off the larger window. -/
theorem rep_shift_eq_zero (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    {s : ℝ} (hs : s ∉ Ioc (0:ℝ) L') :
    Cvs.WeilForm.WindowRepresentative.rep φ (s - shift L L') = 0 := by
  apply Cvs.WeilForm.WindowRepresentative.rep_supp
  intro h
  apply hs
  unfold shift at h
  constructor <;> linarith [h.1, h.2]

/-- **The embedding acts by the translated representative.** -/
theorem embed_ae (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ⇑((embed L L' φ : Cvs.WeilForm.WeilFormOnWindowL2.window L') : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep φ (s - shift L L') := by
  unfold embed
  have h1 := Cvs.WeilForm.PrimeShiftOperator.cutLp_ae L' (Cvs.WeilForm.PrimeShiftOperator.transLp (shift L L') φ)
  have h2 := Cvs.WeilForm.PrimeShiftOperator.transLp_ae (shift L L') (φ : Lp ℝ 2 (volume : Measure ℝ))
  have h3 := Cvs.WeilForm.PrimeShiftOperator.ae_eq_sub (shift L L') (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ)
  filter_upwards [h1, h2.indicator (s := Ioc (0:ℝ) L'), h3.indicator (s := Ioc (0:ℝ) L')]
    with s hs1 hs2 hs3
  rw [hs1, hs2]
  change (Ioc (0:ℝ) L').indicator (fun s => Cvs.WeilForm.WindowRepresentative.fn φ (s - shift L L')) s = _
  rw [hs3]
  by_cases hs : s ∈ Ioc (0:ℝ) L'
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs, rep_shift_eq_zero hL hLL φ hs]

/-- **The embedding is the translate, as a class.** -/
theorem embed_coe (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ((embed L L' φ : Cvs.WeilForm.WeilFormOnWindowL2.window L') : Lp ℝ 2 (volume : Measure ℝ))
      = Cvs.WeilForm.PrimeShiftOperator.transLp (shift L L') φ := by
  apply Lp.ext
  refine (embed_ae hL hLL φ).trans ?_
  have h2 := Cvs.WeilForm.PrimeShiftOperator.transLp_ae (shift L L') (φ : Lp ℝ 2 (volume : Measure ℝ))
  have h3 := Cvs.WeilForm.PrimeShiftOperator.ae_eq_sub (shift L L') (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ)
  exact (h3.symm.trans h2.symm)

/-- **The embedding is an isometry.** -/
theorem norm_embed (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ‖embed L L' φ‖ = ‖φ‖ := by
  rw [Submodule.coe_norm, embed_coe hL hLL φ, Cvs.WeilForm.PrimeShiftOperator.norm_transLp,
    ← Submodule.coe_norm]

/-- **The self-convolution of a window class vanishes at lags of the window's length or more.** -/
theorem selfConvolution_rep_eq_zero_of_le (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {u : ℝ}
    (hu : L ≤ u) : selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) u = 0 := by
  unfold selfConvolution
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Ioc (0:ℝ) L
  · have : s + u ∉ Ioc (0:ℝ) L := fun h => by linarith [hs.1, h.2]
    simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ _ this]
  · simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ _ hs]

/-- **A complete truncation of the prime side is not changed by enlarging it.**  With every prime
power below `e^L` already included, the extra terms have lag at least `L` and vanish. -/
theorem primeSide_eq_of_complete {P R P' R' : ℕ} (hPP : P ≤ P') (hRR : R ≤ R')
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    primePowerSideTruncated P' R' (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ))
      = primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ)) := by
  unfold primePowerSideTruncated
  set g := selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) with hg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- a term with lag `≥ L` vanishes
  have hterm : ∀ (p r : ℕ), Nat.Prime p → 1 ≤ r → L ≤ r * Real.log p →
      primePowerWeight p r * (g (r * Real.log p) + g (-(r * Real.log p))) = 0 := by
    intro p r _ _ hlag
    rw [hg, Cvs.WeilForm.WeilFormReflection.selfConvolution_neg,
      selfConvolution_rep_eq_zero_of_le φ hlag]
    ring
  -- the inner sums agree on every prime `p ≤ P`
  have hinner : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
      (∑ r ∈ Finset.Icc 1 R', primePowerWeight p r * (g (r * Real.log p) + g (-(r * Real.log p))))
        = ∑ r ∈ Finset.Icc 1 R,
            primePowerWeight p r * (g (r * Real.log p) + g (-(r * Real.log p))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    symm
    apply Finset.sum_subset
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    · intro r hr hrn
      simp only [Finset.mem_Icc, not_and, not_le] at hr hrn
      have hrR : R < r := hrn hr.1
      apply hterm p r hp.2 hr.1
      have h2p : (2:ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) h2p
      have hr' : (R:ℝ) + 1 ≤ r := by exact_mod_cast hrR
      have hr0 : (0:ℝ) ≤ r := by positivity
      calc L ≤ R * Real.log 2 := hR
        _ ≤ r * Real.log 2 := by nlinarith
        _ ≤ r * Real.log p := by nlinarith
  -- and the extra primes contribute nothing
  calc (∑ p ∈ (Finset.range (P' + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R',
          primePowerWeight p r * (g (r * Real.log p) + g (-(r * Real.log p))))
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R',
          primePowerWeight p r * (g (r * Real.log p) + g (-(r * Real.log p))) := by
        symm
        apply Finset.sum_subset
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
        · intro p hp hpn
          simp only [Finset.mem_filter, Finset.mem_range, not_and] at hp hpn
          have hpP : P < p := by
            by_contra h
            push Not at h
            exact hpn (by omega) hp.2
          have hlogp : L ≤ Real.log p := by
            have h1 : Real.exp L ≤ p := le_trans hP (by exact_mod_cast hpP.le)
            rw [← Real.log_exp L]
            exact Real.log_le_log (Real.exp_pos L) h1
          apply Finset.sum_eq_zero
          intro r hr
          simp only [Finset.mem_Icc] at hr
          apply hterm p r hp.2 hr.1
          have h1r : (1:ℝ) ≤ r := by exact_mod_cast hr.1
          have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_le)
          nlinarith
    _ = _ := Finset.sum_congr rfl hinner

/-- **The form is unchanged by the embedding**, once the prime side is complete at the smaller
scale. -/
theorem weilQW_embed (hL : 0 ≤ L) (hLL : L ≤ L') {P R P' R' : ℕ} (hPP : P ≤ P') (hRR : R ≤ R')
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.weilQW P' R' (embed L L' φ) = Cvs.WeilForm.WindowRepresentative.weilQW P R φ := by
  unfold Cvs.WeilForm.WindowRepresentative.weilQW
  rw [Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (embed_ae hL hLL φ),
    Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ),
    Cvs.WeilForm.WindowMomentsTranslationInvariant.weilForm_translate]
  unfold Cvs.WeilForm.SelfConvolutionFunctional.weilForm
  rw [primeSide_eq_of_complete hPP hRR hP hR φ]

/-- The representative of the embedding is the translated representative, almost everywhere. -/
theorem rep_embed_ae (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (embed L L' φ)
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep φ (s - shift L L') :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep (embed L L' φ)).symm.trans (embed_ae hL hLL φ)

/-- **The Lévy integrand is carried along.** -/
theorem levy_rep_embed (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (embed L L' φ))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  have h : selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (embed L L' φ))
      = selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) := by
    funext v
    rw [Cvs.WeilForm.ParallelogramLaw.selfConvolution_congr_ae (rep_embed_ae hL hLL φ) v,
      Cvs.WeilForm.WindowMomentsTranslationInvariant.selfConvolution_translate]
  funext u
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  rw [h]

/-- **The embedding on the form domain.** -/
def embedD (hL : 0 ≤ L) (hL' : 0 ≤ L') (hLL : L ≤ L')
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.FormDomain.formDomain hL' :=
  ⟨embed L L' φ, by
    show IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (embed L L' φ)))
      (Set.Ioi 0) volume
    rw [levy_rep_embed hL hLL φ]
    exact φ.2⟩

/-- **The embedding commutes with the midpoint reflection.** -/
theorem reflW_embed (hL : 0 ≤ L) (hLL : L ≤ L') (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflW (embed L L' φ) = embed L L' (Cvs.WeilForm.WindowReflectionSymmetry.reflW φ) := by
  apply Subtype.ext
  apply Lp.ext
  -- left side: the reflection of the embedded class
  have hl : ⇑((Cvs.WeilForm.WindowReflectionSymmetry.reflW (embed L L' φ) : Cvs.WeilForm.WeilFormOnWindowL2.window L')
      : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep φ (L' - s - shift L L') := by
    have h1 := Cvs.WeilForm.WindowReflectionSymmetry.refl_ae L'
      ((embed L L' φ : Cvs.WeilForm.WeilFormOnWindowL2.window L') : Lp ℝ 2 (volume : Measure ℝ))
    have h2 := (MeasureTheory.Measure.measurePreserving_sub_left volume L').quasiMeasurePreserving.ae_eq_comp
      (embed_ae hL hLL φ)
    exact h1.trans h2
  -- right side: the embedding of the reflected class
  have hr : ⇑((embed L L' (Cvs.WeilForm.WindowReflectionSymmetry.reflW φ) : Cvs.WeilForm.WeilFormOnWindowL2.window L')
      : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep φ (L' - s - shift L L') := by
    have h1 := embed_ae hL hLL (Cvs.WeilForm.WindowReflectionSymmetry.reflW φ)
    have h2 := Cvs.WeilForm.PrimeShiftOperator.ae_eq_sub (shift L L')
      (Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae φ)
    refine (h1.trans h2).trans (Filter.Eventually.of_forall fun s => ?_)
    simp only
    congr 1
    unfold shift; ring
  exact hl.trans hr.symm

/-- **The embedding on the form domain commutes with the reflection.** -/
theorem reflD_embedD (hL : 0 ≤ L) (hL' : 0 ≤ L') (hLL : L ≤ L')
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD hL' (embedD hL hL' hLL φ)
      = embedD hL hL' hLL (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ) := by
  apply Subtype.ext
  exact reflW_embed hL hLL φ

end Cvs.WeilForm.NestedWindowsMonotoneBottom
