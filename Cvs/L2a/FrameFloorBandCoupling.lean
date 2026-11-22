import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.CornerSplitSqrtFloor
import Cvs.L2a.DefectChargeSqrtN
import Cvs.L2a.FrameFloorJumpAbsorption
import Cvs.L2a.MirrorFloor
import Cvs.L2a.MirrorSplitDefect
import Cvs.L2a.ParametricFloorSqrtN
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.ReflectionFloor
import Cvs.L2a.SubfamilyDefectCharge
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.QuinticSmoothStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frame floor with the band charged through band coupling

`FrameFloorIntegerM`'s `√N` floor with `1 − ε ≤ τᵢ` asked only off a finite band `S`. The defect splits as `e₁ = e₁^{Sᶜ} + e₁^S`:
the deep part keeps `DefectChargeSqrtN`'s charge `2ε√P√N + 3εP`, and the band part is (BC), `|re⟨e₁^S, 2E − wΦ⟩| ≤ θP`.
So `(½ − 3ε − η − r − θ)P ≤ N + 2ε√P√N`, and for `A = ½ − 3ε − η − r − θ ≥ 0`,
`(√(A + ε²) − ε)²·P ≤ N` and `(√(A + ε²) − ε)²·Σ aᵢ²∫₁^X ψᵢ² ≤ N`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.CornerSplitSqrtFloor

namespace Cvs.L2a.FrameFloorBandCoupling

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-! ### Masked sums and the frame test function -/

/-- A masked full sum is the sum over the mask: `Σᵢ [i ∈ S] aᵢ fᵢ = Σ_{i ∈ S} aᵢ fᵢ`. -/
theorem sum_ite_mem_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (a f : ι → ℝ) :
    ∑ i, (if i ∈ S then a i else 0) * f i = ∑ i ∈ S, a i * f i := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The frame test function `G = 2E − wΦ` lies in `L²(1, ∞)` for `Φ ∈ L²(1, ∞)`, measurable `0 ≤ w ≤ 1`, `X ≥ 1`. -/
theorem memLp_frame {Φ w : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hΦ : MemLp Φ 2 μ₁) (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    MemLp (fun x => 2 * dilSum Φ X x - w x * Φ x) 2 μ₁ := by
  obtain ⟨-, -, -, e, -, -, -, he⟩ := exists_core_arm hX hΦ hwm hw0 hw1
  have h1 : MemLp (dilSum Φ X) 2 μ₀ := by
    refine MemLp.ae_eq ?_ (Lp.memLp e).re
    filter_upwards [he] with x hx
    rw [hx]
    simp
  have h2 : MemLp (dilSum Φ X) 2 μ₁ :=
    h1.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)
  have h3 : MemLp (fun x => w x * Φ x) 2 μ₁ :=
    hΦ.of_le (hwm.aestronglyMeasurable.mul hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨by linarith [hw0 x], hw1 x⟩))
  exact (h2.const_mul 2).sub h3

variable {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-! ### The deep defect and the band defect -/

/-- **The deep defect**: with `1 − ε ≤ τᵢ` off `S` and `0 ≤ ε`, `∫_{Ioi 1} |e₁^{Sᶜ}|² ≤ ε²P`, `P = ∫_{Ioi 1} Φ²`. -/
theorem integral_norm_eOne_sq_compl_le [DecidableEq ι] (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i ∉ S, 1 - ε ≤ μ i * √(c / (2 * π))) :
    ∫ y in Ioi 1, ‖eOne c (fun ξ => ∑ i ∈ Sᶜ, a i * psi c (g i) ξ) y‖ ^ 2
      ≤ ε ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  set b : ι → ℝ := fun i => if i ∈ Sᶜ then a i else 0 with hb
  have hfun : (fun ξ => ∑ i ∈ Sᶜ, a i * psi c (g i) ξ) = fun ξ => ∑ i, b i * psi c (g i) ξ :=
    funext fun ξ => (sum_ite_mem_mul Sᶜ a fun i => psi c (g i) ξ).symm
  obtain ⟨ψL, -, -, -, -, hKψ, -, hψn, -⟩ := rung_span_L2 a hg hg₁ hg₂c hang hc hχ heven hμ
  rw [hfun, integral_norm_eOne_sq_Ioi_one b hg hg₁ hg₂c hang hc hχ heven hμ,
    Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hM : 0 ≤ ∫ x in Ioi 1, psi c (g i) x ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  by_cases hi : i ∈ S
  · have hbi : b i = 0 := by simp [hb, hi]
    rw [hbi, zero_mul, zero_pow two_ne_zero, zero_mul]
    positivity
  · have hbi : b i = a i := by simp [hb, hi]
    rw [hbi]
    rcases hM.eq_or_lt with hM0 | hM0
    · rw [← hM0]; simp
    · have hp : 0 < ‖ψL i‖ := by
        have h2 := hψn i
        nlinarith [norm_nonneg (ψL i)]
      have hK := norm_Kop_le hc (ψL i)
      rw [hKψ i, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg] at hK
      have hτ1 : |μ i * √(c / (2 * π))| ≤ 1 := le_of_mul_le_mul_right (by linarith) hp
      have h1 : (1 - μ i * √(c / (2 * π))) ^ 2 ≤ ε ^ 2 := by
        have := hτ i hi
        have := (abs_le.1 hτ1).2
        nlinarith
      calc (a i * (1 - μ i * √(c / (2 * π)))) ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2
          = (1 - μ i * √(c / (2 * π))) ^ 2 * (a i ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2) := by ring
        _ ≤ ε ^ 2 * (a i ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg _) hM)

/-- **The band defect against `G`**: `∫_{Ioi 1} re(e₁^S)·G = Σ_{i ∈ S} aᵢ(1 − τᵢ)⟨ψᵢ, G⟩` for `G ∈ L²(1, ∞)`. -/
theorem integral_eOne_band_re_mul (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {G : ℝ → ℝ} (hG : MemLp G 2 μ₁) :
    ∫ x in Ioi 1, (eOne c (fun ξ => ∑ i ∈ S, a i * psi c (g i) ξ) x).re * G x
      = ∑ i ∈ S, a i * (1 - μ i * √(c / (2 * π))) * ∫ x in Ioi 1, psi c (g i) x * G x := by
  classical
  have hfun : (fun ξ => ∑ i ∈ S, a i * psi c (g i) ξ)
      = fun ξ => ∑ i, (if i ∈ S then a i else 0) * psi c (g i) ξ :=
    funext fun ξ => (sum_ite_mem_mul S a fun i => psi c (g i) ξ).symm
  rw [hfun, Cvs.L2a.SubfamilyDefectCharge.integral_eOne_re_mul _ hg hg₁ hg₂c hang hc heven hμ hG]
  simp only [mul_assoc]
  exact sum_ite_mem_mul S a _

/-- **(BC)**, band coupling at `X`: `|Σ_{i ∈ S} aᵢ(1 − τᵢ)⟨ψᵢ, 2E − wΦ⟩_{L²(1,∞)}| ≤ θP`, with `τᵢ = μᵢ√(c/2π)`,
`Φ = Σ aᵢψᵢ`, `E = dilSum Φ X` and `P = ∫_{Ioi 1} Φ²`. -/
def BandCoupling (c : ℝ) (g : ι → ℝ → ℝ) (μ a : ι → ℝ) (S : Finset ι) (w : ℝ → ℝ) (X θ : ℝ) : Prop :=
  |∑ i ∈ S, a i * (1 - μ i * √(c / (2 * π))) * ∫ x in Ioi 1, psi c (g i) x
      * (2 * dilSum (fun ξ => ∑ j, a j * psi c (g j) ξ) X x - w x * ∑ j, a j * psi c (g j) x)|
    ≤ θ * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2

/-- **(BC) is the band defect bound**: `BandCoupling` holds iff `|∫_{Ioi 1} re(e₁^S)·(2E − wΦ)| ≤ θP`. -/
theorem bandCoupling_iff (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (θ : ℝ) :
    BandCoupling c g μ a S w X θ
      ↔ |∫ x in Ioi 1, (eOne c (fun ξ => ∑ i ∈ S, a i * psi c (g i) ξ) x).re
          * (2 * dilSum (fun ξ => ∑ i, a i * psi c (g i) ξ) X x - w x * ∑ i, a i * psi c (g i) x)|
        ≤ θ * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  have hΦr : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  rw [integral_eOne_band_re_mul a hg hg₁ hg₂c hang hc heven hμ S (memLp_frame hX hΦr hwm hw0 hw1)]
  rfl

/-! ### The split floor -/

/-- **The split quadratic floor**: `FrameFloorIntegerM`'s `FF_of_corners_sum_G` hypotheses with `1 − ε ≤ τᵢ` only off `S`, and the
band defect bound `|∫_{Ioi 1} re(e₁^S)·(2E − wΦ)| ≤ θP`: `(½ − 3ε − η − r − θ)P ≤ N + 2ε√P√N`. -/
theorem quad_of_corners_split_eOne {St : ℝ → ℝ} (hS : IsStep St) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i ∉ S, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r θ : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hBC : |∫ x in Ioi 1, (eOne c (fun ξ => ∑ i ∈ S, a i * psi c (g i) ξ) x).re
        * (2 * dilSum (fun ξ => ∑ i, a i * psi c (g i) ξ) X x - w x * ∑ i, a i * psi c (g i) x)|
      ≤ θ * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2) :
    (1 / 2 - 3 * ε - η - r - θ) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ (∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2)
        + 2 * ε * (√(∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
          * √(∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2)) := by
  classical
  have hψ : ∀ i, MemLp (psi c (g i)) 2 μ₁ := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc
  have hΦr : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum Finset.univ fun i _ => (hψ i).const_mul (a i)
  have hΦBr : MemLp (fun ξ => ∑ i ∈ S, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum S fun i _ => (hψ i).const_mul (a i)
  have hΦDr : MemLp (fun ξ => ∑ i ∈ Sᶜ, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum Sᶜ fun i _ => (hψ i).const_mul (a i)
  have hdeepI := integral_norm_eOne_sq_compl_le a hg hg₁ hg₂c hang hc hχ heven hμ S hε hτ
  obtain ⟨ψL, F, -, hF, -, -, -, -, hF2⟩ := rung_span_L2 a hg hg₁ hg₂c hang hc hχ heven hμ
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ, Φ = fun ξ => ∑ i, a i * psi c (g i) ξ := ⟨_, rfl⟩
  obtain ⟨ΦB, hΦB⟩ : ∃ Φ : ℝ → ℝ, Φ = fun ξ => ∑ i ∈ S, a i * psi c (g i) ξ := ⟨_, rfl⟩
  obtain ⟨ΦD, hΦD⟩ : ∃ Φ : ℝ → ℝ, Φ = fun ξ => ∑ i ∈ Sᶜ, a i * psi c (g i) ξ := ⟨_, rfl⟩
  rw [← hΦB] at hΦBr hBC
  rw [← hΦD] at hΦDr hdeepI
  rw [← hΦdef] at hΦr hsum hBC ⊢
  have key : ∀ ξ, ∑ i, a i * psi c (g i) ξ = Φ ξ := fun ξ => by rw [hΦdef]
  simp only [key] at hη hF hF2 hBC hdeepI hsum ⊢
  set P := ∫ ξ in Ioi 1, Φ ξ ^ 2 with hPdef
  set N := ∫ y in Ioi 1, posTail Φ X y ^ 2 with hNdef
  have hP : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hN : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  -- the band/deep split of `1_(1,∞)Φ`
  have hsplitΦ : ∀ x, (Ioi (1 : ℝ)).indicator Φ x
      = (Ioi (1 : ℝ)).indicator ΦD x + (Ioi (1 : ℝ)).indicator ΦB x := fun x => by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, hΦdef, hΦD, hΦB]
      exact (Finset.sum_compl_add_sum S _).symm
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]
  have lift : ∀ {f : ℝ → ℝ}, MemLp f 2 μ₁ →
      MemLp (fun x => (((Ioi (1 : ℝ)).indicator f x : ℝ) : ℂ)) 2 μ₀ := fun hf =>
    (((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hf).restrict _).ofReal
  set hD : H₀ := (lift hΦDr).toLp _ with hhD
  set hB : H₀ := (lift hΦBr).toLp _ with hhB
  have hDae : (hD : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator ΦD x : ℝ) : ℂ) := (lift hΦDr).coeFn_toLp
  have hBae : (hB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator ΦB x : ℝ) : ℂ) := (lift hΦBr).coeFn_toLp
  obtain ⟨u, aB, aF, e, hu, haB, haF, he⟩ := exists_core_arm hX hΦr hwm hw0 hw1
  obtain ⟨hh, ha, -, -, -⟩ := core_arm_ae hX hwX hu haB haF he
  have hhs : u + (aB + aF) = hD + hB := by
    refine Lp.ext ?_
    filter_upwards [hh, Lp.coeFn_add hD hB, hDae, hBae] with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, ← Complex.ofReal_add, hsplitΦ]
  -- the core/arm identity and the corner split
  have hid := core_arm_identity_L2 hc hX hwX hu haB haF he
  have hPos := corePos_eq hc hX hwX hu haB haF he
  have hDil := coreDil_eq hc hX hwX hu haB haF he
  have hcorner := coreDil_eq_cornerG hS hc hX hwX hΦr δ hu haB haF he
  have hpos := pos_nonneg (Φ := Φ) (χ := w) (fun x _ => ⟨hw0 x, hw1 x⟩) (u + Uop hc (aB + aF))
    (e - Uop hc aB)
  rw [hPos] at hpos
  -- the `η` term: `re⟨a, Ja⟩ ≥ −ηP`
  have hw : ∀ x, |w x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hw0 x], hw1 x⟩
  have hWF : ((Wop hwm hw F : H₁) : ℝ → ℂ) =ᵐ[μ₁] fun x => ((w x * Φ x : ℝ) : ℂ) := by
    filter_upwards [(memLp_weight hwm hw (Lp.memLp F)).coeFn_toLp, hF] with x h1 h2
    change ((memLp_weight hwm hw (Lp.memLp F)).toLp _ : ℝ → ℂ) x = _
    rw [h1, h2]; push_cast; ring
  have hae : aB + aF = ext (Wop hwm hw F) := by
    refine Lp.ext ?_
    filter_upwards [ha, coeFn_ext (Wop hwm hw F), ae_restrict_of_ae (indicator_congr hWF)] with y h1 h2 h3
    rw [h1, h2, h3, ofReal_indicator]
  have hη' : ‖Wop hwm hw (Kop hc (Wop hwm hw F))‖ ≤ η * ‖F‖ := by
    have hcongr : calK c ((Ioi (1 : ℝ)).indicator (Wop hwm hw F : ℝ → ℂ))
        = calK c ((Ioi 1).indicator fun x => ((w x * Φ x : ℝ) : ℂ)) :=
      calK_congr (ae_restrict_of_ae (indicator_congr hWF))
    have hsq : ‖Wop hwm hw (Kop hc (Wop hwm hw F))‖ ^ 2 ≤ (η * ‖F‖) ^ 2 := by
      rw [mul_pow, hF2, norm_sq_eq_integral]
      refine le_of_eq_of_le (integral_congr_ae ?_) hη
      filter_upwards [(memLp_weight hwm hw (Lp.memLp (Kop hc (Wop hwm hw F)))).coeFn_toLp,
        (memLp_calK_one hc (Lp.memLp (Wop hwm hw F))).coeFn_toLp] with y h1 h2
      change ‖((memLp_weight hwm hw (Lp.memLp (Kop hc (Wop hwm hw F)))).toLp _ : ℝ → ℂ) y‖ ^ 2 = _
      rw [h1]
      change ‖(w y : ℂ) * ((memLp_calK_one hc (Lp.memLp (Wop hwm hw F))).toLp _ : ℝ → ℂ) y‖ ^ 2 = _
      rw [h2, hcongr]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hη0 (norm_nonneg _))
      two_ne_zero).1 hsq
  have hJa : -(η * ‖F‖ ^ 2) ≤ RCLike.re (inner ℂ (ext (Wop hwm hw F)) (Uop hc (ext (Wop hwm hw F)))) := by
    rw [← inner_Kop_right, inner_Wop]
    have h1 := RCLike.abs_re_le_norm (inner ℂ F (Wop hwm hw (Kop hc (Wop hwm hw F))))
    have h2 := norm_inner_le_norm (𝕜 := ℂ) F (Wop hwm hw (Kop hc (Wop hwm hw F)))
    have h3 := mul_le_mul_of_nonneg_left hη' (norm_nonneg F)
    have h4 := neg_abs_le (RCLike.re (inner ℂ F (Wop hwm hw (Kop hc (Wop hwm hw F)))))
    nlinarith
  rw [← hae, hF2] at hJa
  have hFn : ‖F‖ = √P := by rw [← hF2, Real.sqrt_sq (norm_nonneg _)]
  have haN : ‖aB + aF‖ ≤ √P := by
    rw [hae, ← hFn]
    have h1 := norm_ext_sq (Wop hwm hw F)
    have h2 := norm_Wop_le hwm hw F
    have h3 : ‖ext (Wop hwm hw F)‖ ^ 2 ≤ ‖F‖ ^ 2 := by
      rw [h1]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
  -- the `e₁` term split into the deep and band defects
  have hre : 2 * RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) e)
      - RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) (aB + aF))
      = RCLike.re (inner ℂ (Uop hc hD + hD) (e + e - (aB + aF)))
        + RCLike.re (inner ℂ (Uop hc hB + hB) (e + e - (aB + aF))) := by
    have hlin : Uop hc (hD + hB) + (hD + hB) = (Uop hc hD + hD) + (Uop hc hB + hB) := by
      rw [map_add]; abel
    rw [hhs, hlin]
    simp only [inner_add_left, inner_add_right, inner_sub_right, map_add, map_sub]
    ring
  have hdG : ((e + e - (aB + aF) : H₀) : ℝ → ℂ) =ᵐ[μ₀]
      fun x => ((2 * dilSum Φ X x - (Ioi 1).indicator (fun x => w x * Φ x) x : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_sub (e + e) (aB + aF), Lp.coeFn_add e e, he, ha] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, h4]
    push_cast; ring
  have hG0 : ∀ x, x ≤ 1 → 2 * dilSum Φ X x - (Ioi 1).indicator (fun x => w x * Φ x) x = 0 := fun x hx => by
    rw [dilSum_of_le_one hx, indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from fun h => not_lt.2 hx h)]; ring
  have hd0 : ∀ᵐ x ∂μ₀, x ≤ 1 → ((e + e - (aB + aF) : H₀) : ℝ → ℂ) x = 0 := by
    filter_upwards [hdG] with x hx hx1
    rw [hx, hG0 x hx1, Complex.ofReal_zero]
  -- deep: `|re⟨e₁^{Sᶜ}, 2E − a⟩| ≤ 2ε√P√N + 3εP`
  have hdeep : |RCLike.re (inner ℂ (Uop hc hD + hD) (e + e - (aB + aF)))|
      ≤ 2 * ε * (√P * √N) + 3 * ε * P := by
    have h1 := abs_re_inner_le_of_ae_zero (f := Uop hc hD + hD) hd0
    have h2 : ∫ y in Ioi 1, ‖((Uop hc hD + hD : H₀) : ℝ → ℂ) y‖ ^ 2 = ∫ y in Ioi 1, ‖eOne c ΦD y‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one)
        (eOne_ae_of_ae hc hDae)] with y hy
      rw [hy]
    have h3 : √(∫ y in Ioi 1, ‖((Uop hc hD + hD : H₀) : ℝ → ℂ) y‖ ^ 2) ≤ ε * √P := by
      rw [h2, ← Real.sqrt_sq hε, ← Real.sqrt_mul' _ hP]
      exact Real.sqrt_le_sqrt hdeepI
    have h4 : ‖e + e - (aB + aF)‖ ≤ 2 * (√N + √P) + √P := by
      have g1 := norm_sub_le (e + e) (aB + aF)
      have g2 := norm_add_le e e
      have g3 := Cvs.L2a.DefectChargeSqrtN.norm_dilSum_le_sqrt hΦr X he
      linarith
    have h5 := mul_le_mul h3 h4 (norm_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _))
    have h6 := Real.mul_self_sqrt hP
    calc |RCLike.re (inner ℂ (Uop hc hD + hD) (e + e - (aB + aF)))|
        ≤ ε * √P * (2 * (√N + √P) + √P) := h1.trans h5
      _ = 2 * ε * (√P * √N) + 3 * ε * (√P * √P) := by ring
      _ = 2 * ε * (√P * √N) + 3 * ε * P := by rw [h6]
  -- band: `re⟨e₁^S, 2E − a⟩ = ∫_{Ioi 1} re(e₁^S)·(2E − wΦ)`
  have hband : RCLike.re (inner ℂ (Uop hc hB + hB) (e + e - (aB + aF)))
      = ∫ x in Ioi 1, (eOne c ΦB x).re * (2 * dilSum Φ X x - w x * Φ x) := by
    rw [re_inner_of_ae_left hdG hG0]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) (eOne_ae_of_ae hc hBae),
      ae_restrict_mem measurableSet_Ioi] with x h1 hx
    rw [h1, indicator_of_mem hx]
  rw [← hband] at hBC
  obtain ⟨hd1, -⟩ := abs_le.1 hdeep
  obtain ⟨hb1, -⟩ := abs_le.1 hBC
  linarith

/-- **The split quadratic floor under (BC)**: `quad_of_corners_split_eOne` with the band hypothesis in
coefficient form, `BandCoupling c g μ a S w X θ`. -/
theorem quad_of_corners_split {St : ℝ → ℝ} (hS : IsStep St) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i ∉ S, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r θ : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hBC : BandCoupling c g μ a S w X θ) :
    (1 / 2 - 3 * ε - η - r - θ) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ (∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2)
        + 2 * ε * (√(∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
          * √(∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2)) :=
  quad_of_corners_split_eOne hS a hg hg₁ hg₂c hang hc hχ heven hμ S hε hτ hwm hw0 hw1 hX hwX hη0 hη hsum
    ((bandCoupling_iff a hg hg₁ hg₂c hang hc heven hμ S hwm hw0 hw1 hX θ).1 hBC)

/-- **The split floor, `P`-form**: under `quad_of_corners_split`'s hypotheses and `A = ½ − 3ε − η − r − θ ≥ 0`,
`(√(A + ε²) − ε)²·∫_{Ioi 1} Φ² ≤ N`. -/
theorem floor_of_corners_split {St : ℝ → ℝ} (hS : IsStep St) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i ∉ S, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r θ : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hBC : BandCoupling c g μ a S w X θ) (hA : 0 ≤ 1 / 2 - 3 * ε - η - r - θ) :
    (√(1 / 2 - 3 * ε - η - r - θ + ε ^ 2) - ε) ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 :=
  Cvs.L2a.ParametricFloorSqrtN.sq_le_of_quadratic (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _) hε hA
    (quad_of_corners_split hS a hg hg₁ hg₂c hang hc hχ heven hμ S hε hτ hwm hw0 hw1 hX hwX hη0 hη hsum hBC)

/-- **The split floor, sum form, any step**: `FrameFloorIntegerM`'s `FF_of_corners_sum_G` with `1 − ε ≤ τᵢ` only off `S` and the
band through (BC): `(√(A + ε²) − ε)²·Σ aᵢ²∫₁^X ψᵢ² ≤ N`, `A = ½ − 3ε − η − r − θ ≥ 0`. -/
theorem FF_of_corners_split_G {St : ℝ → ℝ} (hS : IsStep St) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i ∉ S, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r θ : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hBC : BandCoupling c g μ a S w X θ) (hA : 0 ≤ 1 / 2 - 3 * ε - η - r - θ) :
    (√(1 / 2 - 3 * ε - η - r - θ + ε ^ 2) - ε) ^ 2
        * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 :=
  FF_of_floor a hg hg₁ hg₂c hang hc hχ hX (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
    (floor_of_corners_split hS a hg hg₁ hg₂c hang hc hχ heven hμ S hε hτ hwm hw0 hw1 hX hwX hη0 hη hsum hBC hA)

/-- **The split floor, sum form, quintic partition**: `FF_of_corners_split_G` at `St = S`. -/
theorem FF_of_corners_split_S (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i ∉ S, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r θ : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hBC : BandCoupling c g μ a S w X θ) (hA : 0 ≤ 1 / 2 - 3 * ε - η - r - θ) :
    (√(1 / 2 - 3 * ε - η - r - θ + ε ^ 2) - ε) ^ 2
        * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 :=
  FF_of_corners_split_G isStep_S a hg hg₁ hg₂c hang hc hχ heven hμ S hε hτ hwm hw0 hw1 hX hwX hη0 hη hsum
    hBC hA

end Cvs.L2a.FrameFloorBandCoupling
