import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.CornerKernelUniform
import Cvs.L2a.CornerSplitSqrtFloor
import Cvs.L2a.CornerSuprema
import Cvs.L2a.CutKernelRemainder
import Cvs.L2a.CutKernels
import Cvs.L2a.DefectChargeSqrtN
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarFarConstantClosedForm
import Cvs.L2a.FarFarProfileClosedForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorJumpAbsorption
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.ParametricFloorSqrtN
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.ReflectionFloor
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
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
# JA: the frame floor at every integer `M`

The `√N` floor holds from `−r·P ≤ D_bot + D_mid + D_top` alone. The sum identity `−2Σ∫ū𝔅_m + ΣC_m + 𝒞_a + D₁`, LOC
bottom and top, `|𝒞_a| ≤ (γ_D + γ_E₁)P`, Prop B and the threshold checks give `r ≤ R̄ + ρ + γ + r₁ + r_S`, and
`ε_τ(5)`, `η` close `κ_F(c)·Σ aᵢ²∫₁^M ψᵢ² ≤ N(M)` at every integer `M ≥ 3`, `κ_F = (√(A + ε²) − ε)²`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.DilationCornerSplit Cvs.L2a.CornerSplitSqrtFloor

namespace Cvs.L2a.FrameFloorIntegerM

local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

/-! ### The floor from a lower bound on the sum of the three parts -/

/-- **The `√N` floor in sum form, any step**: `−r·P ≤ D_bot + D_mid + D_top` and `A = ½ − 3ε − η − r ≥ 0` give
`(√(A + ε²) − ε)²·Σ aᵢ²∫₁^X ψᵢ² ≤ N`. -/
theorem FF_of_corners_sum_G {St : ℝ → ℝ} (hS : IsStep St) {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ}
    {c : ℝ} {χ μ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG St c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hA : 0 ≤ 1 / 2 - 3 * ε - η - r) :
    (√(1 / 2 - 3 * ε - η - r + ε ^ 2) - ε) ^ 2
        * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 := by
  have hΦr : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  obtain ⟨u, aB, aF, e, hu, haB, haF, he⟩ := exists_core_arm hX hΦr hwm hw0 hw1
  obtain ⟨hh, -, -, -, -⟩ := core_arm_ae hX hwX hu haB haF he
  have he₁ := Cvs.L2a.DefectChargeSqrtN.eone_charge_sqrtN a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ X hh he
  have hsplit := coreDil_eq_cornerG hS hc hX hwX hΦr δ hu haB haF he
  set P := ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 with hPdef
  set N := ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 with hNdef
  have hP : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hN : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  set r' := r + 2 * ε + 2 * ε * (√N / √P) with hr
  have hrP : r' * P = r * P + 2 * ε * (√P * √N + P) := by
    have hPs : P = √P * √P := (Real.mul_self_sqrt hP).symm
    rcases eq_or_ne (√P) 0 with h0 | h0
    · rw [hr, hPs, h0]; ring
    · rw [hr]
      have : √N / √P * P = √P * √N := by
        calc √N / √P * P = √N / √P * (√P * √P) := by rw [Real.mul_self_sqrt hP]
          _ = √P * √N := by
            rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ h0, mul_comm]
      linear_combination (2 * ε) * this
  obtain ⟨h4, -⟩ := abs_le.1 he₁
  have hAL : -0 * corePos c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X - r' * P
      ≤ coreDil c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X := by
    rw [hsplit, hrP]
    linarith
  have hfl := floor_of_absorption a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ hwm hw0 hw1 hX hwX hη0 hη
    zero_le_one hAL
  have hexp : (1 / 2 - ε - η - r') * P
      = (1 / 2 - 3 * ε - η - r) * P - 2 * ε * (√P * √N) := by
    linear_combination (-1 : ℝ) * hrP
  have hq : (1 / 2 - 3 * ε - η - r) * P ≤ N + 2 * ε * (√P * √N) := by linarith
  exact FF_of_floor a hg hg₁ hg₂c hang hc hχ hX hN
    (Cvs.L2a.ParametricFloorSqrtN.sq_le_of_quadratic hN hP hε hA hq)

/-- **The `√N` floor in sum form for the quintic partition**: `FF_of_corners_sum_G` at `St = S`. -/
theorem FF_of_corners_sum_S {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ}
    {c : ℝ} {χ μ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X < x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    {δ r : ℝ}
    (hsum : -r * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ
        + DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) w X δ)
    (hA : 0 ≤ 1 / 2 - 3 * ε - η - r) :
    (√(1 / 2 - 3 * ε - η - r + ε ^ 2) - ε) ^ 2
        * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X y ^ 2 :=
  FF_of_corners_sum_G isStep_S a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ hwm hw0 hw1 hX hwX hη0 hη hsum hA

/-! ### The bottom and top budgets over the main terms -/

section budget

open Cvs.L2a.LocalisedBottomCorners Cvs.L2a.CornerSuprema

/-- The excess of `Λ_m` over `L_near(m) + L_far(m, M)`: the oscillations, the collars and the `m = 2` shells. -/
def lamX (c δ s m M : ℝ) : ℝ :=
  (if m = 2 then |gT 2 (2 - s)| / (π ^ 2 * c)
      + ∑ k ∈ Finset.range (nSh s), 4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k
    else |gT m 2| / (π ^ 2 * c)
      + 4 * (181 / 462) / π ^ 2 * δ * (3 / 4) * ((m * (1 - δ)) ^ 2 / ((m * (1 - δ)) ^ 2 - 4) ^ 2))
    + gT m M / (π ^ 2 * c) + 4 * (181 / 462) / π ^ 2 * deltaM δ m * collF (bP m (deltaM δ m)) M

/-- `Λ_m = L_near(m) + L_far(m, M) + lamX`. -/
theorem lamT_eq (c δ s m M : ℝ) : lamT c δ s m M = (Lnear m + Lfar m M) + lamX c δ s m M := by
  unfold lamT lamX lam2 lamN lamF
  split_ifs with h
  · subst h; ring
  · ring

/-- `√(a + b) ≤ √a + √b` for `a ≥ 0` and any `b`. -/
theorem sqrt_add_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) : √(a + b) ≤ √a + √b := by
  rcases le_total 0 b with hb | hb
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  · have h1 : √(a + b) ≤ √a := Real.sqrt_le_sqrt (by linarith)
    linarith [Real.sqrt_nonneg b]

/-- **The bottom residual** at `S*`, `X_b = 550`: `ℬ − r_bot,550 − [M > 550]T̄_bot(550)`, term by term. -/
def resB (c J : ℝ) (M : ℕ) : ℝ :=
  π ^ 2 * Cvs.L2a.TopCornerSum.deltaS c ^ 2 * √(∑ m ∈ Finset.Ico 2 (min M 550), (Lnear m + Lfar m M))
    + (1 + π ^ 2 * Cvs.L2a.TopCornerSum.deltaS c ^ 2)
      * √(∑ m ∈ Finset.Ico 2 (min M 550), lamX c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) m M)
    + 2 * ∑ m ∈ Finset.Ico 2 (min M 550),
      (√(eT c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) m M J) + √(kT c (Cvs.L2a.TopCornerSum.sS c) m M J))
    + stripB c (Cvs.L2a.TopCornerSum.sS c) J + (if 550 < M then kFb c / c * Tbar (kapI c J) 550 else 0)

/-- **`ℬ ≤ r_bot,550 + [M > 550]T̄_bot(550) + resB`** at `S*`. -/
theorem calB_le (c J : ℝ) (M : ℕ) :
    calB c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) 550 M J
      ≤ Cvs.L2a.LocalisedConstants.botMain (kapI c J) M + resB c J M := by
  have hLL : 0 ≤ ∑ m ∈ Finset.Ico 2 (min M 550), (Lnear (m : ℝ) + Lfar m M) := by
    refine Finset.sum_nonneg fun m hm => ?_
    obtain ⟨h2, hK⟩ := Finset.mem_Ico.1 hm
    have hmM : m + 1 ≤ M := by have := min_le_left M 550; omega
    exact add_nonneg (Lnear_nonneg (by exact_mod_cast h2))
      (Lfar_nonneg (by exact_mod_cast h2) (by exact_mod_cast hmM))
  have hsplit : ∑ m ∈ Finset.Ico 2 (min M 550), lamT c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) m M
      = ∑ m ∈ Finset.Ico 2 (min M 550), (Lnear (m : ℝ) + Lfar m M)
        + ∑ m ∈ Finset.Ico 2 (min M 550), lamX c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) m M := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => lamT_eq _ _ _ _ _
  have hsq := sqrt_add_le_of_nonneg (b := ∑ m ∈ Finset.Ico 2 (min M 550),
    lamX c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) m M) hLL
  have hd : 0 ≤ 1 + π ^ 2 * Cvs.L2a.TopCornerSum.deltaS c ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hd
  unfold calB Cvs.L2a.LocalisedConstants.botMain resB
  rw [hsplit]
  push_cast
  split_ifs <;> nlinarith

/-- `ρ_t` at `S*` with the top threshold `X_t = 68`. -/
def rhoTL (c J : ℝ) : ℝ :=
  Cvs.L2a.TopCornerSum.rhoT c J (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) (Cvs.L2a.TopCornerSum.uS c) (Cvs.L2a.TopCornerSum.KS c) 68

/-- **The LOC residual** `resB + ρ_t` at `S*`, `X_b = 550`, `X_t = 68`. -/
def resLoc (c J : ℝ) (M : ℕ) : ℝ := resB c J M + rhoTL c J

/-- `r₁` at `X_t = 68` is `LocalisedConstants`'s `r1main`. -/
theorem r1T_eq (c J : ℝ) (M : ℕ) :
    Cvs.L2a.TopCornerSum.r1T c J 68 M = Cvs.L2a.LocalisedConstants.r1main (kapI c J) M := rfl

/-- **LOC's budgets over the main terms**: `ℬ + r₁ + ρ_t ≤ r1main + botMain + resLoc`. -/
theorem loc_le (c J : ℝ) (M : ℕ) :
    calB c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) 550 M J + (Cvs.L2a.TopCornerSum.r1T c J 68 M + rhoTL c J)
      ≤ Cvs.L2a.LocalisedConstants.r1main (kapI c J) M + Cvs.L2a.LocalisedConstants.botMain (kapI c J) M
        + resLoc c J M := by
  have h := calB_le c J M
  rw [r1T_eq]
  unfold resLoc
  linarith

end budget

/-! ### The three parts at an integer `M` -/

section corners

open Cvs.L2a.FarIntegrationByParts Cvs.L2a.CutKernels

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **The three parts at `S*`**: for `c ≥ 4096`, `σᵢ² ≥ 5c` and the `m = 2` shells,
`D_bot + D_mid + D_top ≥ −(r1main + botMain + resLoc + γ_D + γ_E₁ + r₁ + r_S(c, 5c))·P` at every integer `M ≥ 3`. -/
theorem corners_ge_loc (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 4096 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    (hshell : Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) χ g a) :
    -(Cvs.L2a.LocalisedConstants.r1main (Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι)) M
        + Cvs.L2a.LocalisedConstants.botMain (Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι)) M
        + resLoc c (Fintype.card ι) M
        + (Cvs.L2a.CutKernelRemainder.γD c (Fintype.card ι) + Cvs.L2a.CutKernelRemainder.γE1 c (Fintype.card ι))
        + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c (5 * c))
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2
      ≤ DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2) := by
  have hc0 : 0 < c := by linarith
  have hc80 : 80 ≤ c := by linarith
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by nlinarith [hσ i]
  have hδ := Cvs.L2a.TopCornerSum.deltaS_pos hc0
  have hδ8 := Cvs.L2a.TopCornerSum.deltaS_le hc
  have hs := Cvs.L2a.TopCornerSum.sS_pos hc0
  have hs1 := Cvs.L2a.TopCornerSum.sS_le hc
  have hB := Cvs.L2a.LocalisedBottomCorners.Dbot_local a (Xb := 550) hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hmass hM3
    (by norm_num) hδ (by linarith) hδ (by linarith) hs hs1 hshell
  have hT := Cvs.L2a.TopCornerSum.Dtop_flat_rho a (J := (Fintype.card ι : ℝ)) 68 hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hM3 hmass
    le_rfl hδ (by linarith) hδ (by linarith) hs hs1 (Cvs.L2a.TopCornerSum.uS_zero hc) (Cvs.L2a.TopCornerSum.uS_K hc) (Cvs.L2a.TopCornerSum.uS_mono hc0)
  have hC := Cvs.L2a.CornerKernelUniform.calCa_le a hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hM3 hmass
    (J := (Fintype.card ι : ℝ)) le_rfl
  have hmid := Cvs.L2a.MiddlePartQStep.corners_add_mid_ge_closed a hg hg₁ hg₂c hang hc0 hχi hχ0
    (σ₀ := 5 * c) (by positivity) hσ hM3 (δ := 1 / 2) (by norm_num) (by norm_num)
  have hloc := loc_le c (Fintype.card ι) M
  have hP0 : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set J : ℝ := (Fintype.card ι : ℝ) with hJ
  have hbsum : |∑ m ∈ Finset.Icc 2 (M - 1), ∫ t in Ioi 1,
        ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t|
      ≤ ∑ m ∈ Finset.Icc 2 (M - 1), |∫ t in Ioi 1,
        ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbneg := le_abs_self (∑ m ∈ Finset.Icc 2 (M - 1), ∫ t in Ioi 1,
    ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
  have htsum : |∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m| ≤ ∑ m ∈ Finset.Icc 2 (M - 1), |cTop c χ g a M m| :=
    Finset.abs_sum_le_sum_abs _ _
  have htneg := neg_abs_le (∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m)
  have hCa := neg_abs_le (calCa c χ g a M)
  have hrho : rhoTL c J
      = Cvs.L2a.TopCornerSum.rhoT c J (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) (Cvs.L2a.TopCornerSum.uS c) (Cvs.L2a.TopCornerSum.KS c) 68 := rfl
  have hlocP := mul_le_mul_of_nonneg_right hloc hP0
  rw [hrho] at hlocP
  have e1 : -(Cvs.L2a.LocalisedBottomCorners.calB c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) 550 M J * P)
      ≤ -2 * ∑ m ∈ Finset.Icc 2 (M - 1), ∫ t in Ioi 1,
        ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t := by linarith
  have e2 : -((Cvs.L2a.TopCornerSum.r1T c J 68 M
      + Cvs.L2a.TopCornerSum.rhoT c J (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) (Cvs.L2a.TopCornerSum.uS c) (Cvs.L2a.TopCornerSum.KS c) 68) * P)
      ≤ ∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m := by linarith
  have e3 : -((Cvs.L2a.CutKernelRemainder.γD c J + Cvs.L2a.CutKernelRemainder.γE1 c J) * P) ≤ calCa c χ g a M := by linarith
  linarith

end corners

/-! ### The floor at an integer `M` -/

section floor

open Cvs.L2a.FarIntegrationByParts

/-- **The JA margin** `A = ½ − 3ε_τ(5) − √(C_η(c₀)/c) − (R̄ + ρ + γ_D + γ_E₁ + r₁ + r_S(c, 5c))`. -/
def aJA (c₀ c J ρ : ℝ) : ℝ :=
  1 / 2 - 3 * Cvs.L2a.SpanPlungeBound.epsTauFlat 5 - √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ / c)
    - (Cvs.L2a.LocalisedConstants.Rbar + ρ + (Cvs.L2a.CutKernelRemainder.γD c J + Cvs.L2a.CutKernelRemainder.γE1 c J)
      + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c (5 * c))

/-- **The JA floor constant** `κ_F = (√(A + ε²) − ε)²`, `ε = ε_τ(5)`. -/
def kappaF (c₀ c J ρ : ℝ) : ℝ :=
  (√(aJA c₀ c J ρ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2) - Cvs.L2a.SpanPlungeBound.epsTauFlat 5) ^ 2

theorem cEtaClosed_nonneg (c₀ : ℝ) : 0 ≤ Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ := by
  unfold Cvs.L2a.FarFarConstantClosedForm.cEtaClosed Cvs.L2a.FarFarProfileClosedForm.cEtaSym; have := pi_pos; positivity

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-- **JA at one integer `M`**: for `c ≥ 4096`, `1 ≤ c₀ ≤ c`, the `m = 2` shells, `resLoc(c, M) ≤ ρ` and `A ≥ 0`,
`κ_F·Σ aᵢ²∫₁^M ψᵢ² ≤ ∫_{(1,∞)} posTail(Φ, M)²`. -/
theorem JA_floor (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 4096 ≤ c) {c₀ : ℝ} (hc₀ : 1 ≤ c₀) (hcc : c₀ ≤ c)
    (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hshell : Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) χ g a)
    {M : ℕ} (hM3 : 3 ≤ M) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    {ρ : ℝ} (hρ : resLoc c (Fintype.card ι) M ≤ ρ) (hA : 0 ≤ aJA c₀ c (Fintype.card ι) ρ) :
    kappaF c₀ c (Fintype.card ι) ρ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc80 : 80 ≤ c := by linarith
  have hχc : ∀ i, χ i ≤ c ^ 2 := fun i => by have := hσ i; linarith
  have hτ := Cvs.L2a.SpanPlungeBound.epsTau_P2flat hg hg₁ hg₂c hang hc80 (s₀ := 5) (by norm_num) hχ0 hσ heven hg0
    hμ hidx
  have hηb := Cvs.L2a.FarFarConstantClosedForm.farFar_le_closed_of_le a hg hg₁ hg₂c hang hc₀ hcc hχi hχ0 hχc
  have hη : ∫ y in Ioi 1, ‖(wF y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ / c) ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
    rwa [Real.sq_sqrt (div_nonneg (cEtaClosed_nonneg c₀) hc0.le)]
  have hcor := corners_ge_loc a hg hg₁ hg₂c hang hc hχ0 hσ hχi hM3 hmass hshell
  have hκ : Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι) ≤ 1 :=
    (Cvs.L2a.LocalisedConstants.kappaI_mem (by linarith) (Nat.cast_nonneg _) hJ).2
  have hmain := Cvs.L2a.LocalisedConstants.main_le_Rbar hκ hM3
  have hP0 : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hsum : -(Cvs.L2a.LocalisedConstants.Rbar + ρ
        + (Cvs.L2a.CutKernelRemainder.γD c (Fintype.card ι) + Cvs.L2a.CutKernelRemainder.γE1 c (Fintype.card ι))
        + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c (5 * c))
        * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2) := by
    refine le_trans ?_ hcor
    refine mul_le_mul_of_nonneg_right ?_ hP0
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hwX : ∀ x, (M : ℝ) < x → wF x = 1 := fun x hx => by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    exact (wF_of_two_le (by linarith)).1
  have h := FF_of_corners_sum_S a hg hg₁ hg₂c hang hc0 hχi heven hμ
    (Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg 5) hτ continuous_wF.1.measurable
    (fun x => (Cvs.L2a.FarFarBound.wF_bounds x).1) (fun x => (Cvs.L2a.FarFarBound.wF_bounds x).2.1) hM1 hwX
    (Real.sqrt_nonneg _) hη hsum hA
  exact h

end floor

/-! ### The constants at `c₀ = 10¹⁶` -/

section consts

open Cvs.L2a.CutKernelRemainder

theorem A0_le_inv {c : ℝ} (hc : 1 ≤ c) : A0 c (9 / 10) (1 / 4) ≤ 2 / c := by
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℝ, 0 < u ∧ c = u⁻¹ := ⟨c⁻¹, by positivity, by rw [inv_inv]⟩
  have hu1 : u ≤ 1 := by rwa [one_le_inv₀ hu] at hc
  have e : A0 u⁻¹ (9 / 10) (1 / 4) = 10 / 9 * u + 50 / 108 * u ^ 2 + 25 / 81 * u ^ 3 := by
    unfold A0; field_simp; ring
  rw [e, div_inv_eq_mul]
  nlinarith [pow_pos hu 2, pow_pos hu 3]

theorem B0_le_inv {c : ℝ} (hc : 1 ≤ c) : B0 c (9 / 10) 24 ≤ 120 / c := by
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℝ, 0 < u ∧ c = u⁻¹ := ⟨c⁻¹, by positivity, by rw [inv_inv]⟩
  have hu1 : u ≤ 1 := by rwa [one_le_inv₀ hu] at hc
  have e : B0 u⁻¹ (9 / 10) 24 = 200 / 9 * u + 5400 / 81 * u ^ 2 + 2400 / 81 * u ^ 3 := by
    unfold B0; field_simp; ring
  rw [e, div_inv_eq_mul]
  nlinarith [pow_pos hu 2, pow_pos hu 3]

theorem zR_nonneg_all (s : ℝ) : 0 ≤ zR s := tsum_nonneg fun n => by positivity

/-- `γ_D(c, J) ≤ 10⁻⁶` for `c ≥ 10¹⁶`, `0 ≤ J ≤ c`. -/
theorem gammaD_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c) : γD c J ≤ 1 / 10 ^ 6 := by
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc
  have hc0 : 0 < c := by linarith
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 < q ∧ c = q ^ 2 := ⟨√c, Real.sqrt_pos.2 hc0, (Real.sq_sqrt hc0.le).symm⟩
  have hq8 : 10 ^ 8 ≤ q := by nlinarith
  have hk : kap (q ^ 2) ≤ q := by
    rw [kap_sq hq.le]
    have : √(2 / π) ≤ 1 := by
      rw [Real.sqrt_le_one]; rw [div_le_one pi_pos]; linarith [pi_gt_three]
    nlinarith
  have hk0 : 0 ≤ kap (q ^ 2) := Real.sqrt_nonneg _
  have hA := A0_le_inv hc1
  have hB := B0_le_inv hc1
  have hA0 : 0 ≤ A0 (q ^ 2) (9 / 10) (1 / 4) := by unfold A0; positivity
  have hB0 : 0 ≤ B0 (q ^ 2) (9 / 10) 24 := by unfold B0; positivity
  have hz2 : zR 2 ≤ 2 := by have := zR_le (s := 2) (by norm_num); norm_num at this; linarith
  have hz3 : zR 3 ≤ 3 / 2 := by have := zR_le (s := 3) (by norm_num); norm_num at this; linarith
  have hz2' := zR_nonneg_all 2
  have hz3' := zR_nonneg_all 3
  have hl3 : 1 + Real.log 3 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  unfold γD
  calc 6 * J * kap (q ^ 2) * A0 (q ^ 2) (9 / 10) (1 / 4) ^ 2 * zR 2
        + 3 * (1 + Real.log 3) * J * kap (q ^ 2) / (16 * (q ^ 2) ^ 2)
        + 60 * J * kap (q ^ 2) * B0 (q ^ 2) (9 / 10) 24 * zR 3 / (9 * (9 / 10) * (q ^ 2) ^ 2)
      ≤ 6 * q ^ 2 * q * (2 / q ^ 2) ^ 2 * 2 + 3 * 3 * q ^ 2 * q / (16 * (q ^ 2) ^ 2)
        + 60 * q ^ 2 * q * (120 / q ^ 2) * (3 / 2) / (9 * (9 / 10) * (q ^ 2) ^ 2) := by
        gcongr
    _ = (48 + 9 / 16) / q + 10800 / (81 / 10) / q ^ 3 := by field_simp; ring
    _ ≤ 1 / 10 ^ 6 := by
        have h1 : 1 / q ≤ 1 / 10 ^ 8 := one_div_le_one_div_of_le (by positivity) hq8
        have h3 : 1 / q ^ 3 ≤ 1 / (10 ^ 8) ^ 3 := one_div_le_one_div_of_le (by positivity) (by gcongr)
        rw [div_eq_mul_one_div _ q, div_eq_mul_one_div _ (q ^ 3)]
        nlinarith

/-- `γ_E₁(c, J) ≤ 10⁻⁶` for `c ≥ 10¹⁶`, `J ≤ c`. -/
theorem gammaE1_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ : J ≤ c) : γE1 c J ≤ 1 / 10 ^ 6 := by
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc
  have hc0 : 0 < c := by linarith
  have hk : kap c ≤ √c := Real.sqrt_le_sqrt (by
    rw [div_le_iff₀ pi_pos]; nlinarith [pi_gt_three])
  have hk0 : 0 ≤ kap c := Real.sqrt_nonneg _
  have hJ6 : √(6 * J) ≤ 3 * √c := by
    rw [show 3 * √c = √(9 * c) by rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h8 : 2 ≤ √8 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h3 : 1 ≤ √3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h5 : 1 ≤ √5 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : 1 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hA := A0_le_inv hc1
  have hB := B0_le_inv hc1
  have hA0 : 0 ≤ A0 c (9 / 10) (1 / 4) := by unfold A0; positivity
  have hB0 : 0 ≤ B0 c (9 / 10) 24 := by unfold B0; positivity
  have hz52 : zR (5 / 2) ≤ 5 / 3 := by have := zR_le (s := 5 / 2) (by norm_num); norm_num at this; linarith
  have hz72 : zR (7 / 2) ≤ 7 / 5 := by have := zR_le (s := 7 / 2) (by norm_num); norm_num at this; linarith
  have hz32 : zR (3 / 2) ≤ 3 := by have := zR_le (s := 3 / 2) (by norm_num); norm_num at this; linarith
  have hz52' := zR_nonneg_all (5 / 2)
  have hz72' := zR_nonneg_all (7 / 2)
  have hz32' := zR_nonneg_all (3 / 2)
  have hl3 : 1 + Real.log 3 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hl3' : 0 ≤ 1 + Real.log 3 := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  have hc38 : 1 + 3 / (8 * c) ≤ 2 := by
    have : 3 / (8 * c) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hc12 : 1 + 1 / (2 * c) ≤ 2 := by
    have : 1 / (2 * c) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  unfold γE1
  calc _ ≤ 2 * √c * (3 * (3 * √c) / 2)
        * (10 / 9 * (8 * 2 * (120 / c) / (1 * (9 / 10) * c)) * (5 / 3)
          + 10 / 9 * (16 * (120 / c) / (1 * (9 / 10) ^ 2 * c ^ 2)) * (7 / 5)
          + (10 / 9) ^ 2 * (9 * 2 * 2 / (2 * c))
            * ((2 / c) * 3 / 3 + 1 / (4 * c) / 1 * (3 / 3))
          + (10 / 9) ^ 2 * (9 / (8 * c ^ 2))
            * ((2 / c) * 3 / 6 + 1 / (4 * c) / 1 / (2 * 1) * (3 / 3))
          + (10 / 9) ^ 2 * (9 * 2 * (120 / c) / (1 * (9 / 10) * c ^ 2)) * (5 / 3) / 3
          + (10 / 9) ^ 3 * (81 * 2 ^ 2 / (16 * c ^ 2))
            * ((2 / c) * 3 / 6 + 1 / (4 * c) / 1 / (2 * 1) * (3 / 3))) := by
        gcongr
    _ ≤ 1 / 10 ^ 6 := by
        rw [show 2 * √c * (3 * (3 * √c) / 2) = 9 * (√c * √c) by ring, Real.mul_self_sqrt hc0.le]
        obtain ⟨u, hu, rfl⟩ : ∃ u : ℝ, 0 < u ∧ c = u⁻¹ := ⟨c⁻¹, by positivity, by rw [inv_inv]⟩
        have hu1 : u ≤ 1 / 10 ^ 16 := by
          rw [le_inv_comm₀ (by positivity) hu] at hc; rwa [one_div]
        have e : 9 * u⁻¹ * (10 / 9 * (8 * 2 * (120 / u⁻¹) / (1 * (9 / 10) * u⁻¹)) * (5 / 3)
          + 10 / 9 * (16 * (120 / u⁻¹) / (1 * (9 / 10) ^ 2 * u⁻¹ ^ 2)) * (7 / 5)
          + (10 / 9) ^ 2 * (9 * 2 * 2 / (2 * u⁻¹))
            * ((2 / u⁻¹) * 3 / 3 + 1 / (4 * u⁻¹) / 1 * (3 / 3))
          + (10 / 9) ^ 2 * (9 / (8 * u⁻¹ ^ 2))
            * ((2 / u⁻¹) * 3 / 6 + 1 / (4 * u⁻¹) / 1 / (2 * 1) * (3 / 3))
          + (10 / 9) ^ 2 * (9 * 2 * (120 / u⁻¹) / (1 * (9 / 10) * u⁻¹ ^ 2)) * (5 / 3) / 3
          + (10 / 9) ^ 3 * (81 * 2 ^ 2 / (16 * u⁻¹ ^ 2))
            * ((2 / u⁻¹) * 3 / 6 + 1 / (4 * u⁻¹) / 1 / (2 * 1) * (3 / 3)))
            = 9 * (324050 / 81 * u + 257575 / 48 * u ^ 2) := by
          field_simp; ring
        rw [e]
        nlinarith [pow_pos hu 2]

/-- **`A(c) > 0`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1` and `ρ ≤ 13/100`. -/
theorem aJA_pos {c J ρ : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hρ : ρ ≤ 13 / 100) :
    0 < aJA (10 ^ 16) c J ρ := by
  have hJc : J ≤ c := by linarith
  have h1 := Cvs.L2a.SpanPlungeBound.epsTauFlat_five_le
  have h2 := Cvs.L2a.LocalisedConstants.eta_le_c0 hc
  have h3 := Cvs.L2a.LocalisedConstants.rOne_le_c0 hc
  have h4 := Cvs.L2a.LocalisedConstants.rStrip_le_c0 hc
  have h5 := Cvs.L2a.LocalisedConstants.Rbar_le
  have h6 := gammaD_le hc hJ0 hJc
  have h7 := gammaE1_le hc hJc
  unfold aJA
  norm_num at h2 h3 h6 h7 ⊢
  linarith

/-- `A > 0` gives `κ_F = (√(A + ε²) − ε)² > 0`. -/
theorem kappaF_pos {c₀ c J ρ : ℝ} (hA : 0 < aJA c₀ c J ρ) : 0 < kappaF c₀ c J ρ := by
  unfold kappaF
  have hε := Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg 5
  have hlt : Cvs.L2a.SpanPlungeBound.epsTauFlat 5 < √(aJA c₀ c J ρ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2) := by
    rw [Real.lt_sqrt hε]; linarith
  exact pow_pos (by linarith) 2

end consts

/-! ### JA at every integer `M` -/

section ja

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-- **THEOREM JA**: for `c ≥ 10¹⁶`, `σᵢ² ≥ 5c`, `J ≤ c/4 + 1`, the `m = 2` shells and `resLoc(c, M) ≤ ρ ≤ 13/100`
at every `M ≥ 3`, `κ_F(c) > 0` and `κ_F(c)·Σ aᵢ²∫₁^M ψᵢ² ≤ N(M)` at every integer `M ≥ 3`. -/
theorem JA_integer_floor (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hshell : Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) χ g a)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → resLoc c (Fintype.card ι) M ≤ ρ) (hρ1 : ρ ≤ 13 / 100) :
    0 < kappaF (10 ^ 16) c (Fintype.card ι) ρ
      ∧ ∀ M : ℕ, 3 ≤ M → (∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) →
        kappaF (10 ^ 16) c (Fintype.card ι) ρ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
          ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2 := by
  have hA := aJA_pos (ρ := ρ) hc (Nat.cast_nonneg _) hJ hρ1
  refine ⟨kappaF_pos hA, fun M hM3 hmass => ?_⟩
  exact JA_floor a hg hg₁ hg₂c hang (le_trans (by norm_num) hc) (by norm_num) hc hχ0 hσ hχi heven hg0 hμ hidx hJ
    hshell hM3 hmass (hρ M hM3) hA.le

end ja

end Cvs.L2a.FrameFloorIntegerM
