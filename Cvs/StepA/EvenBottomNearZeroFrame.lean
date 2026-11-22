import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.TopQuadruple
import Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.ZeroLorentzianSums
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even bottom against the zeros off the line, by a frame bound on the near zeros

If every zero off the line has `|Re ρ − 1/2| ≤ d`, then for `L > 0`, every `N` and `H = max(4πN/L, 1)`,
`evLam ≥ −(8448 (L + 2) e^{d(L+2)} log(3H + 5) + 8448 (1/(2π) + 1/L) cosh²(dL/2) (log(H + 5) + 1))`: the zeros
with `|γ| < H` through the frame bound (Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound) and the local count (Cvs.Zeta.ZeroCounting.ZeroLorentzianSums), the rest through the far envelope.
-/

noncomputable section

open Real Matrix
open scoped ComplexConjugate

namespace Cvs.StepA.EvenBottomNearZeroFrame
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.StepA.OneZeroParitySectors (ctr)
open Cvs.StepA.TopQuadruple (offLine pairE)
open Cvs.StepA.ModePolynomialFarEnvelope (envE)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.TopSetCriterion (bandBotE bandRayE restE)
open Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound (frameKernel)

/-! ### One zero's even pairing against the centred transform -/

/-- The centred cosine polynomial of `ξ` is continuous. -/
theorem continuous_cosPoly_centred (L : ℝ) (N : ℕ) (ξ : Idx N → ℝ) :
    Continuous fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) := by
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly; fun_prop

/-- **The even pairing is at least minus the squared transform**: for `L ≠ 0`,
`−‖ctr L g z‖² ≤ pairE L N ξ z` with `g = cosPoly_ξ(· + L/2)`. -/
theorem neg_norm_ctr_sq_le_pairE {L : ℝ} (hL : L ≠ 0) (N : ℕ) (ξ : Idx N → ℝ) (z : ℂ) :
    -‖ctr L (fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2)) z‖ ^ 2
      ≤ pairE L N ξ z := by
  have h := (Cvs.StepA.OneZeroParitySectors.ctr_of_even L
    ((continuous_cosPoly_centred L N ξ).intervalIntegrable _ _)
    (fun t => Cvs.StepA.OneZeroParitySectors.cosPoly_centred_neg hL (mode N) ξ t) z).1
  rw [h, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_im, Complex.mul_im, zero_mul, one_mul, sub_zero, zero_sub, mul_zero,
    zero_add, sub_self]
  unfold pairE
  nlinarith [sq_nonneg (∫ t in -(L / 2)..L / 2,
    Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) * Cvs.StepA.OneZeroParitySectors.ue z t)]

/-! ### The kernel between two zeros -/

/-- **The kernel between two zeros within `d` of the line**: for `L ≥ 0`,
`‖K_L(z_ρ − z̄_σ)‖ ≤ 4(L + 2) e^{d(L+2)}/(1 + (γ_ρ − γ_σ)²)`. -/
theorem norm_frameKernel_zPoint_le {L : ℝ} (hL : 0 ≤ L) {d : ℝ} {ρ σ : nonTrivialZeroSet}
    (hρ : |Cvs.GaussKernel.del ρ| ≤ d) (hσ : |Cvs.GaussKernel.del σ| ≤ d) :
    ‖frameKernel L (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ))‖
      ≤ 4 * (L + 2) * Real.exp (d * (L + 2)) * (1 / (1 + ((ρ : ℂ).im - (σ : ℂ).im) ^ 2)) := by
  have h := Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound.norm_frameKernel_le hL
    (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ))
  have hre : (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ)).re
      = (ρ : ℂ).im - (σ : ℂ).im := by
    rw [Complex.sub_re, Complex.conj_re, Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_re]
  have him : (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ)).im
      = -Cvs.GaussKernel.del ρ - Cvs.GaussKernel.del σ := by
    rw [Complex.sub_im, Complex.conj_im, Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del,
      Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del]; ring
  rw [hre, him, div_eq_mul_one_div] at h
  refine h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)) (by positivity))
  have : |-Cvs.GaussKernel.del ρ - Cvs.GaussKernel.del σ| ≤ 2 * d := by
    calc _ ≤ |Cvs.GaussKernel.del ρ| + |Cvs.GaussKernel.del σ| := by
          rw [show -Cvs.GaussKernel.del ρ - Cvs.GaussKernel.del σ
            = -Cvs.GaussKernel.del ρ + -Cvs.GaussKernel.del σ by ring]
          exact (abs_add_le _ _).trans (by rw [abs_neg, abs_neg])
      _ ≤ 2 * d := by linarith
  nlinarith

/-! ### The near zeros -/

/-- **The near zeros through the frame bound**: for `L > 0`, a finite set `F` of zeros with `|γ| ≤ H` and
`|Re ρ − 1/2| ≤ d`, and every `ξ`,
`Σ_F m_ρ pairE(L, N, ξ, z_ρ) ≥ −8448 (L + 2) e^{d(L+2)} log(3H + 5) · L‖ξ‖²`. -/
theorem sum_mult_pairE_ge {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : Idx N → ℝ) (F : Finset nonTrivialZeroSet)
    {H : ℝ} (hH0 : 0 ≤ H) (hH : ∀ ρ ∈ F, |(ρ : ℂ).im| ≤ H) {d : ℝ}
    (hd : ∀ ρ ∈ F, |Cvs.GaussKernel.del ρ| ≤ d) :
    -(8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * H + 5) * (L * (ξ ⬝ᵥ ξ)))
      ≤ ∑ ρ ∈ F, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  set g := fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) with hg
  set Λ := 8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * H + 5) with hΛ
  have hlog : 0 ≤ Real.log (3 * H + 5) := Real.log_nonneg (by linarith)
  have hΛ0 : 0 ≤ Λ := by positivity
  have hrow : ∀ j ∈ F, ∑ k ∈ F, mult k
      * ‖frameKernel L (Cvs.ZeroCounting.zPoint j - conj (Cvs.ZeroCounting.zPoint k))‖ ≤ Λ := by
    intro j hj
    have hc := Cvs.Zeta.ZeroCounting.ZeroLorentzianSums.sum_mult_inv_one_add_sq_le F hH0 hH (j : ℂ).im
    have hl : Real.log (2 * |(j : ℂ).im| + H + 5) ≤ Real.log (3 * H + 5) :=
      Real.log_le_log (by positivity) (by linarith [hH j hj])
    calc ∑ k ∈ F, mult k
          * ‖frameKernel L (Cvs.ZeroCounting.zPoint j - conj (Cvs.ZeroCounting.zPoint k))‖
        ≤ ∑ k ∈ F, mult k * (4 * (L + 2) * Real.exp (d * (L + 2))
            * (1 / (1 + ((j : ℂ).im - (k : ℂ).im) ^ 2))) :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
            (norm_frameKernel_zPoint_le hL.le (hd j hj) (hd k hk)) (mult_nonneg k)
      _ = 4 * (L + 2) * Real.exp (d * (L + 2))
            * ∑ k ∈ F, mult k * (1 / (1 + ((j : ℂ).im - (k : ℂ).im) ^ 2)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ 4 * (L + 2) * Real.exp (d * (L + 2)) * (2112 * Real.log (3 * H + 5)) :=
          mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hl (by norm_num)))
            (by positivity)
      _ = Λ := by rw [hΛ]; ring
  have hframe := Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound.sum_mul_norm_ctr_sq_le F (fun ρ _ => mult_nonneg ρ)
    Cvs.ZeroCounting.zPoint hL.le (continuous_cosPoly_centred L N ξ) hΛ0 hrow
  have hE := Cvs.StepA.ModePolynomialFarEnvelope.integral_cosPoly_centred_sq_le hL
    (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) ξ
  have hpt : ∀ ρ ∈ F, -(mult ρ * ‖ctr L g (Cvs.ZeroCounting.zPoint ρ)‖ ^ 2)
      ≤ mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := fun ρ _ => by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_norm_ctr_sq_le_pairE hL.ne' N ξ _) (mult_nonneg ρ)
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_neg_distrib] at hsum
  have := mul_le_mul_of_nonneg_left hE hΛ0
  linarith

/-- **The even band bottom of a finite set of near zeros**: for `L > 0` and a finite set `F` of zeros with
`|γ| ≤ H` and `|Re ρ − 1/2| ≤ d`, `bandBotE L N F ≥ −8448 (L + 2) e^{d(L+2)} log(3H + 5)`. -/
theorem neg_le_bandBotE {L : ℝ} (hL : 0 < L) (N : ℕ) (F : Finset nonTrivialZeroSet) {H : ℝ}
    (hH0 : 0 ≤ H) (hH : ∀ ρ ∈ F, |(ρ : ℂ).im| ≤ H) {d : ℝ}
    (hd : ∀ ρ ∈ F, |Cvs.GaussKernel.del ρ| ≤ d) :
    -(8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * H + 5))
      ≤ bandBotE L N (F : Set nonTrivialZeroSet) := by
  refine le_csInf (Cvs.StepA.Edge.TopSetCriterion.bandRayE_nonempty hL N _) ?_
  rintro r ⟨ξ, -, hne, rfl⟩
  rw [le_div_iff₀ (Cvs.StepA.Edge.TopSetCriterion.mul_dot_pos hL hne), Finset.tsum_subtype' F
    (fun ρ => mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ))]
  have := sum_mult_pairE_ge hL N ξ F hH0 hH hd
  linarith

/-! ### The split height and the far zeros -/

/-- The split height `max(4πN/L, 1)`: at or above it every zero is in the far branch of `envE`. -/
def frameHeight (L : ℝ) (N : ℕ) : ℝ := max (2 * (2 * π * N / L)) 1

/-- The zeros off the line with `|γ| < H`. -/
def nearZeros (H : ℝ) : Set nonTrivialZeroSet := {ρ | ρ ∈ offLine ∧ |(ρ : ℂ).im| < H}

/-- The near zeros form a finite set. -/
theorem nearZeros_finite (H : ℝ) : (nearZeros H).Finite :=
  (Cvs.GaussKernel.finite_window H).subset fun _ hρ => hρ.2.le

/-- `cosh²(Im z_ρ · L/2) ≤ cosh²(dL/2)` for `|Re ρ − 1/2| ≤ d`. -/
theorem cosh_sq_zPoint_le_of_del {L : ℝ} (hL : 0 ≤ L) {d : ℝ} {ρ : nonTrivialZeroSet}
    (hρ : |Cvs.GaussKernel.del ρ| ≤ d) :
    cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2 ≤ cosh (d * L / 2) ^ 2 := by
  refine pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_cosh.2 ?_) 2
  rw [Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del, show -Cvs.GaussKernel.del ρ * L / 2
    = -Cvs.GaussKernel.del ρ * (L / 2) by ring, show d * L / 2 = d * (L / 2) by ring, abs_mul, abs_mul,
    abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L / 2),
    abs_of_nonneg ((abs_nonneg _).trans hρ)]
  exact mul_le_mul_of_nonneg_right hρ (by linarith)

/-- **The far zeros**: for `L > 0`, `H ≥ max(4πN/L, 1)` and every zero off the line within `d` of it,
`restE L N (nearZeros H) ≤ 16(2N+1)cosh²(dL/2)/L · 528 (log(H + 5) + 1)/H`. -/
theorem restE_nearZeros_le {L : ℝ} (hL : 0 < L) (N : ℕ) {H : ℝ} (hH1 : 1 ≤ H)
    (hHN : 2 * (2 * π * N / L) ≤ H) {d : ℝ}
    (hd : ∀ ρ ∈ offLine, |Cvs.GaussKernel.del ρ| ≤ d) :
    restE L N (nearZeros H)
      ≤ 16 * (2 * N + 1) * cosh (d * L / 2) ^ 2 / L * (528 * ((Real.log (H + 5) + 1) / H)) := by
  set C := 16 * (2 * N + 1) * cosh (d * L / 2) ^ 2 / L with hC
  have hfar : ∀ ρ ∈ offLine \ nearZeros H, H ≤ |(ρ : ℂ).im| := fun ρ hρ => by
    by_contra h
    exact hρ.2 ⟨hρ.1, not_le.1 h⟩
  have hpt : ∀ ρ : ↥(offLine \ nearZeros H),
      mult ρ * envE L N (Cvs.ZeroCounting.zPoint ρ)
        ≤ C * (mult ρ * (1 / (((ρ : nonTrivialZeroSet) : ℂ).im) ^ 2)) := by
    rintro ⟨ρ, hρ⟩
    have hre : (Cvs.ZeroCounting.zPoint ρ).re = (ρ : ℂ).im := Cvs.ZeroCounting.zPoint_re ρ
    have hb : 2 * (2 * π * N / L) ≤ |(Cvs.ZeroCounting.zPoint ρ).re| := by
      rw [hre]; exact hHN.trans (hfar ρ hρ)
    have hc := cosh_sq_zPoint_le_of_del hL.le (hd ρ hρ.1)
    rw [envE, if_pos hb, hre]
    have e1 : 16 * (2 * (N : ℝ) + 1) * cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2
        / (L * (ρ : ℂ).im ^ 2)
        = 16 * (2 * N + 1) / L * cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2
          * (1 / (ρ : ℂ).im ^ 2) := by ring
    have e2 : C * (mult ρ * (1 / (ρ : ℂ).im ^ 2))
        = mult ρ * (16 * (2 * N + 1) / L * cosh (d * L / 2) ^ 2 * (1 / (ρ : ℂ).im ^ 2)) := by
      rw [hC]; ring
    simp only
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (mult_nonneg ρ)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity)
  have hs1 : Summable fun ρ : ↥(offLine \ nearZeros H) =>
      mult ρ * envE L N (Cvs.ZeroCounting.zPoint ρ) :=
    (Cvs.StepA.ModePolynomialFarEnvelope.summable_envE hL N).subtype _
  have hs2 : Summable fun ρ : ↥(offLine \ nearZeros H) =>
      C * (mult ρ * (1 / (((ρ : nonTrivialZeroSet) : ℂ).im) ^ 2)) :=
    ((Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq.subtype _).mul_left C)
  calc restE L N (nearZeros H)
      ≤ ∑' ρ : ↥(offLine \ nearZeros H), C * (mult ρ * (1 / (((ρ : nonTrivialZeroSet) : ℂ).im) ^ 2)) :=
        Summable.tsum_le_tsum hpt hs1 hs2
    _ = C * ∑' ρ : ↥(offLine \ nearZeros H), mult ρ * (1 / (((ρ : nonTrivialZeroSet) : ℂ).im) ^ 2) :=
        tsum_mul_left
    _ ≤ C * (528 * ((Real.log (H + 5) + 1) / H)) :=
        mul_le_mul_of_nonneg_left (Cvs.Zeta.ZeroCounting.ZeroLorentzianSums.tsum_mult_inv_sq_le_of_ge _ hH1 hfar)
          (by rw [hC]; positivity)

/-! ### The even bottom at one scale -/

/-- **The even bottom against the zeros off the line, at one scale**: if every zero off the line has
`|Re ρ − 1/2| ≤ d`, then for `L > 0`, every `N` and `H = max(4πN/L, 1)`,
`evLam ≥ −(8448 (L + 2) e^{d(L+2)} log(3H + 5) + 8448 (1/(2π) + 1/L) cosh²(dL/2) (log(H + 5) + 1))`. -/
theorem evLam_ge_neg_frame {L : ℝ} (hL : 0 < L) (N : ℕ) {d : ℝ}
    (hd : ∀ ρ ∈ offLine, |Cvs.GaussKernel.del ρ| ≤ d) :
    -(8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * frameHeight L N + 5)
        + 8448 * (1 / (2 * π) + 1 / L) * cosh (d * L / 2) ^ 2
          * (Real.log (frameHeight L N + 5) + 1))
      ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  set H := frameHeight L N with hHdef
  have hH1 : 1 ≤ H := le_max_right _ _
  have hHN : 2 * (2 * π * N / L) ≤ H := le_max_left _ _
  have hfin := nearZeros_finite H
  have hband := Cvs.StepA.Edge.TopSetCriterion.evLam_ge_band hL N (S := nearZeros H) fun _ hρ => hρ.1
  have hbot : -(8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * H + 5))
      ≤ bandBotE L N (nearZeros H) := by
    rw [← hfin.coe_toFinset]
    exact neg_le_bandBotE hL N hfin.toFinset (by linarith)
      (fun ρ hρ => ((hfin.mem_toFinset).1 hρ).2.le) (fun ρ hρ => hd ρ ((hfin.mem_toFinset).1 hρ).1)
  have hrest := restE_nearZeros_le hL N hH1 hHN hd
  have hlog : 0 ≤ Real.log (H + 5) + 1 := by
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ H + 5)]
  have hratio : (2 * (N : ℝ) + 1) / (L * H) ≤ 1 / (2 * π) + 1 / L := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * (N : ℝ) * (2 * π) ≤ L * H := by
      have := mul_le_mul_of_nonneg_left hHN hL.le
      rw [show L * (2 * (2 * π * N / L)) = 2 * N * (2 * π) by field_simp] at this
      exact this
    have e : (1 / (2 * π) + 1 / L) * (L * H) = L * H / (2 * π) + H := by field_simp
    rw [e]
    have : 2 * (N : ℝ) ≤ L * H / (2 * π) := by rw [le_div_iff₀ (by positivity)]; exact h1
    linarith
  have hfar : 16 * (2 * N + 1) * cosh (d * L / 2) ^ 2 / L * (528 * ((Real.log (H + 5) + 1) / H))
      ≤ 8448 * (1 / (2 * π) + 1 / L) * cosh (d * L / 2) ^ 2 * (Real.log (H + 5) + 1) := by
    have e : 16 * (2 * N + 1) * cosh (d * L / 2) ^ 2 / L * (528 * ((Real.log (H + 5) + 1) / H))
        = 8448 * ((2 * N + 1) / (L * H)) * cosh (d * L / 2) ^ 2 * (Real.log (H + 5) + 1) := by
      field_simp; ring
    rw [e]
    gcongr
  linarith

end Cvs.StepA.EvenBottomNearZeroFrame
