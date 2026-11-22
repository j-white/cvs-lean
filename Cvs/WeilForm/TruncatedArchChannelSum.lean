import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated archimedean form is the channel sum, at the `L²` level

For any window class, the archimedean-plus-Lévy part of the truncated Weil form equals
`truncConst N · ‖·‖² − ∑_{k<N} chanInt (bIdx k)`, proved by self-convolution algebra with no
continuity assumed, so it holds for every `L²` class.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.TruncatedArchChannelSum

variable {L : ℝ}

/-- **The scaled exponential integrates to `1/b`** on the half-line. -/
theorem integral_exp_neg_scaled {b : ℝ} (hb : 0 < b) :
    ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) = 1 / b := by
  have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hb
  rw [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one] at h
  rw [one_div]
  exact h

/-- **`bIdx k` is positive.** -/
theorem bIdx_pos (k : ℕ) : 0 < Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k := by
  unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx
  positivity

/-- **The per-channel Lévy integral is the channel weight minus half `chanInt`.** -/
theorem channel_integral (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (k : ℕ) :
    ∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v))
        * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
          - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v)
      = (1 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
        - (1 / 2) * Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
            (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  set g := Cvs.WeilForm.WindowRepresentative.rep φ with hg
  set S0 := selfConvolution g 0 with hS0
  have hb := bIdx_pos k
  -- split the integrand into two integrable pieces
  have hi1 : IntegrableOn (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0)
      (Ioi (0:ℝ)) := by
    have hrw : (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0)
        = fun v => S0 * Real.exp ((-Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * v) := by
      funext v; rw [neg_mul]; ring
    rw [hrw]
    exact (integrableOn_exp_mul_Ioi (by linarith [hb] : (-Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) < 0) 0).const_mul S0
  have hi2 : IntegrableOn (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v))
      * selfConvolution g v) (Ioi (0:ℝ)) :=
    Cvs.WeilForm.ChannelFunctionalL2.integrable_exp_self φ hb
  -- rewrite the difference and split the integral
  have hsplit : ∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * (S0 - selfConvolution g v)
      = (∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0)
        - ∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * selfConvolution g v := by
    rw [← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    ring
  rw [hsplit]
  -- first integral: (1/bIdx k) S0
  have hfirst : ∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0
      = (1 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * S0 := by
    rw [integral_mul_const, integral_exp_neg_scaled hb]
  -- second integral: chanInt / 2
  have hsecond : ∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * selfConvolution g v
      = (1 / 2) * Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g := by
    unfold Cvs.WeilForm.ChannelFunctionalL2.chanInt
    ring
  rw [hfirst, hsecond]

/-- **Each channel term is integrable** on the half-line. -/
theorem channel_term_integrable (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (k : ℕ) :
    IntegrableOn (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v))
        * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
          - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v)) (Ioi (0:ℝ)) := by
  set g := Cvs.WeilForm.WindowRepresentative.rep φ with hg
  set S0 := selfConvolution g 0 with hS0
  have hb := bIdx_pos k
  have hi1 : IntegrableOn (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0)
      (Ioi (0:ℝ)) := by
    have hrw : (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0)
        = fun v => S0 * Real.exp ((-Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * v) := by
      funext v; rw [neg_mul]; ring
    rw [hrw]
    exact (integrableOn_exp_mul_Ioi (by linarith [hb] : (-Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) < 0) 0).const_mul S0
  have hi2 : IntegrableOn (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v))
      * selfConvolution g v) (Ioi (0:ℝ)) :=
    Cvs.WeilForm.ChannelFunctionalL2.integrable_exp_self φ hb
  have heq : (fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * (S0 - selfConvolution g v))
      = fun v => Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * S0
        - Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) * selfConvolution g v := by
    funext v; ring
  rw [heq]
  exact hi1.sub hi2

/-- **The truncated archimedean form is the channel sum**, at the `L²` level. -/
theorem archLevy_eq_channelSum (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (N : ℕ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
      + ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
          * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
            - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) (u / 2))
    = Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
      - ∑ k ∈ Finset.range N, Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
          (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  set g := Cvs.WeilForm.WindowRepresentative.rep φ with hg
  set S0 := selfConvolution g 0 with hS0
  -- substitute u = 2 v in the Lévy integral
  have hsub : (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u * (S0 - selfConvolution g (u / 2)))
      = 2 * ∫ v in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N (2 * v) * (S0 - selfConvolution g v) := by
    have h := integral_comp_mul_left_Ioi'
      (fun u => Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u * (S0 - selfConvolution g (u / 2))) 0
      (show (0:ℝ) < 2 by norm_num)
    rw [mul_zero, smul_eq_mul] at h
    rw [← h]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [show (2 * v) / 2 = v by ring]
  rw [hsub]
  -- densityTrunc N (2v) is the finite sum of channel exponentials
  have hdt : ∀ v : ℝ, Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N (2 * v)
      = ∑ k ∈ Finset.range N, Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v)) := by
    intro v
    unfold Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx_eq]; ring
  -- swap the finite sum with the integral
  have hswap : (∫ v in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N (2 * v) * (S0 - selfConvolution g v))
      = ∑ k ∈ Finset.range N, ∫ v in Ioi (0:ℝ), Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v))
          * (S0 - selfConvolution g v) := by
    have hfun : (fun v => Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N (2 * v) * (S0 - selfConvolution g v))
        = fun v => ∑ k ∈ Finset.range N, Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * v))
            * (S0 - selfConvolution g v) := by
      funext v; rw [hdt v, Finset.sum_mul]
    rw [hfun, integral_finsetSum]
    intro k _; exact channel_term_integrable φ k
  rw [hswap, Finset.sum_congr rfl (fun k _ => channel_integral φ k)]
  -- collapse the constants
  have hterm : ∀ k : ℕ, 2 * ((1 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * S0
      - (1 / 2) * Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g)
      = (1 / ((k : ℝ) + 1 / 4)) * S0 - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g := by
    intro k
    have hk : (1 / 4 + (k : ℝ)) ≠ 0 := by positivity
    rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx_eq]
    field_simp
    ring
  have hfin : 2 * (∑ k ∈ Finset.range N, ((1 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * S0
        - (1 / 2) * Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g))
      = (∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1 / 4))) * S0
        - ∑ k ∈ Finset.range N, Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib,
      Finset.sum_mul]
  rw [hfin, Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst]
  ring

end Cvs.WeilForm.TruncatedArchChannelSum
