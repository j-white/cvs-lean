import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailPrimeChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.LevyUnitBlocks
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The polarisation of `W_∞`

`fullTail`, `posTail`, `tailInt` and `piPlus` are linear on cosine transforms; `WinfBil` is the channel-wise
polarisation of `FullTailWeilFormLimit`'s `Winf`, with `Winf (Φ + tΨ) = Winf Φ + 2t WinfBil Φ Ψ + t² Winf Ψ`, `WinfBil Φ Φ = Winf Φ`;
its arch channel is `∫ a(t) ρ_{f,g}(t) dt` with the polarised spectral density `ρ_{f,g}`.
-/

namespace Cvs.L2a.FullTailPolarisation

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence Cvs.L2a.TailLogScaleTest
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open scoped FourierTransform ComplexConjugate

/-! ### The polarised channels -/

/-- The polarised Lévy integral `½∫_{u>0} ρ_U(u)(P(0) − P(u/2))`, `P` the polarised self-convolution. -/
noncomputable def archFullBil (f k : ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
    * (Cvs.WeilForm.TruncatedFormPolarised.polar f k 0 - Cvs.WeilForm.TruncatedFormPolarised.polar f k (u / 2)) / 2

/-- The polarised spectral density `Re(𝓕f · conj 𝓕k)(t/2π)/2π`. -/
noncomputable def crossSpec (f k : ℝ → ℝ) (t : ℝ) : ℝ :=
  (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) (t / (2 * π)) * conj (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf k) (t / (2 * π)))).re
    / (2 * π)

/-- The polarised pole channel `Π₊(Φ)Π₋(Ψ) + Π₊(Ψ)Π₋(Φ)`. -/
noncomputable def poleBil (Φ Ψ : ℝ → ℝ) : ℝ :=
  Cvs.L2a.FullTailPoleChannel.piPlus Φ * (∫ θ in Ioi 1, fullTail Ψ θ / θ)
    + Cvs.L2a.FullTailPoleChannel.piPlus Ψ * (∫ θ in Ioi 1, fullTail Φ θ / θ)

/-- The polarised arch channel `a₀⟨F_Φ, F_Ψ⟩ + archFullBil f_Φ f_Ψ`. -/
noncomputable def archBil (Φ Ψ : ℝ → ℝ) : ℝ :=
  archSymbol 0 * (∫ θ in Ioi 1, fullTail Φ θ * fullTail Ψ θ)
    + archFullBil (logScale (fullTail Φ)) (logScale (fullTail Ψ))

/-- The polarised prime channel `∫⟨F_Φ, F_Ψ − F_{Ψ,k}⟩ + ⟨F_Ψ, F_Φ − F_{Φ,k}⟩ dk/k − 2∫ log θ F_Φ F_Ψ`. -/
noncomputable def primeBil (Φ Ψ : ℝ → ℝ) : ℝ :=
  (∫ k in Ioi 1, (∫ θ in Ioi 1, (fullTail Φ θ * (fullTail Ψ θ - posTail Ψ k θ)
      + fullTail Ψ θ * (fullTail Φ θ - posTail Φ k θ))) / k)
    - 2 * ∫ θ in Ioi 1, Real.log θ * (fullTail Φ θ * fullTail Ψ θ)

/-- The polarisation of `W_∞`: pole plus arch less prime. -/
noncomputable def WinfBil (Φ Ψ : ℝ → ℝ) : ℝ := poleBil Φ Ψ + archBil Φ Ψ - primeBil Φ Ψ

/-! ### Symmetry and the diagonal -/

/-- On the diagonal `archFullBil` is the Lévy integral. -/
theorem archFullBil_self (f : ℝ → ℝ) : archFullBil f f = Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f := by
  unfold archFullBil Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull
  congr 1; funext u
  simp only [Cvs.WeilForm.TruncatedFormPolarised.polar, ← Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_eq_crossConv]; ring

/-- On the diagonal `WinfBil` is `Winf`. -/
theorem WinfBil_self (Φ : ℝ → ℝ) : WinfBil Φ Φ = Cvs.L2a.FullTailWeilFormLimit.Winf Φ := by
  simp only [WinfBil, poleBil, archBil, primeBil, archFullBil_self, Cvs.L2a.FullTailWeilFormLimit.Winf,
    Cvs.L2a.FullTailPrimeChannel.primeInf, ← two_mul, integral_const_mul, mul_div_assoc, ← sq]
  ring

/-! ### Generic integral identities -/

/-- `∫ (a + s b + r d) = ∫ a + s ∫ b + r ∫ d` on a set. -/
theorem setIntegral_add_smul_add_smul {S : Set ℝ} {a b d : ℝ → ℝ} (ha : IntegrableOn a S)
    (hb : IntegrableOn b S) (hd : IntegrableOn d S) (s r : ℝ) :
    ∫ x in S, (a x + s * b x + r * d x) = (∫ x in S, a x) + s * (∫ x in S, b x) + r * ∫ x in S, d x := by
  have h1 : IntegrableOn (fun x => a x + s * b x) S := ha.add (hb.const_mul s)
  rw [integral_add h1 (hd.const_mul r), integral_add ha (hb.const_mul s), integral_const_mul,
    integral_const_mul]

/-- `F/θ` is integrable on `(1, ∞)` for `|F| ≤ K/θ`. -/
theorem integrableOn_div_of_le {f : ℝ → ℝ} {K : ℝ} (hf : Measurable f) (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) :
    IntegrableOn (fun θ => f θ / θ) (Ioi 1) := by
  refine (integrableOn_mul_of_le hf measurable_inv hfK (K' := 1) (fun θ hθ => ?_)).congr_fun
    (fun θ _ => by simp only [div_eq_mul_inv]) measurableSet_Ioi
  rw [abs_of_pos (inv_pos.mpr hθ), one_div]

/-- `log θ · f h` is integrable on `(1, ∞)` for `|f| ≤ K/θ`, `|h| ≤ K'/θ`. -/
theorem integrableOn_log_mul_of_le {f h : ℝ → ℝ} {K K' : ℝ} (hf : Measurable f) (hh : Measurable h)
    (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) (hhK : ∀ θ, 0 < θ → |h θ| ≤ K' / θ) :
    IntegrableOn (fun θ => Real.log θ * (f θ * h θ)) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (show -(7 / 4 : ℝ) < -1 by norm_num) one_pos).const_mul
    (4 * (K * K'))) (measurable_log.mul (hf.mul hh)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
  have hθ0 : 0 < θ := one_pos.trans hθ
  have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ.le
  have hlog : Real.log θ ≤ θ ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hθ0.le (by norm_num)
  have hK : 0 ≤ K / θ := (abs_nonneg _).trans (hfK θ hθ0)
  have hfh : |f θ * h θ| ≤ K / θ * (K' / θ) := by
    rw [abs_mul]; exact mul_le_mul (hfK θ hθ0) (hhK θ hθ0) (abs_nonneg _) hK
  have hr : θ ^ (-(7 / 4 : ℝ)) = θ ^ (1 / 4 : ℝ) / θ ^ 2 := by
    rw [show -(7 / 4 : ℝ) = 1 / 4 - 2 by norm_num, rpow_sub hθ0, rpow_two]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hl0, hr]
  calc Real.log θ * |f θ * h θ| ≤ θ ^ (1 / 4 : ℝ) / (1 / 4) * (K / θ * (K' / θ)) :=
        mul_le_mul hlog hfh (abs_nonneg _) (hl0.trans hlog)
    _ = 4 * (K * K') * (θ ^ (1 / 4 : ℝ) / θ ^ 2) := by field_simp

/-! ### Linearity of the tails -/

/-- **The position-truncated tail is linear.** -/
theorem posTail_add_smul (Φ Ψ : ℝ → ℝ) (t X θ : ℝ) :
    posTail (fun ξ => Φ ξ + t * Ψ ξ) X θ = posTail Φ X θ + t * posTail Ψ X θ := by
  rw [posTail_eq_sum, posTail_eq_sum, posTail_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hθ : θ ∈ Ioc 1 (X / m)
  · simp only [indicator_of_mem hθ]
  · simp only [indicator_of_notMem hθ]; ring

/-- **The full tail is linear** wherever the partial sums of both summands converge. -/
theorem fullTail_add_smul_of_tendsto {Φ Ψ : ℝ → ℝ}
    (hΦ : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop (𝓝 (fullTail Φ θ)))
    (hΨ : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Ψ (m * θ)) atTop (𝓝 (fullTail Ψ θ)))
    (t : ℝ) :
    fullTail (fun ξ => Φ ξ + t * Ψ ξ) = fun θ => fullTail Φ θ + t * fullTail Ψ θ := by
  funext θ
  by_cases hθ : 1 < θ
  · rw [fullTail, ite_eq_left hθ]
    refine Tendsto.limUnder_eq (((hΦ θ hθ).add ((hΨ θ hθ).const_mul t)).congr fun M => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  · simp [fullTail, hθ]

/-- **The improper integral is linear** on continuous integrands with convergent tails. -/
theorem tailInt_add_smul {Φ Ψ : ℝ → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {u a b : ℝ}
    (ha : Tendsto (fun Y : ℝ => ∫ ξ in u..Y, Φ ξ) atTop (𝓝 a))
    (hb : Tendsto (fun Y : ℝ => ∫ ξ in u..Y, Ψ ξ) atTop (𝓝 b)) (t : ℝ) :
    Cvs.L2a.FullTailPoleChannel.tailInt (fun ξ => Φ ξ + t * Ψ ξ) u = a + t * b := by
  unfold Cvs.L2a.FullTailPoleChannel.tailInt
  refine Tendsto.limUnder_eq ((ha.add (hb.const_mul t)).congr fun Y => ?_)
  rw [intervalIntegral.integral_add (hΦ.intervalIntegrable _ _) ((hΨ.intervalIntegrable _ _).const_mul t),
    intervalIntegral.integral_const_mul]

variable {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c : ℝ}

/-- **The cosine transform is linear** in the profile. -/
theorem psi_add_smul (hg : ContinuousOn g (uIcc (-1) 1)) (hh : ContinuousOn h (uIcc (-1) 1)) (c t : ℝ) :
    psi c (fun s => g s + t * h s) = fun ξ => psi c g ξ + t * psi c h ξ := by
  funext ξ
  have hcos : ContinuousOn (fun s => Real.cos (c * ξ * s)) (uIcc (-1) 1) :=
    (by fun_prop : Continuous fun s : ℝ => Real.cos (c * ξ * s)).continuousOn
  have i1 : IntervalIntegrable (fun s => g s * Real.cos (c * ξ * s)) volume (-1) 1 :=
    (hg.mul hcos).intervalIntegrable
  have i2 : IntervalIntegrable (fun s => h s * Real.cos (c * ξ * s)) volume (-1) 1 :=
    (hh.mul hcos).intervalIntegrable
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 (i2.const_mul t)]
  congr 1; funext s; ring

/-- The `C²` data of a profile combination. -/
theorem hasDerivAt_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (t : ℝ) :
    ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => g s + t * h s) (g₁ s + t * h₁ s) s :=
  fun s hs => (hg s hs).add ((hh s hs).const_mul t)

/-- **The full tail is linear** on cosine transforms of `C²` profiles. -/
theorem fullTail_psi_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    fullTail (fun ξ => psi c g ξ + t * psi c h ξ) = fun θ => fullTail (psi c g) θ + t * fullTail (psi c h) θ :=
  fullTail_add_smul_of_tendsto (fun _ hθ => tendsto_partial hg hg₁ hg₂c hc hθ)
    (fun _ hθ => tendsto_partial hh hh₁ hh₂c hc hθ) t

/-- **`Π₊` is linear** on cosine transforms of `C²` profiles. -/
theorem piPlus_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    Cvs.L2a.FullTailPoleChannel.piPlus (fun ξ => psi c g ξ + t * psi c h ξ)
      = Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) + t * Cvs.L2a.FullTailPoleChannel.piPlus (psi c h) := by
  have hΦ : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hΨ : Continuous (psi c h) :=
    (contDiff_psi (fun s hs => (hh s hs).continuousAt.continuousWithinAt) c).continuous
  have e : ∀ m : ℕ, Cvs.L2a.FullTailPoleChannel.tailInt (fun ξ => psi c g ξ + t * psi c h ξ) ((m : ℝ) + 1)
        / ((m : ℝ) + 1)
      = Cvs.L2a.FullTailPoleChannel.tailInt (psi c g) ((m : ℝ) + 1) / ((m : ℝ) + 1)
        + t * (Cvs.L2a.FullTailPoleChannel.tailInt (psi c h) ((m : ℝ) + 1) / ((m : ℝ) + 1)) := by
    intro m
    have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := m.cast_nonneg (α := ℝ); linarith
    rw [tailInt_add_smul hΦ hΨ (Cvs.L2a.FullTailPoleChannel.tendsto_tailInt hg hg₁ hg₂c hc hm)
      (Cvs.L2a.FullTailPoleChannel.tendsto_tailInt hh hh₁ hh₂c hc hm) t]
    ring
  unfold Cvs.L2a.FullTailPoleChannel.piPlus
  rw [tsum_congr e, (Cvs.L2a.FullTailPoleChannel.summable_piPlus hg hg₁ hg₂c hc).tsum_add
    ((Cvs.L2a.FullTailPoleChannel.summable_piPlus hh hh₁ hh₂c hc).mul_left t), tsum_mul_left]

/-! ### The channels of a combination -/

/-- **The pole channel of a combination.** -/
theorem pole_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    2 * Cvs.L2a.FullTailPoleChannel.piPlus (fun ξ => psi c g ξ + t * psi c h ξ)
        * (∫ θ in Ioi 1, fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ / θ)
      = 2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (∫ θ in Ioi 1, fullTail (psi c g) θ / θ)
        + 2 * t * poleBil (psi c g) (psi c h)
        + t ^ 2 * (2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c h) * (∫ θ in Ioi 1, fullTail (psi c h) θ / θ)) := by
  have i1 := integrableOn_div_of_le (measurable_fullTail hg hg₁ hg₂c hc)
    fun θ hθ => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have i2 := integrableOn_div_of_le (measurable_fullTail hh hh₁ hh₂c hc)
    fun θ hθ => abs_fullTail_le hh hh₁ hh₂c hc hθ
  have e : ∫ θ in Ioi 1, fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ / θ
      = (∫ θ in Ioi 1, fullTail (psi c g) θ / θ) + t * ∫ θ in Ioi 1, fullTail (psi c h) θ / θ := by
    simp only [fullTail_psi_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t]
    calc _ = ∫ θ in Ioi 1, (fullTail (psi c g) θ / θ + t * (fullTail (psi c h) θ / θ)) := by
          congr 1; funext θ; ring
      _ = _ := by rw [integral_add i1 (i2.const_mul t), integral_const_mul]
  rw [piPlus_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t, e, poleBil]
  ring

/-- `∫ (F + tG)² = ∫ F² + 2t⟨F, G⟩ + t² ∫ G²` for the full tails. -/
theorem integral_sq_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    ∫ θ in Ioi 1, (fullTail (psi c g) θ + t * fullTail (psi c h) θ) ^ 2
      = (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
        + 2 * t * (∫ θ in Ioi 1, fullTail (psi c g) θ * fullTail (psi c h) θ)
        + t ^ 2 * ∫ θ in Ioi 1, fullTail (psi c h) θ ^ 2 := by
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hGm := measurable_fullTail hh hh₁ hh₂c hc
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hGb := fun θ (hθ : 0 < θ) => abs_fullTail_le hh hh₁ hh₂c hc hθ
  calc _ = ∫ θ in Ioi 1, (fullTail (psi c g) θ ^ 2 + (2 * t) * (fullTail (psi c g) θ * fullTail (psi c h) θ)
          + t ^ 2 * fullTail (psi c h) θ ^ 2) := by congr 1; funext θ; ring
    _ = _ := setIntegral_add_smul_add_smul (integrableOn_sq_of_le hFm hFb)
          (integrableOn_mul_of_le hFm hGm hFb hGb) (integrableOn_sq_of_le hGm hGb) _ _

/-- The log-scale profile is linear. -/
theorem logScale_add_smul (F G : ℝ → ℝ) (t : ℝ) :
    logScale (fun θ => F θ + t * G θ) = fun s => logScale F s + t * logScale G s := by
  funext s; simp only [logScale]; ring

/-- The self-convolution is quadratic: `S_{tk} = t² S_k`. -/
theorem selfConvolution_const_mul (k : ℝ → ℝ) (t v : ℝ) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (fun x => t * k x) v = t ^ 2 * Cvs.Zeta.Explicit.Weil.selfConvolution k v := by
  simp only [Cvs.Zeta.Explicit.Weil.selfConvolution]
  rw [← integral_const_mul]; congr 1; funext x; ring

/-- The Lévy integrand is quadratic: `levy (t k) = t² levy k`. -/
theorem levy_const_mul (k : ℝ → ℝ) (t u : ℝ) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => t * k x) u = t ^ 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy k u := by
  simp only [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, selfConvolution_const_mul]; ring

/-- The Lévy integrand of a combination is integrable when both summands' are. -/
theorem integrableOn_levy_add_smul {f k : ℝ → ℝ} (hf : MemLp f 2 volume) (hk : MemLp k 2 volume)
    (hlf : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hlk : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy k) (Ioi 0) volume) (t : ℝ) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => f x + t * k x)) (Ioi 0) volume := by
  have h := Cvs.WeilForm.Archimedean.LevyUnitBlocks.integrableOn_levy_sub hf (hk.const_mul (-t)) hlf
    (IntegrableOn.congr_fun (hlk.const_mul ((-t) ^ 2)) (fun u _ => (levy_const_mul k (-t) u).symm)
      measurableSet_Ioi)
  have e : (f - fun x => -t * k x) = fun x => f x + t * k x := by funext x; simp only [Pi.sub_apply]; ring
  rwa [e] at h

/-- **The Lévy integral of a combination**, polarised. -/
theorem archFull_add_smul {f k : ℝ → ℝ} (hf : MemLp f 2 volume) (hk : MemLp k 2 volume)
    (hlf : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hlk : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy k) (Ioi 0) volume) (t : ℝ) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (fun x => f x + t * k x)
      = Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f + 2 * t * archFullBil f k + t ^ 2 * Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull k := by
  have hS := integrableOn_levy_add_smul hf hk hlf hlk 1
  have hP : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.WeilForm.TruncatedFormPolarised.polar f k 0 - Cvs.WeilForm.TruncatedFormPolarised.polar f k (u / 2)) / 2) (Ioi 0) volume := by
    refine IntegrableOn.congr_fun (((hS.sub hlf).sub hlk).div_const 2) (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_add_smul hf hk 1]
    ring
  have e : ∀ u ∈ Ioi (0 : ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Zeta.Explicit.Weil.selfConvolution (fun x => f x + t * k x) 0
        - Cvs.Zeta.Explicit.Weil.selfConvolution (fun x => f x + t * k x) (u / 2))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u + 2 * t * (Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (Cvs.WeilForm.TruncatedFormPolarised.polar f k 0 - Cvs.WeilForm.TruncatedFormPolarised.polar f k (u / 2)) / 2)
        + t ^ 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy k u := by
    intro u _
    simp only [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_add_smul hf hk t]
    ring
  unfold Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull archFullBil
  rw [setIntegral_congr_fun measurableSet_Ioi e]
  exact setIntegral_add_smul_add_smul hlf hP hlk _ _

/-- **The arch channel of a combination.** -/
theorem arch_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    archSymbol 0 * (∫ θ in Ioi 1, fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ ^ 2)
        + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (fun ξ => psi c g ξ + t * psi c h ξ)))
      = (archSymbol 0 * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
          + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c g))))
        + 2 * t * archBil (psi c g) (psi c h)
        + t ^ 2 * (archSymbol 0 * (∫ θ in Ioi 1, fullTail (psi c h) θ ^ 2)
          + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c h)))) := by
  obtain ⟨hf2, -⟩ := memLp_logScale_fullTail hg hg₁ hg₂c hc
  obtain ⟨hk2, -⟩ := memLp_logScale_fullTail hh hh₁ hh₂c hc
  simp only [fullTail_psi_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t, logScale_add_smul]
  rw [integral_sq_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t,
    archFull_add_smul hf2 hk2 (Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc)
      (Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hh hh₁ hh₂c hc) t, archBil]
  ring

/-- **The level of a combination**: `⟨F, F − F_k⟩` expands with the polarised level as cross term. -/
theorem level_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t k : ℝ) :
    ∫ θ in Ioi 1, fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ
        * (fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ - posTail (fun ξ => psi c g ξ + t * psi c h ξ) k θ)
      = (∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ))
        + t * (∫ θ in Ioi 1, (fullTail (psi c g) θ * (fullTail (psi c h) θ - posTail (psi c h) k θ)
            + fullTail (psi c h) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)))
        + t ^ 2 * ∫ θ in Ioi 1, fullTail (psi c h) θ * (fullTail (psi c h) θ - posTail (psi c h) k θ) := by
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hGm := measurable_fullTail hh hh₁ hh₂c hc
  have hPm := measurable_posTail_psi hg c k
  have hQm := measurable_posTail_psi hh c k
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hGb := fun θ (hθ : 0 < θ) => abs_fullTail_le hh hh₁ hh₂c hc hθ
  have hFPb : ∀ θ, 0 < θ → |fullTail (psi c g) θ - posTail (psi c g) k θ|
      ≤ 2 * BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / θ := fun θ hθ => by
    rw [abs_sub_comm]; exact abs_posTail_sub_le hg hg₁ hg₂c hc k hθ
  have hGQb : ∀ θ, 0 < θ → |fullTail (psi c h) θ - posTail (psi c h) k θ|
      ≤ 2 * BG c (h 1 + h (-1)) (|h₁ 1 - h₁ (-1)| + ∫ s in (-1 : ℝ)..1, |h₂ s|) / θ := fun θ hθ => by
    rw [abs_sub_comm]; exact abs_posTail_sub_le hh hh₁ hh₂c hc k hθ
  have i1 := integrableOn_mul_of_le hFm (hFm.sub hPm) hFb hFPb
  have i2 := (integrableOn_mul_of_le hFm (hGm.sub hQm) hFb hGQb).add
    (integrableOn_mul_of_le hGm (hFm.sub hPm) hGb hFPb)
  have i3 := integrableOn_mul_of_le hGm (hGm.sub hQm) hGb hGQb
  simp only [fullTail_psi_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t, posTail_add_smul]
  calc _ = ∫ θ in Ioi 1, (fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)
          + t * (fullTail (psi c g) θ * (fullTail (psi c h) θ - posTail (psi c h) k θ)
            + fullTail (psi c h) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ))
          + t ^ 2 * (fullTail (psi c h) θ * (fullTail (psi c h) θ - posTail (psi c h) k θ))) := by
        congr 1; funext θ; ring
    _ = _ := setIntegral_add_smul_add_smul i1 i2 i3 _ _

/-- **The prime channel of a combination.** -/
theorem primeInf_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    Cvs.L2a.FullTailPrimeChannel.primeInf (fun ξ => psi c g ξ + t * psi c h ξ)
      = Cvs.L2a.FullTailPrimeChannel.primeInf (psi c g) + 2 * t * primeBil (psi c g) (psi c h)
        + t ^ 2 * Cvs.L2a.FullTailPrimeChannel.primeInf (psi c h) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have iL1 := Cvs.L2a.FullTailPrimeChannel.integrableOn_level hg hg₁ hg₂c hc
  have iL2 := Cvs.L2a.FullTailPrimeChannel.integrableOn_level hh hh₁ hh₂c hc
  have iLS := Cvs.L2a.FullTailPrimeChannel.integrableOn_level (hasDerivAt_add_smul hg hh 1)
    (hasDerivAt_add_smul hg₁ hh₁ 1) (hg₂c.add (continuousOn_const.mul hh₂c)) hc
  rw [psi_add_smul hgc hhc c 1] at iLS
  have iB : IntegrableOn (fun k => (∫ θ in Ioi 1, (fullTail (psi c g) θ * (fullTail (psi c h) θ
      - posTail (psi c h) k θ) + fullTail (psi c h) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ))) / k)
      (Ioi 1) := by
    refine ((iLS.sub iL1).sub iL2).congr_fun (fun k _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [level_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc 1 k]
    ring
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hGm := measurable_fullTail hh hh₁ hh₂c hc
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hGb := fun θ (hθ : 0 < θ) => abs_fullTail_le hh hh₁ hh₂c hc hθ
  have iG1 : IntegrableOn (fun θ => Real.log θ * fullTail (psi c g) θ ^ 2) (Ioi 1) :=
    (integrableOn_log_mul_of_le hFm hFm hFb hFb).congr_fun (fun θ _ => by simp only [sq]) measurableSet_Ioi
  have iG2 : IntegrableOn (fun θ => Real.log θ * fullTail (psi c h) θ ^ 2) (Ioi 1) :=
    (integrableOn_log_mul_of_le hGm hGm hGb hGb).congr_fun (fun θ _ => by simp only [sq]) measurableSet_Ioi
  have iG12 := integrableOn_log_mul_of_le hFm hGm hFb hGb
  have eOuter : ∫ k in Ioi 1, (∫ θ in Ioi 1, fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ
        * (fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ
          - posTail (fun ξ => psi c g ξ + t * psi c h ξ) k θ)) / k
      = (∫ k in Ioi 1, (∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)) / k)
        + t * (∫ k in Ioi 1, (∫ θ in Ioi 1, (fullTail (psi c g) θ * (fullTail (psi c h) θ
            - posTail (psi c h) k θ) + fullTail (psi c h) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ))) / k)
        + t ^ 2 * ∫ k in Ioi 1,
            (∫ θ in Ioi 1, fullTail (psi c h) θ * (fullTail (psi c h) θ - posTail (psi c h) k θ)) / k := by
    rw [← setIntegral_add_smul_add_smul iL1 iB iL2]
    congr 1; funext k
    rw [level_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t k]
    ring
  have eLog : ∫ θ in Ioi 1, Real.log θ * fullTail (fun ξ => psi c g ξ + t * psi c h ξ) θ ^ 2
      = (∫ θ in Ioi 1, Real.log θ * fullTail (psi c g) θ ^ 2)
        + 2 * t * (∫ θ in Ioi 1, Real.log θ * (fullTail (psi c g) θ * fullTail (psi c h) θ))
        + t ^ 2 * ∫ θ in Ioi 1, Real.log θ * fullTail (psi c h) θ ^ 2 := by
    rw [← setIntegral_add_smul_add_smul iG1 iG12 iG2]
    simp only [fullTail_psi_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t]
    congr 1; funext θ; ring
  rw [Cvs.L2a.FullTailPrimeChannel.primeInf, eOuter, eLog, Cvs.L2a.FullTailPrimeChannel.primeInf,
    Cvs.L2a.FullTailPrimeChannel.primeInf, primeBil]
  ring

/-! ### `W_∞` is a quadratic form -/

/-- **`W_∞` of a combination**: `Winf (Φ + tΨ) = Winf Φ + 2t WinfBil Φ Ψ + t² Winf Ψ`. -/
theorem Winf_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => psi c g ξ + t * psi c h ξ)
      = Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g) + 2 * t * WinfBil (psi c g) (psi c h)
        + t ^ 2 * Cvs.L2a.FullTailWeilFormLimit.Winf (psi c h) := by
  rw [Cvs.L2a.FullTailWeilFormLimit.Winf, pole_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t,
    arch_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t, primeInf_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t,
    Cvs.L2a.FullTailWeilFormLimit.Winf, Cvs.L2a.FullTailWeilFormLimit.Winf, WinfBil]
  ring

/-- **`W_∞` of a profile combination**: the same identity with `psi c (g + t h)`. -/
theorem Winf_psi_add_smul (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) (t : ℝ) :
    Cvs.L2a.FullTailWeilFormLimit.Winf (psi c (fun s => g s + t * h s))
      = Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g) + 2 * t * WinfBil (psi c g) (psi c h)
        + t ^ 2 * Cvs.L2a.FullTailWeilFormLimit.Winf (psi c h) := by
  rw [psi_add_smul (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hh s hs).continuousAt.continuousWithinAt) c t]
  exact Winf_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc t

/-! ### The arch channel in spectral form -/

/-- The Fourier transform of a combination of integrable functions. -/
theorem fourier_cf_add_smul {f k : ℝ → ℝ} (hf : Integrable f) (hk : Integrable k) (t w : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (fun x => f x + t * k x)) w
      = 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w + (t : ℂ) * 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf k) w := by
  simp only [Real.fourier_eq]
  rw [← integral_const_mul, ← integral_add]
  · congr 1; funext v
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Circle.smul_def, smul_eq_mul]; push_cast; ring
  · exact (Real.fourierIntegral_convergent_iff w).2 hf.ofReal
  · have hI : Integrable (fun a : ℝ => 𝐞 (-inner ℝ a w) •
        Cvs.WeilForm.SelfConvolutionTransform.cf k a) volume :=
      (Real.fourierIntegral_convergent_iff w).2 hk.ofReal
    exact hI.const_mul (t : ℂ)

/-- **The spectral density is quadratic**: `ρ_{f+tk} = ρ_f + 2t ρ_{f,k} + t² ρ_k`. -/
theorem specDensity_add_smul {f k : ℝ → ℝ} (hf : Integrable f) (hk : Integrable k) (t w : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + t * k x) w
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity f w + 2 * t * crossSpec f k w
        + t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity k w := by
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity crossSpec
  rw [fourier_cf_add_smul hf hk]
  set a := 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) (w / (2 * π))
  set b := 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf k) (w / (2 * π))
  have key : ‖a + (t : ℂ) * b‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * (a * conj b).re + t ^ 2 * ‖b‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [key]
  ring

/-- `a · ρ_f` is integrable for `f ∈ L¹ ∩ L²` with integrable Lévy integrand. -/
theorem integrable_arch_mul_specDensity {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (h1 : Integrable f)
    (hl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume) :
    Integrable (fun t => archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) := by
  refine ((Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch h2 h1 hl).add
    ((Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1).const_mul (archSymbol 0))).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]; ring

/-- **The polarised arch integral**: `∫ a ρ_{f,k} = ½(∫ a ρ_{f+k} − ∫ a ρ_f − ∫ a ρ_k)`. -/
theorem integral_arch_crossSpec {f k : ℝ → ℝ} (hf2 : MemLp f 2 volume) (hf1 : Integrable f)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hk2 : MemLp k 2 volume) (hk1 : Integrable k)
    (hkl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy k) (Ioi 0) volume) :
    ∫ t, archSymbol t * crossSpec f k t
      = ((∫ t, archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + 1 * k x) t)
        - (∫ t, archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
        - ∫ t, archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) / 2 := by
  have iS := integrable_arch_mul_specDensity (f := fun x => f x + 1 * k x) (hf2.add (hk2.const_mul 1))
    (hf1.add (hk1.const_mul 1))
    (integrableOn_levy_add_smul hf2 hk2 hfl hkl 1)
  have iF := integrable_arch_mul_specDensity hf2 hf1 hfl
  have iK := integrable_arch_mul_specDensity hk2 hk1 hkl
  have iSF : Integrable (fun t => archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + 1 * k x) t
      - archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) := iS.sub iF
  have e : ∀ t, archSymbol t * crossSpec f k t
      = (archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + 1 * k x) t
        - archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
        - archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) / 2 := by
    intro t; rw [specDensity_add_smul hf1 hk1 1 t]; ring
  rw [integral_congr_ae (Eventually.of_forall e), integral_div, integral_sub iSF iK, integral_sub iS iF]

/-- **The arch channel of `WinfBil` in spectral form**: `a₀⟨F_Φ, F_Ψ⟩ + archFullBil = ∫ a(t) ρ_{f_Φ,f_Ψ}(t) dt`. -/
theorem arch_bil_eq_spectral (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    archBil (psi c g) (psi c h)
      = ∫ t, archSymbol t * crossSpec (logScale (fullTail (psi c g))) (logScale (fullTail (psi c h))) t := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  obtain ⟨hf2, hf1⟩ := memLp_logScale_fullTail hg hg₁ hg₂c hc
  obtain ⟨hk2, hk1⟩ := memLp_logScale_fullTail hh hh₁ hh₂c hc
  have hfl := Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc
  have hkl := Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hh hh₁ hh₂c hc
  have Ag := Cvs.L2a.FullTailWeilFormLimit.arch_fullTail_eq_spectral hg hg₁ hg₂c hc
  have Ah := Cvs.L2a.FullTailWeilFormLimit.arch_fullTail_eq_spectral hh hh₁ hh₂c hc
  have AS := Cvs.L2a.FullTailWeilFormLimit.arch_fullTail_eq_spectral (hasDerivAt_add_smul hg hh 1)
    (hasDerivAt_add_smul hg₁ hh₁ 1) (hg₂c.add (continuousOn_const.mul hh₂c)) hc
  simp only [psi_add_smul hgc hhc c 1, fullTail_psi_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc 1,
    logScale_add_smul] at AS
  rw [integral_sq_add_smul hg hg₁ hg₂c hh hh₁ hh₂c hc 1, archFull_add_smul hf2 hk2 hfl hkl 1] at AS
  rw [integral_arch_crossSpec hf2 hf1 hfl hk2 hk1 hkl, archBil]
  linear_combination (AS - Ag - Ah) / 2

end Cvs.L2a.FullTailPolarisation
