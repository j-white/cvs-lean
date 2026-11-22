import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.WeilForm.ChannelCapByDuality
import Cvs.WeilForm.ChannelEnergyIdentity
import Cvs.WeilForm.ChannelQuadGreenFunction
import Cvs.WeilForm.OddPoleTermBound

/-!
# The channel cap from the energy identity and the Robin–Poincaré bound

    Poincaré `t²∫K² ≤ ∫K'² + b(K(0)²+K(L)²)`   ⟹
        `∫ s, f s · ∫ u, f u · e^{−b|s−u|} ≤ (2b/(b²+t²)) · ∫ f²`

for continuous `f` supported in `[0, L]`, `K = convSplit b L f`.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.ChannelCapEnergyPoincare

/-- **The per-channel cap.** -/
theorem channel_cap {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : Continuous f)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → f x = 0) {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (hpoin : t ^ 2 * (∫ s in (0:ℝ)..L, Cvs.Finite.ExponentialKernelLocalises.convSplit b L f s ^ 2)
      ≤ (∫ s in (0:ℝ)..L, Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f s ^ 2)
        + b * (Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 ^ 2
          + Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L ^ 2)) :
    (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      ≤ (2 * b / (b ^ 2 + t ^ 2)) * ∫ x, f x ^ 2 := by
  set K := Cvs.Finite.ExponentialKernelLocalises.convSplit b L f with hK
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun s =>
    (Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convSplit hf s).continuousAt
  -- names for the integrals
  set pair := ∫ s in (0:ℝ)..L, f s * K s with hpair
  set IK2 := ∫ s in (0:ℝ)..L, K s ^ 2 with hIK2
  set If2 := ∫ x, f x ^ 2 with hIf2
  have hchan : (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|))) = pair :=
    Cvs.WeilForm.ChannelQuadGreenFunction.channelQuad_convSplit hL hf hsupp b
  have henergy := Cvs.WeilForm.ChannelEnergyIdentity.energy_identity hL hf b
  rw [← hK] at henergy
  -- `∫ f² = ∫₀^L f²`, both nonneg
  have hIf2eq : If2 = ∫ s in (0:ℝ)..L, f s ^ 2 := by
    rw [hIf2, intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) L)
        (fun x hx => by rw [hsupp x hx]; ring)]
  have hIf2nn : 0 ≤ If2 :=
    integral_nonneg fun x => sq_nonneg _
  have hIK2nn : 0 ≤ IK2 :=
    intervalIntegral.integral_nonneg hL fun s _ => sq_nonneg _
  -- Cauchy–Schwarz: `pair² ≤ (∫₀^L f²)·IK2`
  have hCS : pair ^ 2 ≤ (∫ s in (0:ℝ)..L, f s ^ 2) * IK2 :=
    Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le hL
      ((hf.pow 2).continuousOn.intervalIntegrable)
      ((hKc.pow 2).continuousOn.intervalIntegrable)
      ((hf.mul hKc).continuousOn.intervalIntegrable)
  rw [← hIf2eq] at hCS
  -- dual cap
  set lam := 2 * b / (b ^ 2 + t ^ 2) with hlam
  have hden : 0 < b ^ 2 + t ^ 2 := by positivity
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hng : 0 ≤ Real.sqrt IK2 := Real.sqrt_nonneg _
  have hnf : 0 ≤ Real.sqrt If2 := Real.sqrt_nonneg _
  rw [hchan]
  have hcap := Cvs.WeilForm.ChannelCapByDuality.cap_of_dual (lam := lam) (ng := Real.sqrt IK2)
    (nf := Real.sqrt If2) (pair := pair) (Qg := pair) hlampos rfl ?_ ?_ hng hnf
  · rw [Real.sq_sqrt hIf2nn] at hcap; exact hcap
  · -- `ng²/lam ≤ Qg`
    rw [Real.sq_sqrt hIK2nn, div_le_iff₀ hlampos, hlam,
      show pair * (2 * b / (b ^ 2 + t ^ 2)) = pair * (2 * b) / (b ^ 2 + t ^ 2) by ring,
      le_div_iff₀ hden]
    nlinarith [henergy, hpoin]
  · -- `pair ≤ ng·nf`, from `pair² ≤ (ng·nf)²`
    have hsq : pair ^ 2 ≤ (Real.sqrt IK2 * Real.sqrt If2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hIK2nn, Real.sq_sqrt hIf2nn, mul_comm]
      exact hCS
    have hM : (0:ℝ) ≤ Real.sqrt IK2 * Real.sqrt If2 := by positivity
    have habs : |pair| ≤ |Real.sqrt IK2 * Real.sqrt If2| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    calc pair ≤ |pair| := le_abs_self _
      _ ≤ |Real.sqrt IK2 * Real.sqrt If2| := habs
      _ = Real.sqrt IK2 * Real.sqrt If2 := abs_of_nonneg hM

end Cvs.WeilForm.ChannelCapEnergyPoincare
