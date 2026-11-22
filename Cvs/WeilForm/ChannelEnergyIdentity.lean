import Mathlib
import Cvs.Finite.ExponentialKernelLocalises

/-!
# The channel energy identity

    `2b ∫₀^L f·K = b² ∫₀^L K² + b (K(0)² + K(L)²) + ∫₀^L K'²`

for `K = convSplit b L f`, `K' = convDeriv b L f`, by integration by parts with the ODE
`K'' = b²K − 2bf` and the Robin boundary data.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace Cvs.WeilForm.ChannelEnergyIdentity

/-- **The channel energy identity.** -/
theorem energy_identity {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : Continuous f) (b : ℝ) :
    2 * b * ∫ s in (0:ℝ)..L, f s * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f s
      = b ^ 2 * (∫ s in (0:ℝ)..L, Cvs.Finite.ExponentialKernelLocalises.convSplit b L f s ^ 2)
        + b * (Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 ^ 2
          + Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L ^ 2)
        + ∫ s in (0:ℝ)..L, Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f s ^ 2 := by
  set K := Cvs.Finite.ExponentialKernelLocalises.convSplit b L f with hK
  set K' := Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f with hK'
  have hdK : ∀ s, HasDerivAt K (K' s) s := fun s => Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convSplit hf s
  have hdK' : ∀ s, HasDerivAt K' (b ^ 2 * K s - 2 * b * f s) s := fun s =>
    Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convDeriv hf s
  have hKcont : Continuous K := continuous_iff_continuousAt.mpr fun s => (hdK s).continuousAt
  have hK'cont : Continuous K' := continuous_iff_continuousAt.mpr fun s => (hdK' s).continuousAt
  have hprod : ∀ s, HasDerivAt (fun s => K' s * K s)
      ((b ^ 2 * K s - 2 * b * f s) * K s + K' s * K' s) s := fun s => (hdK' s).mul (hdK s)
  have hicont : Continuous fun s => (b ^ 2 * K s - 2 * b * f s) * K s + K' s * K' s := by fun_prop
  have hftc : (∫ s in (0:ℝ)..L, ((b ^ 2 * K s - 2 * b * f s) * K s + K' s * K' s))
      = K' L * K L - K' 0 * K 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hprod s)
      hicont.continuousOn.intervalIntegrable
  have hb0 : K' 0 = b * K 0 := Cvs.Finite.ExponentialKernelLocalises.convDeriv_zero
  have hbL : K' L = -b * K L := Cvs.Finite.ExponentialKernelLocalises.convDeriv_end
  have hbK2 : IntervalIntegrable (fun s => b ^ 2 * K s ^ 2) volume 0 L :=
    (by fun_prop : Continuous fun s => b ^ 2 * K s ^ 2).continuousOn.intervalIntegrable
  have h2bfK : IntervalIntegrable (fun s => 2 * b * (f s * K s)) volume 0 L :=
    (by fun_prop : Continuous fun s => 2 * b * (f s * K s)).continuousOn.intervalIntegrable
  have hK'2 : IntervalIntegrable (fun s => K' s ^ 2) volume 0 L :=
    (by fun_prop : Continuous fun s => K' s ^ 2).continuousOn.intervalIntegrable
  have hsplit : (∫ s in (0:ℝ)..L, ((b ^ 2 * K s - 2 * b * f s) * K s + K' s * K' s))
      = b ^ 2 * (∫ s in (0:ℝ)..L, K s ^ 2)
        - 2 * b * (∫ s in (0:ℝ)..L, f s * K s)
        + ∫ s in (0:ℝ)..L, K' s ^ 2 := by
    have e1 : (∫ s in (0:ℝ)..L, ((b ^ 2 * K s - 2 * b * f s) * K s + K' s * K' s))
        = ∫ s in (0:ℝ)..L, ((b ^ 2 * K s ^ 2 - 2 * b * (f s * K s)) + K' s ^ 2) :=
      intervalIntegral.integral_congr fun s _ => by ring
    rw [e1, intervalIntegral.integral_add (hbK2.sub h2bfK) hK'2,
      intervalIntegral.integral_sub hbK2 h2bfK, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit, hb0, hbL] at hftc
  nlinarith [hftc]

end Cvs.WeilForm.ChannelEnergyIdentity
