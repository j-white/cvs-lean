import Mathlib
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The secular polynomial of the universal factor is real-rooted whenever step (a) holds
`R_x(u) = P_x(u²)/∏_l (q_l − u²)` with the scale-free polynomial `P_x(w) = ∑_k x_k ∏_{l≠k}(q_l − w)`,
and the Fourier–Laplace transform of the mode sum is `i·z·(e^{izL} − 1)·S(z)`. So the certified
zero-freeness off the axes (`Cvs.Finite.TruncationZeroFreeOffAxes`, `Cvs.Finite.DisplacementIdentity`, `Cvs.Limit.StepAZeroFreeMinimiser`) says exactly that `P_x` has no non-real
root: the discrete minimiser's `K − 1` secular roots `w_j` are real, and the nesting question is
how `w_j(x(L))` (which the minimiser places near `(Lγ_j)²`) moves with `L`.
-/

noncomputable section

open Real Filter Topology Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.SecularRealRooted
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- **The Fourier–Laplace transform of an even mode sum is `i·z·(e^{izL} − 1)·S(z)`.** -/
theorem fourierLaplace_eq_S {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) {z : ℂ}
    (hz : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z ≠ 0) :
    FourierLaplace.fourierLaplace (cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)) z
      = Complex.I * z * (Complex.exp (Complex.I * z * (L : ℂ)) - 1)
        * Cvs.Finite.UniversalFunctionPairing.S L mode xi z := by
  classical
  rw [Cvs.Finite.TruncationZeroFreeOffAxes.fourierLaplace_modeSum hL hinv hmode hxieven z hz]
  -- the odd part of the partial-fraction sum vanishes
  have hz' : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) - z ≠ 0 := by
    intro i
    have := hz (neg i)
    rw [Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg hmode] at this
    intro h; apply this; push_cast; linear_combination -h
  have hsplit : ∀ i, (xi i : ℂ) / (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z)
      = -z * ((xi i : ℂ) / (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) ^ 2 - z ^ 2))
        + ((xi i : ℂ) * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ))
          / (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) ^ 2 - z ^ 2) := by
    intro i
    have h1 := hz i; have h2 := hz' i
    have h3 : ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) ^ 2 - z ^ 2
        = (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z)
          * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) - z) := by ring
    rw [h3]
    field_simp
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hodd : ∑ i, ((xi i : ℂ) * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ))
      / (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) ^ 2 - z ^ 2) = 0 := by
    set g : ι → ℂ := fun i => ((xi i : ℂ) * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ))
      / (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) ^ 2 - z ^ 2) with hg
    have h2 : ∀ i, g (neg i) = -g i := by
      intro i
      simp only [hg, hxieven, Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg hmode]
      push_cast
      ring
    have hS : ∑ i, g i = -∑ i, g i := by
      calc ∑ i, g i = ∑ i, g (neg i) :=
            (Equiv.sum_comp (Function.Involutive.toPerm neg hinv) g).symm
        _ = ∑ i, -g i := Finset.sum_congr rfl fun i _ => h2 i
        _ = -∑ i, g i := Finset.sum_neg_distrib g
    have h3 : (2 : ℂ) * ∑ i, g i = 0 := by linear_combination hS
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
  rw [hodd, add_zero]
  have hI : (Complex.exp (Complex.I * z * (L : ℂ)) - 1) / Complex.I
      = -Complex.I * (Complex.exp (Complex.I * z * (L : ℂ)) - 1) := by
    rw [div_eq_iff Complex.I_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hI]
  unfold Cvs.Finite.UniversalFunctionPairing.S Cvs.Finite.TruncationZeroFreeOffAxes.omega
  ring

end Cvs.Finite.SecularRealRooted
