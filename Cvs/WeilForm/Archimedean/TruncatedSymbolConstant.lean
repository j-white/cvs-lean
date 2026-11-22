import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.Digamma
import Cvs.Zeta.Digamma.DigammaQuarterConstant
import Cvs.Zeta.Digamma.DigammaQuarterFourierPair

/-!
# The truncated archimedean symbol's constant, and the four-term threshold

    truncConst N = archSymbol 0 + ∑_{n<N} 1/(n+¼) = Re ψ(N+¼) − log π

`archSymbol 0` is `−γ − 3log 2 − π/2 − log π`, so the constant is positive exactly when at
least four Lévy terms are retained.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex

namespace Cvs.WeilForm.Archimedean.TruncatedSymbolConstant

/-- The constant term of the archimedean symbol truncated to its first `N` Lévy poles. -/
def truncConst (N : ℕ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1 / 4))

/-- **`archSymbol 0` in closed form.**  `DigammaQuarterFourierPair`'s value of `ψ(¼)`, with the `log π` of the
archimedean factor. -/
theorem archSymbol_zero_eq :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      = -Real.eulerMascheroniConstant - 3 * Real.log 2 - Real.pi / 2 - Real.log Real.pi := by
  have harg : Cvs.Zeta.digammaArg 0 0 = (1 / 4 : ℂ) := by
    simp [Cvs.Zeta.digammaArg]
  have h2 : (Complex.log 2).re = Real.log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.log_ofReal_re]
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  rw [harg, Cvs.Enclosure.digamma_quarter]
  simp [Complex.sub_re, h2]

/-- **`γ` below `harmonic 16 − log 16`.**  Mathlib's sandwich holds at every index; at sixteen it
gives `γ < 0.60815`, where the library states `2/3` outright. -/
theorem gamma_lt_harmonic16 :
    Real.eulerMascheroniConstant < 2436559 / 720720 - 4 * Real.log 2 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
  rw [Real.eulerMascheroniSeq'] at h
  simp only [if_neg (by norm_num : (16:ℕ) ≠ 0)] at h
  have hh : ((harmonic 16 : ℚ) : ℝ) = 2436559 / 720720 := by norm_num [harmonic]
  have hl : Real.log ((16:ℕ) : ℝ) = 4 * Real.log 2 := by
    rw [show ((16:ℕ) : ℝ) = 2 ^ (4:ℕ) from by norm_num, Real.log_pow]
    push_cast; ring
  rw [hh, hl] at h
  exact h

/-- **Euler's constant, from the sixty-fourth harmonic number.**  `eulerMascheroniSeq'` is
decreasing to `γ`, and `log 64 = 6 log 2`. -/
theorem gamma_lt_harmonic64 :
    Real.eulerMascheroniConstant
      < 623171679694215690971693339 / 131362987122535807501262400 - 6 * Real.log 2 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  rw [Real.eulerMascheroniSeq'] at h
  simp only [if_neg (by norm_num : (64:ℕ) ≠ 0)] at h
  have hh : ((harmonic 64 : ℚ) : ℝ)
      = 623171679694215690971693339 / 131362987122535807501262400 := by
    norm_num [harmonic]
  have hl : Real.log ((64:ℕ) : ℝ) = 6 * Real.log 2 := by
    rw [show ((64:ℕ) : ℝ) = 2 ^ (6:ℕ) from by norm_num, Real.log_pow]
    push_cast; ring
  rw [hh, hl] at h
  exact h

/-- **The archimedean constant, sharpened.**  The same identity as `archSymbol_zero_lower`, with
`γ` taken from index sixty-four rather than sixteen: the `γ` bound was the whole of the loss. -/
theorem archSymbol_zero_lower' : (-5.3801 : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 := by
  obtain ⟨hlp, hlp'⟩ := Cvs.Moments.log_pi_bounds
  have hg := gamma_lt_harmonic64
  have hl1 := Real.log_two_gt_d9
  have hp2 := Real.pi_lt_d6
  rw [archSymbol_zero_eq]
  linarith

/-- **A sharper lower bound for the archimedean constant**, from `γ`'s sandwich at sixteen. -/
theorem archSymbol_zero_lower : (-5.4032 : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 := by
  obtain ⟨hlp, hlp'⟩ := Cvs.Moments.log_pi_bounds
  have hg := gamma_lt_harmonic16
  have hl1 := Real.log_two_gt_d9
  have hp2 := Real.pi_lt_d6
  rw [archSymbol_zero_eq]
  linarith

/-- **The enclosure**, inherited from Mathlib's bounds on `γ`, `log 2` and `π`. -/
theorem archSymbol_zero_bounds :
    (-5.4618 : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      ∧ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ (-5.2948 : ℝ) := by
  obtain ⟨hlp, hlp'⟩ := Cvs.Moments.log_pi_bounds
  have hg1 := Real.one_half_lt_eulerMascheroniConstant
  have hg2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [archSymbol_zero_eq]
  constructor <;> linarith

/-- **The constant is the symbol read at the `N`-th pole.**  Truncating the density shifts the
digamma argument along its own poles. -/
theorem truncConst_eq_shifted (N : ℕ) :
    truncConst N = (Complex.digamma (Cvs.Zeta.digammaArg 0 N)).re - Real.log Real.pi := by
  have harg : Cvs.Zeta.digammaArg 0 N = (1 / 4 : ℂ) + (N : ℂ) := by
    simp [Cvs.Zeta.digammaArg]
  have hrec := Cvs.Zeta.digamma_add_nat (1 / 4 : ℂ) (by norm_num) N
  have hre : ∀ k ∈ Finset.range N,
      (((1 / 4 : ℂ) + (k : ℕ))⁻¹).re = 1 / ((k : ℝ) + 1 / 4) := by
    intro k _
    have : ((1 / 4 : ℂ) + (k : ℕ)) = (((k : ℝ) + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_inv, Complex.ofReal_re, inv_eq_one_div]
  rw [harg, hrec, Complex.add_re, Complex.re_sum, Finset.sum_congr rfl hre, truncConst]
  have h0 : Cvs.Zeta.digammaArg 0 0 = (1 / 4 : ℂ) := by simp [Cvs.Zeta.digammaArg]
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  rw [h0]
  ring

/-- **Four terms are enough.** -/
theorem truncConst_four_pos : 0 < truncConst 4 := by
  have h := archSymbol_zero_bounds.1
  simp only [truncConst, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  linarith

end Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
