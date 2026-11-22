import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The channel cap by duality, without second derivatives

    Q g = ⟨f, g⟩,   (1/λ)‖g‖² ≤ Q g,   ⟨g, f⟩ ≤ ‖g‖‖f‖   ⟹   ⟨g, f⟩ ≤ λ‖f‖²

so the cap needs the weak identity, the Robin–Poincaré bound and Cauchy–Schwarz, and nothing
of second order.
-/

noncomputable section

namespace Cvs.WeilForm.ChannelCapByDuality

/-- **The cap, by duality.**  `ng = ‖g‖`, `nf = ‖f‖`, `pair = ⟨g, f⟩`, `Qg` the Robin form at
`g`.  The Poincaré bound on `Qg` forces `‖g‖ ≤ λ‖f‖`, and Cauchy–Schwarz then caps the pairing;
no second derivative appears anywhere. -/
theorem cap_of_dual {lam ng nf pair Qg : ℝ} (hlam : 0 < lam)
    (hweak : Qg = pair)
    (hP : ng ^ 2 / lam ≤ Qg)
    (hCS : pair ≤ ng * nf)
    (hng : 0 ≤ ng) (hnf : 0 ≤ nf) :
    pair ≤ lam * nf ^ 2 := by
  rw [hweak] at hP
  have hstep : ng ^ 2 / lam ≤ ng * nf := le_trans hP hCS
  have hng2 : ng ^ 2 ≤ lam * (ng * nf) := by
    rw [div_le_iff₀ hlam] at hstep
    nlinarith [hstep]
  rcases eq_or_lt_of_le hng with h0 | hpos
  · have : pair ≤ 0 := by
      refine le_trans hCS ?_
      rw [← h0]; simp
    nlinarith [this, sq_nonneg nf, hlam.le]
  · have hle : ng ≤ lam * nf := by
      have := hng2
      nlinarith [hpos]
    calc pair ≤ ng * nf := hCS
      _ ≤ (lam * nf) * nf := by nlinarith [hnf]
      _ = lam * nf ^ 2 := by ring

end Cvs.WeilForm.ChannelCapByDuality
