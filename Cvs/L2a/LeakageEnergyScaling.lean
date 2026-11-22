import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Upstream.SmallAdmixtureMassBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The leakage energy beyond `kx` is at most `K/k` of the energy beyond `x`

`arcsin y ≤ (π/2) y` on `[0, 1]` turns `SmallAdmixtureMassBounds`'s tail ratio into `R(Y) ≤ C/Y`, and summing the Poisson modes
`Σ_{m ≤ M} (1/m) ∫_{mk}^Z ĝ²` against `Σ 1/m² ≤ π²/6` gives `K/k` times `∫_{ξ₀}^Z ĝ²`: the hypothesis of
`PrimeResonanceSum`'s resonance bound, with `K` explicit in `c`, `χ`, `ξ₀`, `Z` and the admixture `ε`.
-/

namespace Cvs.L2a.LeakageEnergyScaling

open intervalIntegral Real Set Finset Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-- `arcsin y ≤ (π/2) y` for `0 ≤ y ≤ 1`. -/
theorem arcsin_le_pi_div_two_mul {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : arcsin y ≤ π / 2 * y := by
  have hπ := pi_pos
  have hy : π / 2 * y ≤ π / 2 := by nlinarith
  rw [arcsin_le_iff_le_sin ⟨by linarith, h1⟩ ⟨by nlinarith, hy⟩]
  have := mul_le_sin (by positivity : 0 ≤ π / 2 * y) hy
  have e : 2 / π * (π / 2 * y) = y := by field_simp
  linarith

/-- The constant of the `1/Y` law. -/
noncomputable def lawC (c χ ξ₀ Z : ℝ) : ℝ :=
  fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
    - fac c χ ξ₀ / (2 * qP c χ ξ₀)) * (π / (4 * √(c ^ 2 - χ)) + 1 / (2 * (c ^ 2 - χ)))

/-- **`R(Y) ≤ C/Y`.** For `1 ≤ Y`, the rate of Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay is at most `lawC/Y`. -/
theorem rate_le {c χ ξ₀ Z Y : ℝ} (hY : 1 ≤ Y) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hpre : 0 ≤ fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
      - fac c χ ξ₀ / (2 * qP c χ ξ₀))) :
    fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
      - fac c χ ξ₀ / (2 * qP c χ ξ₀)) * (arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) + 1 / (2 * qP c χ Y))
      ≤ lawC c χ ξ₀ Z / Y := by
  have hd := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.sub_pos' hχc
  have hs : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hY0 : 0 < Y := by linarith
  have hyi : 0 ≤ 1 / Y := by positivity
  have hyi1 : 1 / Y ≤ 1 := by rw [div_le_one hY0]; exact hY
  have ha := arcsin_le_pi_div_two_mul hyi hyi1
  have hq : (c ^ 2 - χ) * Y ^ 2 ≤ qP c χ Y := by
    unfold qP; nlinarith [mul_nonneg hχ (by nlinarith : (0:ℝ) ≤ Y ^ 2 - 1)]
  have hq' : (c ^ 2 - χ) * Y ≤ qP c χ Y := by
    have : Y ≤ Y ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hd.le]
  have h1 : arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) ≤ π / (4 * √(c ^ 2 - χ)) / Y := by
    rw [div_le_iff₀ (by positivity)]
    calc arcsin (1 / Y) ≤ π / 2 * (1 / Y) := ha
      _ = π / (4 * √(c ^ 2 - χ)) / Y * (2 * √(c ^ 2 - χ)) := by field_simp; ring
  have h2 : 1 / (2 * qP c χ Y) ≤ 1 / (2 * (c ^ 2 - χ)) / Y := by
    have hq0 : 0 < qP c χ Y := lt_of_lt_of_le (mul_pos hd hY0) hq'
    rw [div_div, one_div_le_one_div (by positivity) (mul_pos (mul_pos two_pos hd) hY0)]
    nlinarith
  unfold lawC
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hpre
  rw [add_div]
  linarith

/-- **The mode sum.** If each tail `T m` (the energy beyond `mk`) is at most `(C/(mk)) T₀`, with
`C, T₀ ≥ 0` and `k > 0`, then `Σ_{m=1}^{M} T m / m ≤ (C π²/6 / k) T₀`. -/
theorem mode_sum_le {T : ℕ → ℝ} {C T₀ k : ℝ} (hC : 0 ≤ C) (hT₀ : 0 ≤ T₀) (hk : 0 < k) (M : ℕ)
    (hT : ∀ m ∈ Finset.Icc 1 M, T m ≤ C / ((m : ℝ) * k) * T₀) :
    ∑ m ∈ Finset.Icc 1 M, T m / m ≤ C * (π ^ 2 / 6) / k * T₀ := by
  have hterm : ∀ m ∈ Finset.Icc 1 M, T m / m ≤ C * T₀ / k * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by linarith
    rw [div_le_iff₀ hm0]
    calc T m ≤ C / ((m : ℝ) * k) * T₀ := hT m hm
      _ = C * T₀ / k * (1 / (m : ℝ) ^ 2) * m := by field_simp
  have hsum : ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ) ^ 2) ≤ π ^ 2 / 6 := by
    have h := hasSum_zeta_two
    calc ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ) ^ 2) ≤ ∑ m ∈ Finset.range (M + 1), (1 / (m : ℝ) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; simp [Finset.mem_Icc] at hm; simp; omega
          · intro _ _ _; positivity
      _ ≤ π ^ 2 / 6 := sum_le_hasSum _ (fun _ _ => by positivity) h
  calc ∑ m ∈ Finset.Icc 1 M, T m / m ≤ ∑ m ∈ Finset.Icc 1 M, C * T₀ / k * (1 / (m : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = C * T₀ / k * ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ C * T₀ / k * (π ^ 2 / 6) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * (π ^ 2 / 6) / k * T₀ := by ring

/-- **The resonance input for `ĝ`.** For `ĝ = ψ − κφ` with `ψ` a prolate solution on `[ξ₀, Z]`,
`ξ₀ ≤ k`, `1 ≤ M`, `M k ≤ Z` and the admixture at most `ε < 1` on `[ξ₀, Z]` and every `[mk, Z]`,
`Σ_{m=1}^{M} (1/m) ∫_{mk}^Z ĝ² ≤ ((1+ε)/(1−ε))² lawC (π²/6)/k · ∫_{ξ₀}^Z ĝ²`. -/
theorem ghat_mode_sum {c χ κ ε k : ℝ} {ψ u φ : ℝ → ℝ} {ξ₀ Z : ℝ} (M : ℕ) (hM : 1 ≤ M) (h1 : 1 < ξ₀)
    (hk : ξ₀ ≤ k) (hMZ : (M : ℝ) * k ≤ Z) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ Z, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ Z, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2)
    (hL : 0 < (arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
      - fac c χ ξ₀ / (2 * qP c χ ξ₀))
    (hφ : ContinuousOn φ (Icc ξ₀ Z)) (hε : 0 < ε) (hε1 : ε < 1)
    (hmix : ∀ m ∈ Finset.Icc 1 M, ∫ t in (m * k)..Z, (κ * φ t) ^ 2
      ≤ ε ^ 2 * ∫ t in (m * k)..Z, ψ t ^ 2)
    (hmix0 : ∫ t in ξ₀..Z, (κ * φ t) ^ 2 ≤ ε ^ 2 * ∫ t in ξ₀..Z, ψ t ^ 2) :
    ∑ m ∈ Finset.Icc 1 M, (∫ t in (m * k)..Z, (ψ t - κ * φ t) ^ 2) / m
      ≤ ((1 + ε) / (1 - ε)) ^ 2 * lawC c χ ξ₀ Z * (π ^ 2 / 6) / k
        * ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hk0 : 0 < k := by linarith
  have hle : ξ₀ ≤ Z := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hF : 0 < fac c χ ξ₀ := by
    have hW0 := wP_pos h1 hc2 hχc
    unfold fac; exact mul_pos (div_pos (by linarith) (by linarith)) (exp_pos _)
  have hpre : 0 ≤ fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
      - fac c χ ξ₀ / (2 * qP c χ ξ₀)) := div_nonneg hF.le hL.le
  have hC : 0 ≤ ((1 + ε) / (1 - ε)) ^ 2 * lawC c χ ξ₀ Z := by
    have hd := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.sub_pos' hχc
    unfold lawC; positivity
  have hT0 : 0 ≤ ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2 := integral_nonneg hle fun _ _ => sq_nonneg _
  have key := mode_sum_le (T := fun m : ℕ => ∫ t in (m * k)..Z, (ψ t - κ * φ t) ^ 2)
    (C := ((1 + ε) / (1 - ε)) ^ 2 * lawC c χ ξ₀ Z) hC hT0 hk0 M (fun m hm => by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have hY : ξ₀ ≤ m * k := by nlinarith
      have hYZ : (m : ℝ) * k ≤ Z := le_trans (by nlinarith) hMZ
      have tr := Cvs.Upstream.SmallAdmixtureMassBounds.ghat_tail_ratio h1 hY hYZ hc hχ hχc hψ hu hW hL hφ hε hε1
        (hmix m hm) hmix0
      have hr := rate_le (Y := m * k) (by nlinarith) hc hχ hχc hpre
      refine tr.trans ?_
      have hsq : 0 ≤ ((1 + ε) / (1 - ε)) ^ 2 := sq_nonneg _
      calc ((1 + ε) / (1 - ε)) ^ 2 * (fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀))
            / (2 * c * fac c χ ξ₀) - fac c χ ξ₀ / (2 * qP c χ ξ₀))
            * (arcsin (1 / (m * k)) / (2 * √(c ^ 2 - χ)) + 1 / (2 * qP c χ (m * k))))
            * ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2
          ≤ ((1 + ε) / (1 - ε)) ^ 2 * (lawC c χ ξ₀ Z / (m * k)) * ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2 := by
            gcongr
        _ = ((1 + ε) / (1 - ε)) ^ 2 * lawC c χ ξ₀ Z / (m * k) * ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2 := by
            ring)
  simpa [mul_comm, mul_left_comm, mul_assoc] using key

end Cvs.L2a.LeakageEnergyScaling
