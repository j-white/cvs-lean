import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip

/-!
# The `ζ`-ordinate gap already supplies the `ξ` collar

The limit needs a *single* height `T'` satisfying two conditions at once:
`exists_zero_free_height'` wants it far from the ordinates of `ζ` zeros in a ball about `2 +
iT`, and `rect_zero_sum_of_collar` wants no `ξ` ordinate in `[T', T' + δ)`.
-/

open Complex Metric

namespace Cvs.Zeta

/-- The zeros of `ξ` are symmetric under conjugation.  Routed through `ζ`, since
`riemannZeta_conj` is what Mathlib provides; legitimate because every zero of `ξ` has
`0 < Re` (`Cvs.Zeta.XiStrip`), where the two functions vanish together. -/
theorem riemannXi_conj_zero {s : ℂ} (h : riemannXi s = 0) :
    riemannXi ((starRingEnd ℂ) s) = 0 := by
  obtain ⟨hre0, hre1⟩ := riemannXi_zero_mem_strip h
  have hs1 : s ≠ 1 := by intro hc; rw [hc] at hre1; simp at hre1
  have hζ : riemannZeta s = 0 := (riemannXi_eq_zero_iff_riemannZeta hre0 hs1).mp h
  have hcre : ((starRingEnd ℂ) s).re = s.re := by simp
  have hc1 : (starRingEnd ℂ) s ≠ 1 := by
    intro hc
    apply hs1
    have := congrArg (starRingEnd ℂ) hc
    simpa using this
  refine (riemannXi_eq_zero_iff_riemannZeta (by rw [hcre]; exact hre0) hc1).mpr ?_
  rw [riemannZeta_conj, hζ]
  simp

/-- **The `ζ`-ordinate gap already supplies the `ξ` collar.** `exists_zero_free_height'` places
`T'` far from the ordinates of the `ζ` zeros in a ball about `2 + iT`;
`exists_zero_free_ordinate` places it outside a collar of `ξ` ordinates. -/
theorem collar_of_zeta_gap {T T' gap r : ℝ} (hT : 3 ≤ T) (hgap1 : gap ≤ 1)
    (h1 : T ≤ T') (h2 : T' ≤ T + 1) (hr : 4 ≤ r)
    (hfree : ∀ z : ℂ, z ∈ closedBall (2 + (T : ℂ) * I) r → riemannZeta z = 0 →
      gap ≤ |T' - z.im|) :
    ∀ u : ℂ, riemannXi u = 0 → |u.im| < T' ∨ T' + gap ≤ |u.im| := by
  intro u h0
  by_contra hc
  obtain ⟨hlt, hge⟩ := not_or.mp hc
  -- `|Im u|` lies in `[T', T' + gap)`
  have hb1 : T' ≤ |u.im| := not_lt.mp hlt
  have hb2 : |u.im| < T' + gap := not_le.mp hge
  obtain ⟨hre0, hre1⟩ := riemannXi_zero_mem_strip h0
  -- move to the upper half-plane
  set v : ℂ := if 0 ≤ u.im then u else (starRingEnd ℂ) u with hv
  have hvzero : riemannXi v = 0 := by
    rw [hv]; split_ifs with h
    · exact h0
    · exact riemannXi_conj_zero h0
  have hvre : v.re = u.re := by rw [hv]; split_ifs <;> simp
  have hvim : v.im = |u.im| := by
    rw [hv]; split_ifs with h
    · rw [abs_of_nonneg h]
    · simp; rw [abs_of_neg (not_le.mp h)]
  -- `v` lies in the ball
  have hmem : v ∈ closedBall (2 + (T : ℂ) * I) r := by
    have hw : (v - (2 + (T : ℂ) * I)).re = v.re - 2 := by simp
    have hwi : (v - (2 + (T : ℂ) * I)).im = v.im - T := by simp
    have hn := Complex.norm_le_abs_re_add_abs_im (v - (2 + (T : ℂ) * I))
    rw [hw, hwi] at hn
    have ha : |v.re - 2| ≤ 2 := by
      rw [hvre, abs_le]; constructor <;> linarith
    have hb : |v.im - T| ≤ 2 := by
      rw [hvim, abs_le]; constructor <;> linarith
    simp only [mem_closedBall, dist_eq_norm]
    linarith
  -- and is a zero of `ζ`
  have hv1 : v ≠ 1 := by
    intro hcon
    have : v.im = 0 := by rw [hcon]; simp
    rw [hvim] at this
    linarith
  have hvre0 : 0 < v.re := by rw [hvre]; exact hre0
  have hζ : riemannZeta v = 0 := (riemannXi_eq_zero_iff_riemannZeta hvre0 hv1).mp hvzero
  have := hfree v hmem hζ
  rw [hvim, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ |u.im| - T')] at this
  linarith

end Cvs.Zeta
