import Mathlib
import Cvs.Zeta.DigammaGrowth
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiZeroCountBridge
import Cvs.Zeta.XiZetaBridge

/-!
# Off the real axis, the right half-plane constraint disappears

Two extensions, both replacing `0 < Re s` by `Im s ≠ 0`, and both needed so the Landau disc at
height `T` can be large enough to cross the critical strip.
-/

open Complex Real Finset

namespace Cvs.Zeta

theorem ne_neg_nat_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) : s ≠ -m := by
  intro hc
  exact hs (by rw [hc]; simp)

/-- The digamma recurrence, off the real axis rather than in the right half-plane. -/
theorem digamma_add_nat_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (n : ℕ) :
    Complex.digamma (s + n) = Complex.digamma s + ∑ k ∈ range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsn : (s + (n : ℂ)).im ≠ 0 := by simpa using hs
      rw [Nat.cast_succ, ← add_assoc,
        Complex.digamma_apply_add_one _ (ne_neg_nat_of_im_ne_zero hsn), ih,
        Finset.sum_range_succ, add_assoc]

/-- **`‖ψ‖ = O(log|Im x|)` on *any* vertical strip, off the real axis.**
`Cvs.Zeta.exists_norm_digamma_le` needs `Re x > 0`, because the Gauss series does. -/
theorem exists_norm_digamma_le_strip (a B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, a ≤ x.re → x.re ≤ B → 1 ≤ |x.im| →
      ‖Complex.digamma x‖ ≤ C * (1 + Real.log (2 + |x.im|)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 - a) (1 - B))
  have hna : 0 < a + n := by
    have := le_trans (le_max_left (1 - a) (1 - B)) hn.le
    linarith
  have hnB : 1 ≤ B + n := by
    have := le_trans (le_max_right (1 - a) (1 - B)) hn.le
    linarith
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_digamma_le (B + n) hnB
  refine ⟨C₀ + n, by positivity, fun x h1 h2 h3 => ?_⟩
  have him : x.im ≠ 0 := by intro h; rw [h] at h3; norm_num at h3
  have hlog0 : 0 ≤ Real.log (2 + |x.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg x.im])
  have hrec := digamma_add_nat_of_im_ne_zero him n
  have hshift : ‖Complex.digamma (x + n)‖ ≤ C₀ * (1 + Real.log (2 + |x.im|)) := by
    have hre : (x + (n : ℂ)).re = x.re + n := by simp
    have hi : (x + (n : ℂ)).im = x.im := by simp
    have := hC₀ (x + n) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [hi]; exact h3)
    rwa [hi] at this
  have hcorr : ‖∑ k ∈ range n, (x + (k : ℂ))⁻¹‖ ≤ (n : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ k ∈ range n, ‖(x + (k : ℂ))⁻¹‖ ≤ 1 := by
      intro k _
      rw [norm_inv, inv_le_one_iff₀]
      right
      exact le_trans h3 (abs_im_le_norm_add_nat x k)
    calc ∑ k ∈ range n, ‖(x + (k : ℂ))⁻¹‖ ≤ ∑ _k ∈ range n, (1 : ℝ) :=
          Finset.sum_le_sum hb
      _ = (n : ℝ) := by simp
  have hsplit : Complex.digamma x
      = Complex.digamma (x + n) - ∑ k ∈ range n, (x + (k : ℂ))⁻¹ := by
    rw [hrec]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  nlinarith [hshift, hcorr, hlog0, Nat.cast_nonneg (α := ℝ) n]

/-- **The `ξ`/`ζ` log-derivative bridge, off the real axis.** `Cvs.Zeta.logDeriv_riemannXi_eq_zeta`
requires `0 < Re s`, inherited from `Gammaℝ_ne_zero_of_re_pos`. -/
theorem logDeriv_riemannXi_eq_zeta_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s
      = 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have h0 : s ≠ 0 := ne_zero_of_im_ne_zero hs
  have h1 : s ≠ 1 := ne_one_of_im_ne_zero hs
  have hG : Gammaℝ s ≠ 0 := gammaR_ne_zero_of_im_ne_zero hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hev : riemannXi =ᶠ[nhds s]
      fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) / 2 := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with w hw
    exact riemannXi_eq_gammaR_mul_zeta (ne_zero_of_im_ne_zero hw)
      (ne_one_of_im_ne_zero hw) (gammaR_ne_zero_of_im_ne_zero hw)
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := differentiableAt_id.sub_const 1
  have hd3 : DifferentiableAt ℂ Gammaℝ s := differentiableAt_gammaR hG
  have hd4 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  have e1 : logDeriv (fun w : ℂ => w) s = 1 / s := by
    rw [logDeriv_apply, deriv_id'']
  have e2 : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  have hdiv : logDeriv (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w) / 2) s
      = logDeriv (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w)) s := by
    have hre : (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w) / 2)
        = fun w : ℂ => (w * (w - 1) * (Gammaℝ w * riemannZeta w)) * (2 : ℂ)⁻¹ := by
      funext w; ring
    rw [hre, logDeriv_mul_const s ((2 : ℂ)⁻¹) (by norm_num)]
  have m1 : logDeriv (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w)) s
      = logDeriv (fun w : ℂ => w * (w - 1)) s
        + logDeriv (fun w : ℂ => Gammaℝ w * riemannZeta w) s :=
    logDeriv_mul (f := fun w : ℂ => w * (w - 1))
      (g := fun w : ℂ => Gammaℝ w * riemannZeta w) s
      (mul_ne_zero h0 hsub) (mul_ne_zero hG hz) (hd1.fun_mul hd2) (hd3.fun_mul hd4)
  have m2 : logDeriv (fun w : ℂ => w * (w - 1)) s
      = logDeriv (fun w : ℂ => w) s + logDeriv (fun w : ℂ => w - 1) s :=
    logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s h0 hsub hd1 hd2
  have m3 : logDeriv (fun w : ℂ => Gammaℝ w * riemannZeta w) s
      = logDeriv Gammaℝ s + logDeriv riemannZeta s :=
    logDeriv_mul (f := Gammaℝ) (g := riemannZeta) s hG hz hd3 hd4
  rw [hdiv, m1, m2, m3, e1, e2]
  ring

end Cvs.Zeta
