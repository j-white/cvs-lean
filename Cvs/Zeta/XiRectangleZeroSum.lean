import Mathlib
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectWinding
import Cvs.Zeta.RectXi
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip

/-!
# The zero sum on the rung-7 rectangle

`rect_argument_principle_riemannXi` takes an abstract open `U` and a hypothesis saying every
zero of `ξ` in it is strictly inside the rectangle.
-/

open Complex Set

namespace Cvs.Zeta

/-- **The zero sum on the rung-7 rectangle.** -/
theorem rect_zero_sum_of_collar {T' δ : ℝ} (hT'0 : 0 ≤ T') (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : ∀ u : ℂ, riemannXi u = 0 → |u.im| < T' ∨ T' + δ ≤ |u.im|)
    {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, riemannXi ρ = 0) ∧
      (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
      (∀ u : ℂ, riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
      (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
      rectBoundaryIntegral (fun u => logDeriv riemannXi u * φ u)
          (-1 - (T' : ℂ) * I) (2 + (T' : ℂ) * I)
        = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ := by
  set U : Set ℂ := Ioo (-1 - δ) (2 + δ) ×ℂ Ioo (-T' - δ) (T' + δ) with hUdef
  have hzre : (-1 - (T' : ℂ) * I).re = -1 := by simp
  have hzim : (-1 - (T' : ℂ) * I).im = -T' := by simp
  have hwre : ((2 : ℂ) + (T' : ℂ) * I).re = 2 := by simp
  have hwim : ((2 : ℂ) + (T' : ℂ) * I).im = T' := by simp
  have hUo : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have hU : closedRect (-1 - (T' : ℂ) * I) ((2 : ℂ) + (T' : ℂ) * I) ⊆ U := by
    intro u hu
    rw [closedRect, hzre, hzim, hwre, hwim, Complex.mem_reProdIm] at hu
    rw [hUdef, Complex.mem_reProdIm]
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hu
    rw [Set.uIcc_of_le (by linarith : -T' ≤ T')] at hu
    exact ⟨⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩,
      ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩⟩
  have hUr : U ⊆ Metric.closedBall (0 : ℂ) (T' + 4) := by
    intro u hu
    rw [hUdef, Complex.mem_reProdIm] at hu
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hu
    have hn := Complex.norm_le_abs_re_add_abs_im u
    have hre : |u.re| ≤ 2 + δ := by rw [abs_le]; constructor <;> linarith
    have him : |u.im| ≤ T' + δ := by rw [abs_le]; constructor <;> linarith
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hzU : ∀ u ∈ U, riemannXi u = 0 →
      (-1 - (T' : ℂ) * I).re < u.re ∧ u.re < ((2 : ℂ) + (T' : ℂ) * I).re ∧
      (-1 - (T' : ℂ) * I).im < u.im ∧ u.im < ((2 : ℂ) + (T' : ℂ) * I).im := by
    intro u hu h0
    rw [hUdef, Complex.mem_reProdIm] at hu
    obtain ⟨-, ⟨h3, h4⟩⟩ := hu
    obtain ⟨hr1, hr2⟩ := riemannXi_zero_re_mem h0
    have him : |u.im| < T' := by
      rcases hgap u h0 with h | h
      · exact h
      · exfalso
        have : |u.im| < T' + δ := by rw [abs_lt]; constructor <;> linarith
        linarith
    rw [abs_lt] at him
    rw [hzre, hzim, hwre, hwim]
    exact ⟨hr1, hr2, him.1, him.2⟩
  obtain ⟨S, m, hS0, hSin, hScap, hSmult, heq⟩ :=
    rect_argument_principle_riemannXi (T' + 4) hUo hU hUr hzU hφ.differentiableOn
  refine ⟨S, m, hS0, ?_, ?_, hSmult, heq⟩
  · intro ρ hρ
    have := hSin ρ hρ
    rw [hzre, hzim, hwre, hwim] at this
    exact this
  · intro u h0 him
    refine hScap u ?_ h0
    rw [hUdef, Complex.mem_reProdIm]
    obtain ⟨hr1, hr2⟩ := riemannXi_zero_re_mem h0
    rw [abs_lt] at him
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [him.1], by linarith [him.2]⟩⟩

end Cvs.Zeta
