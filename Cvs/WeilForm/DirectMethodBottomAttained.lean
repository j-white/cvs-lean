import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowFormLowerSemicontinuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The direct method: the bottom of the window's Weil form is attained

    D sequentially compact in L²  ⟹  the infimum of `weilForm` over `D` is a minimum

A minimising sequence has a subsequence converging in `L²` to a member of `D`, and `Cvs.WeilForm.WindowFormLowerSemicontinuous`
says the form cannot jump up in the limit.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.DirectMethodBottomAttained

/-- **The infimum is attained.** -/
theorem exists_minimiser {D : Set (ℝ → ℝ)} (P R : ℕ) {L lam : ℝ}
    (hmemD : ∀ f ∈ D, MemLp f 2 (volume : Measure ℝ))
    (hsuppD : ∀ f ∈ D, ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hcontD : ∀ f ∈ D, AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ))
    (hintD : ∀ f ∈ D, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0)
      (volume : Measure ℝ))
    (hnormD : ∀ f ∈ D, (∫ x : ℝ, f x ^ 2) = 1)
    (hlam : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R '' D) lam)
    (hcpt : ∀ (F : ℕ → ℝ → ℝ) (B : ℝ), (∀ n, F n ∈ D) →
      (∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ B) →
      ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ g ∈ D ∧
        Tendsto (fun k => ∫ x : ℝ, (F (φ k) x - g x) ^ 2) atTop (nhds 0)) :
    ∃ g ∈ D, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam := by
  classical
  -- a minimising sequence
  have hchoice : ∀ n : ℕ, ∃ f, f ∈ D ∧
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f < lam + 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra hcon
    push_neg at hcon
    have hlb : lam + 1 / ((n : ℝ) + 1) ∈ lowerBounds
        (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R '' D) := by
      rintro y ⟨f, hf, rfl⟩
      exact hcon f hf
    have hle : lam + 1 / ((n : ℝ) + 1) ≤ lam := hlam.2 hlb
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose F hFD hFlt using hchoice
  have hFB : ∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ lam + 1 := by
    intro n
    have h1 : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith [hFlt n]
  obtain ⟨φ, g, hφ, hgD, htend⟩ := hcpt F (lam + 1) hFD hFB
  refine ⟨g, hgD, le_antisymm ?_ (hlam.1 ⟨g, hgD, rfl⟩)⟩
  by_contra hcon
  push_neg at hcon
  set ε : ℝ := (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g - lam) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- lower semicontinuity along the subsequence
  have hlsc := Cvs.WeilForm.WindowFormLowerSemicontinuous.weilForm_le_eventually (L := L) (C := 1) P R
    (hmemD g hgD) (fun k => hmemD _ (hFD (φ k))) (hsuppD g hgD)
    (fun k => hsuppD _ (hFD (φ k))) (hcontD g hgD) (fun k => hcontD _ (hFD (φ k)))
    (hintD g hgD) (fun k => hintD _ (hFD (φ k))) htend
    (fun k => le_of_eq (hnormD _ (hFD (φ k)))) hε
  -- the minimising bound eventually beats ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  have htail : ∀ᶠ k in atTop, 1 / ((φ k : ℝ) + 1) < ε := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkφ : N ≤ φ k := le_trans hk hφ.le_apply
    refine lt_of_le_of_lt ?_ hN
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.succ_le_succ hkφ
  obtain ⟨k, hk1, hk2⟩ := (hlsc.and htail).exists
  have hlt := hFlt (φ k)
  linarith

end Cvs.WeilForm.DirectMethodBottomAttained
