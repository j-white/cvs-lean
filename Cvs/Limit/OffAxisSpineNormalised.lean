import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.RecentredTransformConj
import Cvs.Finite.RecentredTransformEven
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineEvenApproximants
import Cvs.Limit.OffAxisSpineFourValues
import Cvs.Limit.OffAxisWitnessSymmetry
import Cvs.Limit.ZeroFreeApproximantsRH

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-axis spine with no condition on the limit's shape

Normalising the recentred approximants by a real constant to modulus one at a single point off both
coordinate axes gives the limit modulus one there, hence a witness, and carries both the evenness
of `Cvs.Finite.RecentredTransformEven` and the conjugation of `Cvs.Finite.RecentredTransformConj` to the limit, so the spine asks nothing of the limit
beyond the convergence and the zeros it must see.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.OffAxisSpineNormalised
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit Cvs.Limit.ZeroFreeApproximantsRH

/-- **A locally uniform limit of a family of modulus one at a point has modulus one there.** -/
theorem norm_eq_one_of_tendsto {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ} {z₀ : ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop s) (hz₀ : z₀ ∈ s)
    (hnorm : ∀ n, ‖F n z₀‖ = 1) : ‖f z₀‖ = 1 := by
  have h := (hconv.tendsto_at hz₀).norm
  simp only [hnorm] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **A locally uniform limit of conjugate-symmetric functions is conjugate-symmetric**, on a set
closed under conjugation. -/
theorem eq_conj_of_tendsto {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop s)
    (hs : ∀ z ∈ s, (starRingEnd ℂ) z ∈ s)
    (hF : ∀ n, ∀ z ∈ s, F n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F n z))
    {z : ℂ} (hz : z ∈ s) :
    f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z) := by
  have h1 := hconv.tendsto_at (hs z hz)
  have h2 : Tendsto (fun n => (starRingEnd ℂ) (F n z)) atTop (𝓝 ((starRingEnd ℂ) (f z))) :=
    (Complex.continuous_conj.tendsto _).comp (hconv.tendsto_at hz)
  have heq : (fun n => F n ((starRingEnd ℂ) z)) = fun n => (starRingEnd ℂ) (F n z) :=
    funext fun n => hF n z hz
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The off-axis spine, asking nothing of the limit but the convergence and the zeros it sees.** -/
theorem riemannHypothesis_of_ground_centred_offAxes_real_normalised
    {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) (c : ℕ → ℂ) (f : ℂ → ℂ) {w₀ : ℂ}
    (hw₀ : w₀ ∈ offAxes) (hcreal : ∀ n, (c n).im = 0)
    (hnorm : ∀ n,
      ‖c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) w₀‖ = 1)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z)
      f atTop offAxes)
    (hsees : ∀ z ∈ offAxes, Xi z = 0 → f z = 0) :
    RiemannHypothesis := by
  -- the constants are non-zero, or the normalisation would read `0 = 1`
  have hc : ∀ n, c n ≠ 0 := by
    intro n hcn
    have h := hnorm n
    rw [hcn, zero_mul, norm_zero] at h
    exact zero_ne_one h
  -- the limit has modulus one at `w₀`, so it does not vanish there
  have hnf : ‖f w₀‖ = 1 := norm_eq_one_of_tendsto hconv hw₀ hnorm
  have hfw₀ : f w₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnf
    exact zero_ne_one hnf
  -- evenness passes to the limit: the constant cancels on both sides
  have heven : ∀ z ∈ offAxes, f (-z) = f z := fun _z hz =>
    Cvs.Limit.OffAxisSpineEvenApproximants.eq_neg_of_tendsto hconv
      (fun _ h => Cvs.Limit.OffAxisWitnessSymmetry.neg_mem_offAxes h)
      (fun n _y hy => by
        rw [Cvs.Finite.RecentredTransformEven.cgtransform_neg (P n) (R n) (hL n) (N n) hy]) hz
  -- conjugation passes to the limit because the constants are real
  have hconj : ∀ z ∈ offAxes,
      f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z) := fun _z hz =>
    eq_conj_of_tendsto hconv (fun _ h => Cvs.Limit.OffAxisWitnessSymmetry.conj_mem_offAxes h)
      (fun n _y hy => by
        rw [Cvs.Finite.RecentredTransformConj.cgtransform_conj (P n) (R n) (hL n) (N n) hy, map_mul,
          Complex.conj_eq_iff_im.mpr (hcreal n)]) hz
  exact Cvs.Limit.OffAxisSpineFourValues.riemannHypothesis_of_ground_centred_offAxes_quadrants
    hL P R N c hc f hconv
    (fun _ _ hs ht => Cvs.Limit.OffAxisWitnessSymmetry.exists_quad_of_symm heven hconj hw₀ hfw₀ hs ht) hsees

end Cvs.Limit.OffAxisSpineNormalised
