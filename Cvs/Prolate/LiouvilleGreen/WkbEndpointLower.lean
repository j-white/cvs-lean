import Mathlib
import Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent
import Cvs.Prolate.LiouvilleGreen.TurningPointLayer
import Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB lower bound on the endpoint value

For a positive solution of the angular equation on `[m, 1]`, `0 ≤ m ≤ s₀ = √χ/c`, `3χ ≤ c²`, `0 < ε ≤ s₀` and
`s₁ = s₀ + η ≤ s_m`: `g(1) ≥ g(m)(ε/s₀)^{1/p(s₀)}e^{−K(ε+η)/p(s₁)}e^{cΦ₂(s₀)}(pq(s₁)/pq(s_m))^{1/4}`,
`K = √(pq)(s₁) + γ(s₁) + q(s₁)η`; with the peak lemma, `g(1)²` is at least half the square of the rest.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.LiouvilleGreen.WkbEndpointLower

open Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier (pp qq Bb gam gamD)
open Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent (U)
open Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint (sm mem_uIcc)

/-- The layer constant `K = √(pq)(s₁) + γ(s₁) + q(s₁)η` at `s₁ = s₀ + η`. -/
def Kl (c χ η : ℝ) : ℝ :=
  Bb c χ (√χ / c + η) + gam c χ (√χ / c + η) + qq c χ (√χ / c + η) * η

set_option maxHeartbeats 1000000 in
/-- **The peak through the turning layer**: `g(m)(ε/s₀)^{1/p(s₀)}e^{−K(ε+η)/p(s₁)} ≤ g(s₁)`, `s₁ = s₀ + η`, for
`g > 0` on `[m, 1]`. -/
theorem layer_ge {g g₁ g₂ : ℝ → ℝ} {c χ m ε η : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 < χ) (h3 : 3 * χ ≤ c ^ 2) (hm0 : 0 ≤ m) (hmT : m ≤ √χ / c)
    (hε : 0 < ε) (hεT : ε ≤ √χ / c) (hη : 0 < η) (hηm : √χ / c + η ≤ sm c χ)
    (hpos : ∀ s ∈ Icc m 1, 0 < g s) :
    g m * exp ((log ε - log (√χ / c)) / pp (√χ / c)) * exp (-(Kl c χ η * (ε + η) / pp (√χ / c + η)))
      ≤ g (√χ / c + η) := by
  have hχc : χ < c ^ 2 := by linarith
  have hsm1 := Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_lt_one hc hχ hχc
  set T := √χ / c with hTd
  have hT0 : 0 < T := by positivity
  set s₁ := T + η with hs₁d
  have hTs₁ : T < s₁ := by linarith
  have hs₁1 : s₁ < 1 := lt_of_le_of_lt hηm hsm1
  have hT1 : T < 1 := hTs₁.trans hs₁1
  have hTsq : c ^ 2 * T ^ 2 = χ := by rw [hTd, div_pow, Real.sq_sqrt hχ.le]; field_simp
  have hpos' : ∀ s ∈ Icc s₁ 1, 0 < g s := fun s hs => hpos s ⟨(hmT.trans hTs₁.le).trans hs.1, hs.2⟩
  -- `U` on `[m, s₁]`
  have hUc : ContinuousOn (U g g₁) (Icc m s₁) :=
    Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.continuousOn_U hm0 hs₁1.le hg hg₁ fun s hs => (hpos s ⟨hs.1, hs.2.trans hs₁1.le⟩).ne'
  have hUd : ∀ x ∈ Ioo m s₁, HasDerivAt (U g g₁) (U g g₁ x ^ 2 / (1 - x ^ 2) - (c ^ 2 * x ^ 2 - χ)) x := by
    intro x hx
    have hm := mem_uIcc (hm0.trans hx.1.le) (hx.2.le.trans hs₁1.le)
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2, hs₁1]
    exact Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.hasDerivAt_U (hg x hm) (hg₁ x hm) (hang x hm) hx2
      (hpos x ⟨hx.1.le, hx.2.le.trans hs₁1.le⟩).ne'
  have hq_le : ∀ x, 0 ≤ x → x ≤ T → c ^ 2 * x ^ 2 - χ ≤ 0 := fun x h0 h1 => by
    have : x ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ h0 h1 2
    nlinarith
  have hUsq : ∀ x ∈ Ioo m T, U g g₁ x ^ 2 ≤ U g g₁ x ^ 2 / (1 - x ^ 2) - (c ^ 2 * x ^ 2 - χ) := by
    intro x hx
    have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, hT1]
    have hp1 : 1 - x ^ 2 ≤ 1 := by nlinarith
    have h1 : U g g₁ x ^ 2 ≤ U g g₁ x ^ 2 / (1 - x ^ 2) := by
      rw [le_div_iff₀ hp]; nlinarith [sq_nonneg (U g g₁ x)]
    linarith [hq_le x (hm0.trans hx.1.le) hx.2.le]
  -- `U ≤ K` on `[m, s₁]`
  have hUs₁ : U g g₁ s₁ ≤ Bb c χ s₁ + gam c χ s₁ :=
    Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.U_le_W hg hg₁ hang hc hχ h3 (by linarith) hηm hpos' s₁ ⟨le_rfl, hηm⟩
  have hqs₁ : 0 ≤ qq c χ s₁ := by
    unfold qq; have : T ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ hT0.le hTs₁.le 2; nlinarith
  have hlin := Cvs.Prolate.LiouvilleGreen.TurningPointLayer.le_add_mul (U := U g g₁) (k := qq c χ s₁) (hUc.mono (Icc_subset_Icc_left hmT))
    (fun x hx => hUd x ⟨lt_of_le_of_lt hmT hx.1, hx.2⟩) (fun x hx => by
      have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, hs₁1, hT0]
      have h1 : 0 ≤ U g g₁ x ^ 2 / (1 - x ^ 2) := div_nonneg (sq_nonneg _) hp.le
      have h2 : c ^ 2 * x ^ 2 - χ ≤ qq c χ s₁ := by
        unfold qq; have : x ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ (hT0.le.trans hx.1.le) hx.2.le 2; nlinarith
      linarith)
  have hmonoU : MonotoneOn (U g g₁) (Icc m T) := by
    rcases eq_or_lt_of_le hmT with he | hlt
    · rw [he, Icc_self]; exact (Set.subsingleton_singleton).monotoneOn _
    refine monotoneOn_of_deriv_nonneg (convex_Icc m T) (hUc.mono (Icc_subset_Icc_right hTs₁.le)) ?_ ?_
    · intro x hx; rw [interior_Icc] at hx
      exact (hUd x ⟨hx.1, hx.2.trans hTs₁⟩).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hUd x ⟨hx.1, hx.2.trans hTs₁⟩).deriv]
      exact le_trans (sq_nonneg _) (hUsq x hx)
  have hUK : ∀ x ∈ Icc m s₁, U g g₁ x ≤ Kl c χ η := by
    intro x hx
    have hK : U g g₁ T ≤ Kl c χ η := by
      have := hlin T ⟨le_rfl, hTs₁.le⟩
      unfold Kl; rw [← hTd]
      have hη' : s₁ - T = η := by ring
      rw [hη'] at this; linarith
    rcases le_or_gt x T with hxT | hxT
    · exact (hmonoU ⟨hx.1, hxT⟩ ⟨hmT, le_rfl⟩ hxT).trans hK
    · have := hlin x ⟨hxT.le, hx.2⟩
      unfold Kl; rw [← hTd]
      have : qq c χ s₁ * (s₁ - x) ≤ qq c χ s₁ * η :=
        mul_le_mul_of_nonneg_left (by linarith) hqs₁
      linarith [hlin x ⟨hxT.le, hx.2⟩]
  have hK0 : 0 ≤ Kl c χ η := by
    have hq1 : 0 < qq c χ s₁ := by
      unfold qq; have : T ^ 2 < s₁ ^ 2 := pow_lt_pow_left₀ hTs₁ hT0.le two_ne_zero; nlinarith
    have hγ : 0 ≤ gam c χ s₁ := by
      refine Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.gam_nonneg hq1 (hT0.trans hTs₁) ?_
      have h1 : s₁ ^ 2 ≤ sm c χ ^ 2 := pow_le_pow_left₀ (hT0.trans hTs₁).le hηm 2
      rw [Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_sq hc hχ, le_div_iff₀ (by positivity)] at h1; nlinarith
    unfold Kl; rw [← hTd]
    have := Real.sqrt_nonneg (pp s₁ * qq c χ s₁)
    unfold Bb; positivity
  -- generic facts for the steps
  have hgc : ∀ a b, 0 ≤ a → b ≤ 1 → ContinuousOn g (Icc a b) := fun a b ha hb x hx =>
    (hg x (mem_uIcc (ha.trans hx.1) (hx.2.trans hb))).continuousAt.continuousWithinAt
  have hg₁U : ∀ x, x ^ 2 < 1 → g x ≠ 0 → g₁ x = -(U g g₁ x * g x) / pp x := fun x hx hgx =>
    Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.g₁_eq hgx (by linarith)
  have hpT : 0 < pp T := by unfold pp; nlinarith
  have hps₁ : 0 < pp s₁ := by unfold pp; nlinarith [hT0]
  -- the bound at `s₁`
  have hfac1 : exp ((log ε - log T) / pp T) ≤ 1 := by
    rw [exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [log_le_log hε hεT]) hpT.le
  have hstep : g m * exp ((log ε - log T) / pp T) * exp (-(Kl c χ η * (ε + η) / pp s₁)) ≤ g s₁ := by
    have hlay : ∀ a, m ≤ a → T - ε ≤ a → a ≤ s₁ → g a * exp (-(Kl c χ η * (ε + η) / pp s₁)) ≤ g s₁ := by
      intro a hma hTa has₁
      have h := Cvs.Prolate.LiouvilleGreen.TurningPointLayer.step_layer (U := U g g₁) (p := pp) (g₁ := g₁) has₁ hK0 hps₁
        (hgc a s₁ (hm0.trans hma) hs₁1.le) (fun x hx => hg x (mem_uIcc (hm0.trans (hma.trans hx.1.le))
          (hx.2.le.trans hs₁1.le)))
        (fun x hx => hpos x ⟨hma.trans hx.1.le, hx.2.le.trans hs₁1.le⟩)
        (fun x hx => hg₁U x (by nlinarith [hx.1, hx.2, hs₁1, hm0.trans hma])
          (hpos x ⟨hma.trans hx.1.le, hx.2.le.trans hs₁1.le⟩).ne')
        (fun x hx => by unfold pp; nlinarith [hx.1, hx.2, hm0.trans hma])
        (fun x hx => hUK x ⟨hma.trans hx.1.le, hx.2.le⟩)
      refine le_trans ?_ h
      refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (hpos a ⟨hma, has₁.trans hs₁1.le⟩).le
      have : Kl c χ η * (s₁ - a) ≤ Kl c χ η * (ε + η) := mul_le_mul_of_nonneg_left (by linarith) hK0
      exact neg_le_neg (div_le_div_of_nonneg_right this hps₁.le)
    rcases le_or_gt m (T - ε) with hcase | hcase
    · have hturn := Cvs.Prolate.LiouvilleGreen.TurningPointLayer.step_turning (U := U g g₁) (p := pp) (g₁ := g₁) (T := T)
        hcase (by linarith) hpT (hgc m (T - ε) hm0 (by linarith))
        (fun x hx => hg x (mem_uIcc (hm0.trans hx.1.le) (by linarith [hx.2])))
        (fun x hx => hpos x ⟨hx.1.le, by linarith [hx.2]⟩)
        (fun x hx => hg₁U x (by nlinarith [hx.1, hx.2, hT1, hm0]) (hpos x ⟨hx.1.le, by linarith [hx.2]⟩).ne')
        (fun x hx => by unfold pp; have : x ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (hm0.trans hx.1.le) (by linarith [hx.2]) 2
                        linarith)
        (fun x hx => Cvs.Prolate.LiouvilleGreen.TurningPointLayer.le_inv_sub (hUc.mono (Icc_subset_Icc_right hTs₁.le))
          (fun y hy => hUd y ⟨hy.1, hy.2.trans hTs₁⟩) hUsq x ⟨hx.1.le, by linarith [hx.2]⟩)
      have hTm : (log ε - log T) / pp T ≤ (log (T - (T - ε)) - log (T - m)) / pp T := by
        apply div_le_div_of_nonneg_right _ hpT.le
        rw [show T - (T - ε) = ε by ring]
        linarith [log_le_log (by linarith) (show T - m ≤ T by linarith)]
      calc g m * exp ((log ε - log T) / pp T) * exp (-(Kl c χ η * (ε + η) / pp s₁))
          ≤ g m * exp ((log (T - (T - ε)) - log (T - m)) / pp T) * exp (-(Kl c χ η * (ε + η) / pp s₁)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exp_le_exp.2 hTm)
              (hpos m ⟨le_rfl, hmT.trans hT1.le⟩).le) (exp_pos _).le
        _ ≤ g (T - ε) * exp (-(Kl c χ η * (ε + η) / pp s₁)) := mul_le_mul_of_nonneg_right hturn (exp_pos _).le
        _ ≤ g s₁ := hlay (T - ε) hcase le_rfl (by linarith)
    · calc g m * exp ((log ε - log T) / pp T) * exp (-(Kl c χ η * (ε + η) / pp s₁))
          ≤ g m * 1 * exp (-(Kl c χ η * (ε + η) / pp s₁)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac1
              (hpos m ⟨le_rfl, hmT.trans hT1.le⟩).le) (exp_pos _).le
        _ = g m * exp (-(Kl c χ η * (ε + η) / pp s₁)) := by ring
        _ ≤ g s₁ := hlay m le_rfl hcase.le (hmT.trans hTs₁.le)
  exact hstep

end Cvs.Prolate.LiouvilleGreen.WkbEndpointLower
