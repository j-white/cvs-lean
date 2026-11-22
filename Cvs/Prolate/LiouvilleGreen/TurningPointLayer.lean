import Mathlib
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The turning-point layer

A Riccati variable with `U′ ≥ U² ≥ 0` up to `T` has `U ≤ 1/(T − s)`; one with `U′ ≥ −k` has `U(t) ≤ U(b) + k(b − t)`.
Through `g′ = −Ug/p` these give `g(a) ≥ g(m)((T − a)/(T − m))^{1/p_T}` and `g(b) ≥ g(a)e^{−K(b − a)/p_b}`.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.LiouvilleGreen.TurningPointLayer

/-- **Blow-up bound**: if `U` is continuous on `[m, T]` with `U′ ≥ U²` inside, then `U s ≤ 1/(T − s)` on `[m, T)`. -/
theorem le_inv_sub {U U' : ℝ → ℝ} {m T : ℝ} (hUc : ContinuousOn U (Icc m T))
    (hU : ∀ x ∈ Ioo m T, HasDerivAt U (U' x) x) (hge : ∀ x ∈ Ioo m T, U x ^ 2 ≤ U' x) :
    ∀ s ∈ Ico m T, U s ≤ 1 / (T - s) := by
  intro s hs
  have hsT : 0 < T - s := by linarith [hs.2]
  by_contra hcon
  push_neg at hcon
  have hUs : 0 < U s := lt_of_le_of_lt (by positivity) hcon
  have hsub : Icc s T ⊆ Icc m T := Icc_subset_Icc_left hs.1
  -- `U` is monotone on `[s, T]`
  have hmono : MonotoneOn U (Icc s T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc s T) (hUc.mono hsub) ?_ ?_
    · intro x hx; rw [interior_Icc] at hx
      exact (hU x ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hU x ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩).deriv]
      exact le_trans (sq_nonneg _) (hge x ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩)
  have hpos : ∀ x ∈ Icc s T, 0 < U x := fun x hx => lt_of_lt_of_le hUs (hmono ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1)
  -- `1/U + x` is antitone on `[s, T]`
  have hanti : AntitoneOn (fun x => 1 / U x + x) (Icc s T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s T) ?_ ?_ ?_
    · refine ContinuousOn.add ?_ continuousOn_id
      exact continuousOn_const.div (hUc.mono hsub) fun x hx => (hpos x hx).ne'
    · intro x hx; rw [interior_Icc] at hx
      have hx' : x ∈ Ioo m T := ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩
      have hne := (hpos x (Ioo_subset_Icc_self hx)).ne'
      exact (((hasDerivAt_const x (1 : ℝ)).div (hU x hx') hne).add (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      have hx' : x ∈ Ioo m T := ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩
      have hp := hpos x (Ioo_subset_Icc_self hx)
      have hd : HasDerivAt (fun x => 1 / U x + x) ((0 * U x - 1 * U' x) / U x ^ 2 + 1) x :=
        ((hasDerivAt_const x (1 : ℝ)).div (hU x hx') hp.ne').add (hasDerivAt_id x)
      rw [hd.deriv]
      have := hge x hx'
      rw [show (0 * U x - 1 * U' x) / U x ^ 2 + 1 = (U x ^ 2 - U' x) / U x ^ 2 by field_simp; ring]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have h := hanti ⟨le_rfl, hs.2.le⟩ ⟨hs.2.le, le_rfl⟩ hs.2.le
  simp only at h
  have hT := hpos T ⟨hs.2.le, le_rfl⟩
  have h1 : 1 / U s < T - s := by
    rw [div_lt_iff₀ hUs]; rw [div_lt_iff₀ hsT] at hcon; linarith
  have : 0 < 1 / U T := by positivity
  linarith

/-- **Linear bound**: if `U′ ≥ −k` on `(a, b)` then `U t ≤ U b + k(b − t)` on `[a, b]`. -/
theorem le_add_mul {U U' : ℝ → ℝ} {a b k : ℝ} (hUc : ContinuousOn U (Icc a b))
    (hU : ∀ x ∈ Ioo a b, HasDerivAt U (U' x) x) (hge : ∀ x ∈ Ioo a b, -k ≤ U' x) :
    ∀ t ∈ Icc a b, U t ≤ U b + k * (b - t) := by
  intro t ht
  have hmono : MonotoneOn (fun x => U x + k * x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) (hUc.add (continuousOn_const.mul continuousOn_id)) ?_ ?_
    · intro x hx; rw [interior_Icc] at hx
      exact ((hU x hx).add ((hasDerivAt_id x).const_mul k)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      have hd : HasDerivAt (fun x => U x + k * x) (U' x + k * 1) x :=
        (hU x hx).add ((hasDerivAt_id x).const_mul k)
      rw [hd.deriv]
      linarith [hge x hx]
  have := hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
  simp only at this
  linarith

/-- **Step through the approach to the turning point**: if `g > 0`, `g′ = −Ug/p`, `U ≤ 1/(T − s)` and
`p ≥ p_T > 0` on `[m, a]`, `a < T`, then `g(m)((T − a)/(T − m))^{1/p_T} ≤ g(a)`, written with `exp ∘ log`. -/
theorem step_turning {g g₁ U p : ℝ → ℝ} {m a T pT : ℝ} (hma : m ≤ a) (haT : a < T) (hpT : 0 < pT)
    (hgc : ContinuousOn g (Icc m a)) (hg : ∀ x ∈ Ioo m a, HasDerivAt g (g₁ x) x)
    (hg0 : ∀ x ∈ Ioo m a, 0 < g x) (hgU : ∀ x ∈ Ioo m a, g₁ x = -(U x * g x) / p x)
    (hp : ∀ x ∈ Ioo m a, pT ≤ p x) (hUle : ∀ x ∈ Ioo m a, U x ≤ 1 / (T - x)) :
    g m * exp ((log (T - a) - log (T - m)) / pT) ≤ g a := by
  have hmT : 0 < T - m := by linarith
  have h := Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.mul_exp_le (h := fun x => -log (T - x) / pT)
    (h₁ := fun x => 1 / (pT * (T - x))) hma hgc ?_ hg ?_ ?_
  · have e : g m * exp ((log (T - a) - log (T - m)) / pT)
        = g m * exp (-log (T - m) / pT) * exp (-(-log (T - a) / pT)) := by
      rw [mul_assoc, ← exp_add]; congr 1; congr 1; ring
    rw [e]
    calc g m * exp (-log (T - m) / pT) * exp (-(-log (T - a) / pT))
        ≤ g a * exp (-log (T - a) / pT) * exp (-(-log (T - a) / pT)) :=
          mul_le_mul_of_nonneg_right h (exp_pos _).le
      _ = g a := by rw [mul_assoc, ← exp_add]; simp
  · refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.neg ?_
    refine ContinuousOn.log (continuousOn_const.sub continuousOn_id) fun x hx => ?_
    exact (show (0 : ℝ) < T - x by linarith [hx.2]).ne'
  · intro x hx
    have hx0 : 0 < T - x := by linarith [hx.2]
    have hd := (((hasDerivAt_id x).const_sub T).log hx0.ne').neg.div_const pT
    refine hd.congr_deriv ?_
    simp only [id]
    field_simp
  · intro x hx
    have hx0 : 0 < T - x := by linarith [hx.2]
    have hpx : 0 < p x := lt_of_lt_of_le hpT (hp x hx)
    rw [hgU x hx]
    have hgx := hg0 x hx
    have hU' : U x / p x ≤ 1 / (pT * (T - x)) := by
      rcases le_or_gt (U x) 0 with hU0 | hU0
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg hU0 hpx.le) (by positivity)
      · rw [div_le_div_iff₀ hpx (by positivity)]
        have h1 := hUle x hx
        rw [le_div_iff₀ hx0] at h1
        nlinarith [hp x hx]
    have : -(U x * g x) / p x + g x * (1 / (pT * (T - x))) = g x * (1 / (pT * (T - x)) - U x / p x) := by
      field_simp; ring
    rw [this]
    exact mul_nonneg hgx.le (by linarith)

/-- **Step across a layer with bounded `U`**: if `g > 0`, `g′ = −Ug/p`, `U ≤ K` (`K ≥ 0`) and `p ≥ p_b > 0` on
`[a, b]`, then `g(a)e^{−K(b − a)/p_b} ≤ g(b)`. -/
theorem step_layer {g g₁ U p : ℝ → ℝ} {a b K pb : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hpb : 0 < pb)
    (hgc : ContinuousOn g (Icc a b)) (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g₁ x) x)
    (hg0 : ∀ x ∈ Ioo a b, 0 < g x) (hgU : ∀ x ∈ Ioo a b, g₁ x = -(U x * g x) / p x)
    (hp : ∀ x ∈ Ioo a b, pb ≤ p x) (hUle : ∀ x ∈ Ioo a b, U x ≤ K) :
    g a * exp (-(K * (b - a) / pb)) ≤ g b := by
  have h := Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.mul_exp_le (h := fun x => K * x / pb) (h₁ := fun _ => K / pb) hab hgc
    ((continuousOn_const.mul continuousOn_id).div_const _) hg
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul K).div_const pb) ?_
  · calc g a * exp (-(K * (b - a) / pb)) = g a * exp (K * a / pb) * exp (-(K * b / pb)) := by
          rw [mul_assoc, ← exp_add]; congr 1; congr 1; ring
      _ ≤ g b * exp (K * b / pb) * exp (-(K * b / pb)) := mul_le_mul_of_nonneg_right h (exp_pos _).le
      _ = g b := by rw [mul_assoc, ← exp_add]; simp
  · intro x hx
    have hpx : 0 < p x := lt_of_lt_of_le hpb (hp x hx)
    rw [hgU x hx]
    have hgx := hg0 x hx
    have hU' : U x / p x ≤ K / pb := by
      rcases le_or_gt (U x) 0 with hU0 | hU0
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg hU0 hpx.le) (by positivity)
      · calc U x / p x ≤ K / p x := div_le_div_of_nonneg_right (hUle x hx) hpx.le
          _ ≤ K / pb := div_le_div_of_nonneg_left hK hpb (hp x hx)
    have : -(U x * g x) / p x + g x * (K / pb) = g x * (K / pb - U x / p x) := by field_simp; ring
    rw [this]
    exact mul_nonneg hgx.le (by linarith)

end Cvs.Prolate.LiouvilleGreen.TurningPointLayer
