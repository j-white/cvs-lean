import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The planar box lemma

The planar box lemma of the EdgeResidue assembly: a continuous function on a box, negative on the
sides and nonpositive on the bottom, with the local wedge conditions at its zeros, is negative above
the bottom.
-/

open Set Filter Topology

namespace Cvs.StepA.Edge.PlanarBoxLemma
/-- **Box lemma**: a continuous `f` on the box `[-ρ, ρ] × [a, b]`, negative on the sides,
nonpositive on the bottom, with a negative upper half-disc at each bottom zero and a positive
point below-left of each interior zero that is a local maximum of its row, is negative above `a`. -/
theorem box_neg {f : ℝ × ℝ → ℝ} (hf : Continuous f) {ρ a b : ℝ}
    (hside : ∀ y ∈ Icc a b, f (-ρ, y) < 0 ∧ f (ρ, y) < 0)
    (hbot : ∀ x ∈ Icc (-ρ) ρ, f (x, a) ≤ 0)
    (hWA : ∀ z ∈ Ioo (-ρ) ρ, f (z, a) = 0 → ∃ r > 0, ∀ x y, a ≤ y →
      0 < (x - z) ^ 2 + (y - a) ^ 2 → (x - z) ^ 2 + (y - a) ^ 2 < r ^ 2 → f (x, y) < 0)
    (hWB : ∀ x₀ ∈ Ioo (-ρ) ρ, ∀ y₀ ∈ Ioc a b, f (x₀, y₀) = 0 →
      (∃ ε > 0, ∀ x, |x - x₀| < ε → f (x, y₀) ≤ 0) →
      ∃ lam > 0, ∃ η₀ > 0, ∀ η ∈ Ioo 0 η₀, 0 < f (x₀ - lam * η, y₀ - η)) :
    ∀ x ∈ Icc (-ρ) ρ, ∀ y ∈ Ioc a b, f (x, y) < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁, y₁, hy₁, hf₁⟩ := hcon
  have hab : a ≤ b := hy₁.1.le.trans hy₁.2
  -- the nonnegative set of the box strictly above the bottom edge
  set B : Set (ℝ × ℝ) := Icc (-ρ) ρ ×ˢ Icc a b
  set K' : Set (ℝ × ℝ) := {p | p ∈ B ∧ 0 ≤ f p ∧ a < p.2}
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hK'cl : IsClosed K' := by
    refine isClosed_of_closure_subset fun p hp => ?_
    have hpB : p ∈ B := closure_minimal (fun q (hq : q ∈ K') => hq.1) hBc.isClosed hp
    have hpf : 0 ≤ f p := closure_minimal (fun q (hq : q ∈ K') => hq.2.1) (isClosed_le continuous_const hf) hp
    have hpa : a ≤ p.2 :=
      closure_minimal (fun q (hq : q ∈ K') => hq.2.2.le) (isClosed_le continuous_const continuous_snd) hp
    refine ⟨hpB, hpf, lt_of_le_of_ne hpa fun hpa' => ?_⟩
    obtain ⟨px, py⟩ := p
    simp only at hpa'
    subst hpa'
    have hz : f (px, a) = 0 := le_antisymm (hbot px hpB.1) hpf
    have hpx : px ∈ Ioo (-ρ) ρ := by
      have hs := hside a ⟨le_rfl, hab⟩
      refine ⟨lt_of_le_of_ne hpB.1.1 fun h => ?_, lt_of_le_of_ne hpB.1.2 fun h => ?_⟩
      · rw [← h] at hz; linarith [hs.1]
      · rw [h] at hz; linarith [hs.2]
    obtain ⟨r, hr, hdisc⟩ := hWA px hpx hz
    have hN : IsOpen {q : ℝ × ℝ | (q.1 - px) ^ 2 + (q.2 - a) ^ 2 < r ^ 2} :=
      isOpen_lt (by fun_prop) continuous_const
    obtain ⟨⟨qx, qy⟩, hqN, hqK⟩ :=
      mem_closure_iff.1 hp _ hN (show (px - px) ^ 2 + (a - a) ^ 2 < r ^ 2 by
        simpa using pow_pos hr 2)
    have hqy : 0 < (qy - a) ^ 2 := by have := hqK.2.2; simp only at this; positivity
    have := hdisc qx qy hqK.2.2.le (by positivity) hqN
    linarith [hqK.2.1]
  have hK'c : IsCompact K' := hBc.of_isClosed_subset hK'cl fun q hq => hq.1
  obtain ⟨⟨x₂, y₂⟩, hpK, hmin⟩ :=
    hK'c.exists_isMinOn ⟨(x₁, y₁), ⟨hx₁, hy₁.1.le, hy₁.2⟩, hf₁, hy₁.1⟩ continuous_snd.continuousOn
  obtain ⟨⟨hx₂, hy₂a, hy₂b⟩, hf₂, hay₂⟩ := hpK
  simp only at hf₂ hay₂
  -- `f < 0` on the box strictly between the bottom edge and the lowest point
  have hbelow : ∀ x ∈ Icc (-ρ) ρ, ∀ y, a < y → y < y₂ → f (x, y) < 0 := by
    intro x hx y hay hy
    by_contra h
    have := isMinOn_iff.1 hmin (x, y) ⟨⟨hx, hay.le, hy.le.trans hy₂b⟩, not_lt.1 h, hay⟩
    exact absurd this (not_le.2 hy)
  have hrow : ∀ x ∈ Icc (-ρ) ρ, f (x, y₂) ≤ 0 := by
    intro x hx
    have ht : Tendsto (fun y => f (x, y)) (𝓝[<] y₂) (𝓝 (f (x, y₂))) :=
      ((hf.comp (Continuous.prodMk continuous_const continuous_id)).tendsto y₂).mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hay₂] with y hy
    exact (hbelow x hx y hy.1 hy.2).le
  have hz₂ : f (x₂, y₂) = 0 := le_antisymm (hrow x₂ hx₂) hf₂
  have hx₂' : x₂ ∈ Ioo (-ρ) ρ := by
    have hs := hside y₂ ⟨hay₂.le, hy₂b⟩
    refine ⟨lt_of_le_of_ne hx₂.1 fun h => ?_, lt_of_le_of_ne hx₂.2 fun h => ?_⟩
    · rw [← h] at hz₂; linarith [hs.1]
    · rw [h] at hz₂; linarith [hs.2]
  have hloc : ∃ ε > 0, ∀ x, |x - x₂| < ε → f (x, y₂) ≤ 0 := by
    refine ⟨min (x₂ + ρ) (ρ - x₂), lt_min (by linarith [hx₂'.1]) (by linarith [hx₂'.2]),
      fun x hx => hrow x ?_⟩
    rw [abs_lt] at hx
    have := min_le_left (x₂ + ρ) (ρ - x₂)
    have := min_le_right (x₂ + ρ) (ρ - x₂)
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨lam, hlam, η₀, hη₀, hpos⟩ := hWB x₂ hx₂' y₂ ⟨hay₂, hy₂b⟩ hz₂ hloc
  set η := min (η₀ / 2) (min ((y₂ - a) / 2) ((x₂ + ρ) / (2 * lam))) with hη
  have hx₂ρ : 0 < x₂ + ρ := by linarith [hx₂'.1]
  have hηpos : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  have hη1 : η ≤ η₀ / 2 := min_le_left _ _
  have hη2 : η ≤ (y₂ - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ (x₂ + ρ) / (2 * lam) := (min_le_right _ _).trans (min_le_right _ _)
  have hlη : lam * η ≤ (x₂ + ρ) / 2 := by
    calc lam * η ≤ lam * ((x₂ + ρ) / (2 * lam)) := mul_le_mul_of_nonneg_left hη3 hlam.le
      _ = (x₂ + ρ) / 2 := by field_simp
  have h1 := hpos η ⟨hηpos, by linarith⟩
  have h2 := hbelow (x₂ - lam * η)
    ⟨by linarith, by nlinarith [hx₂'.2]⟩ (y₂ - η) (by linarith) (by linarith)
  linarith

end Cvs.StepA.Edge.PlanarBoxLemma
