import Mathlib
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The peak of an even angular prolate

For `((1 − s²)g′)′ = (c²s² − χ)g` with `0 < χ < c²`, `g` even, `∫g² = 1`, `g(1) ≠ 0`: some `m ∈ [0, √χ/c]` has
`g(m)² ≥ 1/2`, `g` keeps the sign of `g(m)` on `[m, 1]` and `g·g′ ≤ 0` there. Beyond the turning point the flux
forbids zeros; before it the Sonin amplitude `g² + ((1 − s²)g′)²/((1 − s²)(χ − c²s²))` is nondecreasing.
-/

noncomputable section

open Real Set Filter Topology

namespace Cvs.Prolate.EvenAngularPeak

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-! ### Monotonicity from a derivative on a closed interval -/

/-- A function differentiable on `[a, b]` with nonnegative derivative inside is monotone there. -/
theorem monotoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (h : ∀ x ∈ Ioo a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by rw [interior_Icc] at hx ⊢; exact (hf x (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Icc] at hx; exact h x hx)

/-- A function differentiable on `[a, b]` with positive derivative inside is strictly monotone there. -/
theorem strictMonoOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (h : ∀ x ∈ Ioo a b, 0 < f' x) : StrictMonoOn f (Icc a b) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by rw [interior_Icc] at hx ⊢; exact (hf x (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Icc] at hx; exact h x hx)

/-- A function differentiable on `[a, b]` with nonpositive derivative inside is antitone there. -/
theorem antitoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (h : ∀ x ∈ Ioo a b, f' x ≤ 0) : AntitoneOn f (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by rw [interior_Icc] at hx ⊢; exact (hf x (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Icc] at hx; exact h x hx)

/-- A function differentiable on `[a, b]` with negative derivative inside is strictly antitone there. -/
theorem strictAntiOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (h : ∀ x ∈ Ioo a b, f' x < 0) : StrictAntiOn f (Icc a b) :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by rw [interior_Icc] at hx ⊢; exact (hf x (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Icc] at hx; exact h x hx)

/-- The square `g²` has derivative `2gg′`. -/
theorem hasDerivAt_sq {x : ℝ} (h : HasDerivAt g (g₁ x) x) :
    HasDerivAt (fun s => g s ^ 2) (2 * g x * g₁ x) x :=
  (h.pow 2).congr_deriv (by simp)

/-! ### The flux and the turning point -/

/-- The flux `(1 − s²)g′` has derivative `(c²s² − χ)g` on `[−1, 1]`. -/
theorem hasDerivAt_flux (hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (heq : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun t => (1 - t ^ 2) * g₁ t) ((c ^ 2 * s ^ 2 - χ) * g s) s := by
  have hp : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_sub 1)
  exact (hp.mul (hd₁ s hs)).congr_deriv (by linear_combination heq s hs)

/-- The turning point `s₀ = √χ/c` lies in `(0, 1)` and satisfies `c²s₀² = χ`. -/
theorem turn_facts (hc : 0 < c) (hχ0 : 0 < χ) (hχc : χ < c ^ 2) :
    0 < √χ / c ∧ √χ / c < 1 ∧ c ^ 2 * (√χ / c) ^ 2 = χ := by
  refine ⟨by positivity, (div_lt_one hc).2 ((Real.sqrt_lt' hc).2 hχc), ?_⟩
  rw [div_pow, Real.sq_sqrt hχ0.le]
  field_simp

/-- The potential factors through the turning point: `c²s² − χ = c²(s − s₀)(s + s₀)`. -/
theorem pot_eq {s₀ s : ℝ} (hcs : c ^ 2 * s₀ ^ 2 = χ) : c ^ 2 * s ^ 2 - χ = c ^ 2 * ((s - s₀) * (s + s₀)) := by
  rw [← hcs]; ring

/-! ### The forbidden zone -/

/-- Beyond the turning point, if `g` has the sign of `g(1)` on `[a, 1]` then the flux at `a < 1` has the opposite
sign. -/
theorem flux_mul_neg (hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (heq : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) {s₀ a : ℝ} (hs₀ : 0 ≤ s₀) (hcs : c ^ 2 * s₀ ^ 2 = χ) (ha : s₀ ≤ a) (ha1 : a < 1)
    (hpos : ∀ s ∈ Icc a 1, 0 < g 1 * g s) : (1 - a ^ 2) * g₁ a * g 1 < 0 := by
  have hmono : StrictMonoOn (fun t => (1 - t ^ 2) * g₁ t * g 1) (Icc a 1) := by
    refine strictMonoOn_Icc (f' := fun t => (c ^ 2 * t ^ 2 - χ) * g t * g 1) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hasDerivAt_flux hd₁ heq ⟨by linarith [hx.1], hx.2⟩).mul_const (g 1)
    · have h1 : 0 < c ^ 2 * x ^ 2 - χ := by
        rw [pot_eq hcs]
        exact mul_pos (by positivity) (mul_pos (by linarith [hx.1]) (by linarith [hx.1]))
      have h2 := hpos x (Ioo_subset_Icc_self hx)
      have : (c ^ 2 * x ^ 2 - χ) * g x * g 1 = (c ^ 2 * x ^ 2 - χ) * (g 1 * g x) := by ring
      simp only [this]
      exact mul_pos h1 h2
  have := hmono ⟨le_rfl, ha1.le⟩ ⟨ha1.le, le_rfl⟩ ha1
  simpa using this

/-- Beyond the turning point `g` has no zero: `g(1)g(s) > 0` on `[s₀, 1]`. -/
theorem forbidden (hd : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (heq : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hcs : c ^ 2 * s₀ ^ 2 = χ) (hg1 : g 1 ≠ 0) :
    ∀ s ∈ Icc s₀ 1, 0 < g 1 * g s := by
  have hgc : ContinuousOn g (Icc s₀ 1) := fun s hs =>
    (hd s ⟨by linarith [hs.1], hs.2⟩).continuousAt.continuousWithinAt
  have hg1sq : 0 < g 1 * g 1 := mul_self_pos.2 hg1
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hle⟩ := hcon
  set Z := Icc s₀ 1 ∩ (fun t => g 1 * g t) ⁻¹' Iic 0 with hZ
  have hZc : IsClosed Z :=
    (continuousOn_const.mul hgc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZb : BddAbove Z := ⟨1, fun t ht => ht.1.2⟩
  have hz := hZc.csSup_mem ⟨s, hs, hle⟩ hZb
  set z := sSup Z
  have hz2 : g 1 * g z ≤ 0 := hz.2
  have hz1 : z < 1 := lt_of_le_of_ne hz.1.2 (fun h => by rw [h] at hz2; linarith)
  have hright : ∀ t ∈ Ioc z 1, 0 < g 1 * g t := fun t ht => by
    by_contra h
    push Not at h
    have : t ≤ z := le_csSup hZb ⟨⟨by linarith [hz.1.1, ht.1], ht.2⟩, h⟩
    linarith [ht.1]
  have hder : ∀ t ∈ Ioo z 1, g 1 * g₁ t ≤ 0 := fun t ht => by
    have := flux_mul_neg hd₁ heq hc hs₀ hcs (by linarith [hz.1.1, ht.1]) ht.2
      (fun u hu => hright u ⟨by linarith [hu.1, ht.1], hu.2⟩)
    have hp : 0 < 1 - t ^ 2 := by nlinarith [hz.1.1, ht.1, ht.2]
    nlinarith
  have hanti : AntitoneOn (fun t => g 1 * g t) (Icc z 1) :=
    antitoneOn_Icc (f' := fun t => g 1 * g₁ t)
      (fun x hx => (hd x ⟨by linarith [hz.1.1, hx.1], hx.2⟩).const_mul (g 1)) hder
  have := hanti ⟨le_rfl, hz1.le⟩ ⟨hz1.le, le_rfl⟩ hz1.le
  simp only at this
  linarith

/-- Beyond the turning point `|g|` strictly decreases: `g g′ < 0` on `[s₀, 1]`. -/
theorem forbidden_deriv (hd : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (heq : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hs₀1 : s₀ < 1) (hcs : c ^ 2 * s₀ ^ 2 = χ) (hg1 : g 1 ≠ 0) :
    ∀ s ∈ Icc s₀ 1, g s * g₁ s < 0 := by
  intro s hs
  have hpos := forbidden hd hd₁ heq hc hs₀ hcs hg1
  have h1 : g₁ s * g 1 < 0 := by
    rcases eq_or_lt_of_le hs.2 with h | h
    · subst h
      have h1 := heq 1 ⟨by norm_num, le_rfl⟩
      have hg1' : g₁ 1 = (χ - c ^ 2) * g 1 / 2 := by linear_combination (-1 / 2 : ℝ) * h1
      have hgap : 0 < c ^ 2 - χ := by
        rw [← hcs]
        have : 0 < 1 - s₀ ^ 2 := by nlinarith
        nlinarith [mul_pos (pow_pos hc 2) this]
      rw [hg1']
      nlinarith [mul_pos hgap (mul_self_pos.2 hg1)]
    · have := flux_mul_neg hd₁ heq hc hs₀ hcs hs.1 h (fun u hu => hpos u ⟨hs.1.trans hu.1, hu.2⟩)
      have hp : 0 < 1 - s ^ 2 := by nlinarith [hs.1]
      nlinarith
  have h2 := hpos s hs
  have h3 : 0 < g 1 ^ 2 := by positivity
  nlinarith [mul_neg_of_neg_of_pos h1 h2]

/-! ### The amplitude in the allowed region -/

/-- The Sonin amplitude `g² + ((1 − s²)g′)²/((1 − s²)(χ − c²s²))`. -/
def amp (g g₁ : ℝ → ℝ) (c χ s : ℝ) : ℝ :=
  g s ^ 2 + ((1 - s ^ 2) * g₁ s) ^ 2 / ((1 - s ^ 2) * (χ - c ^ 2 * s ^ 2))

/-- The amplitude has derivative `w² · 2s(χ + c² − 2c²s²)/D²`, `w = (1 − s²)g′`, `D = (1 − s²)(χ − c²s²)`. -/
theorem hasDerivAt_amp (hd : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (heq : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (hD : (1 - s ^ 2) * (χ - c ^ 2 * s ^ 2) ≠ 0) :
    HasDerivAt (amp g g₁ c χ)
      (((1 - s ^ 2) * g₁ s) ^ 2 * (2 * s * (χ + c ^ 2 - 2 * c ^ 2 * s ^ 2)) /
        ((1 - s ^ 2) * (χ - c ^ 2 * s ^ 2)) ^ 2) s := by
  have hw := hasDerivAt_flux hd₁ heq hs
  have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_sub 1)
  have h2 : HasDerivAt (fun t : ℝ => χ - c ^ 2 * t ^ 2) (-(c ^ 2 * (2 * s))) s := by
    simpa using (((hasDerivAt_pow 2 s).const_mul (c ^ 2)).const_sub χ)
  have := (hasDerivAt_sq (hd s hs)).add ((hw.pow 2).div (h1.mul h2) hD)
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  have hA : 1 - s ^ 2 ≠ 0 := left_ne_zero_of_mul hD
  have hB : χ - c ^ 2 * s ^ 2 ≠ 0 := right_ne_zero_of_mul hD
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  simp only [Nat.cast_ofNat]
  have hB' : χ - s ^ 2 * c ^ 2 ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- Before the turning point the amplitude is nondecreasing: `amp a ≤ amp b` for `0 ≤ a ≤ b < s₀`. -/
theorem amp_mono (hd : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (heq : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) {s₀ : ℝ} (hs₀1 : s₀ < 1) (hcs : c ^ 2 * s₀ ^ 2 = χ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < s₀) : amp g g₁ c χ a ≤ amp g g₁ c χ b := by
  have hfacts : ∀ x ∈ Icc a b, x ∈ Icc (-1 : ℝ) 1 ∧ 0 < 1 - x ^ 2 ∧ 0 < χ - c ^ 2 * x ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hxs : x < s₀ := lt_of_le_of_lt hx.2 hb
    refine ⟨⟨by linarith, by linarith⟩, by nlinarith, ?_⟩
    have := pot_eq (s := x) hcs
    have : 0 < c ^ 2 * ((s₀ - x) * (x + s₀)) :=
      mul_pos (by positivity) (mul_pos (by linarith) (by linarith))
    nlinarith
  refine monotoneOn_Icc (fun x hx => hasDerivAt_amp hd hd₁ heq (hfacts x hx).1
    (mul_pos (hfacts x hx).2.1 (hfacts x hx).2.2).ne') (fun x hx => ?_) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hx0 : 0 ≤ x := ha.trans hx.1.le
  have hx := hfacts x (Ioo_subset_Icc_self hx)
  refine div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) ?_)) (sq_nonneg _)
  nlinarith [hx.2.2]

/-! ### Critical points -/

/-- At an interior maximum of `g²` on `[a, b]` with `g ≠ 0`, `g′` vanishes. -/
theorem deriv_eq_zero_of_isMaxOn {a b m : ℝ} (hm : m ∈ Ioo a b) (hdm : HasDerivAt g (g₁ m) m)
    (hmax : IsMaxOn (fun s => g s ^ 2) (Icc a b) m) (hgm : g m ≠ 0) : g₁ m = 0 := by
  have hloc : IsLocalMax (fun s => g s ^ 2) m := hmax.isLocalMax (Icc_mem_nhds hm.1 hm.2)
  have h := hloc.hasDerivAt_eq_zero (hasDerivAt_sq hdm)
  rcases mul_eq_zero.1 h with h | h
  · exact absurd ((mul_eq_zero.1 h).resolve_left two_ne_zero) hgm
  · exact h

/-- An even function has `g′(0) = 0`. -/
theorem deriv_zero_of_even (hd0 : HasDerivAt g (g₁ 0) 0) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    g₁ 0 = 0 := by
  have h1 : HasDerivAt (g ∘ Neg.neg) (g₁ 0 * -1) 0 :=
    HasDerivAt.comp (0 : ℝ) (by simpa using hd0) (hasDerivAt_neg 0)
  have h2 : HasDerivAt g (g₁ 0 * -1) 0 := h1.congr_of_eventuallyEq (by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with s hs
    exact (heven s hs).symm)
  have := hd0.unique h2
  linarith

/-! ### The peak -/

/-- **The peak lemma**: an even angular prolate has a point `m ∈ [0, √χ/c]` maximising `g²` on `[0, 1]`, with
`g(m)² ≥ 1/2`, beyond which `g` keeps its sign and `|g|` is nonincreasing. -/
theorem exists_peak (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hc : 0 < c) (hχ0 : 0 < χ) (hχc : χ < c ^ 2) (hg1 : g 1 ≠ 0) :
    ∃ m ∈ Icc (0 : ℝ) (√χ / c), 1 / 2 ≤ g m ^ 2 ∧ (∀ s ∈ Icc m 1, 0 < g m * g s) ∧
      (∀ s ∈ Icc m 1, g s * g₁ s ≤ 0) ∧ ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 ≤ g m ^ 2 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hd : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s := fun s hs => hg s (hI ▸ hs)
  have hd₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s := fun s hs => hg₁ s (hI ▸ hs)
  have heq : ∀ s ∈ Icc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0 := fun s hs => hang s (hI ▸ hs)
  obtain ⟨hs₀0, hs₀1, hcs⟩ := turn_facts hc hχ0 hχc
  set s₀ := √χ / c with hs₀
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  have hgc01 : ContinuousOn (fun s => g s ^ 2) (Icc (0 : ℝ) 1) := (hgc.mono hsub).pow 2
  -- the maximum of `g²` on `[0, 1]` is at least `1/2`
  obtain ⟨p, hp, hpmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hgc01
  set M := g p ^ 2 with hMdef
  have hhalf : ∫ s in (0 : ℝ)..1, g s ^ 2 = 1 / 2 := by
    have := Cvs.Prolate.AngularBesselInequality.integral_sq_even hgc heven
    linarith
  have hM : 1 / 2 ≤ M := by
    have hint : IntervalIntegrable (fun s => g s ^ 2) MeasureTheory.volume 0 1 :=
      (by rwa [uIcc_of_le zero_le_one] : ContinuousOn (fun s => g s ^ 2) (uIcc 0 1)).intervalIntegrable
    have := intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
      (fun x hx => (isMaxOn_iff.1 hpmax x hx : g x ^ 2 ≤ M))
    simpa [hhalf] using this
  -- the largest maximiser
  set S := Icc (0 : ℝ) 1 ∩ (fun s => g s ^ 2) ⁻¹' {M} with hS
  have hSc : IsClosed S := hgc01.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSb : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hmS := hSc.csSup_mem ⟨p, hp, rfl⟩ hSb
  set m := sSup S
  have hmM : g m ^ 2 = M := hmS.2
  have hmax : IsMaxOn (fun s => g s ^ 2) (Icc 0 1) m := isMaxOn_iff.2 fun s hs => by
    show g s ^ 2 ≤ g m ^ 2
    rw [hmM]; exact isMaxOn_iff.1 hpmax s hs
  have hlargest : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = M → s ≤ m := fun s hs h => le_csSup hSb ⟨hs, h⟩
  have hgm : g m ≠ 0 := fun h => by rw [h] at hmM; linarith
  have hpos1 := forbidden hd hd₁ heq hc hs₀0.le hcs hg1
  have hfd := forbidden_deriv hd hd₁ heq hc hs₀0.le hs₀1 hcs hg1
  -- the largest maximiser is before the turning point
  have hms₀ : m ≤ s₀ := by
    by_contra h
    push Not at h
    have hanti : StrictAntiOn (fun s => g s ^ 2) (Icc s₀ 1) :=
      strictAntiOn_Icc (fun x hx => hasDerivAt_sq (hd x ⟨by linarith [hx.1], hx.2⟩))
        (fun x hx => by nlinarith [hfd x (Ioo_subset_Icc_self hx)])
    have h1 : g m ^ 2 < g s₀ ^ 2 := hanti ⟨le_rfl, hs₀1.le⟩ ⟨h.le, hmS.1.2⟩ h
    have h2 : g s₀ ^ 2 ≤ g m ^ 2 := isMaxOn_iff.1 hmax s₀ ⟨hs₀0.le, hs₀1.le⟩
    linarith
  -- `g′` vanishes at the peak
  have hg₁m : g₁ m = 0 := by
    rcases eq_or_lt_of_le hmS.1.1 with h | h
    · rw [← h]; exact deriv_zero_of_even (hd 0 ⟨by norm_num, by norm_num⟩) heven
    · exact deriv_eq_zero_of_isMaxOn ⟨h, by linarith⟩ (hd m ⟨by linarith, by linarith⟩) hmax hgm
  -- no zero after the peak
  have hnz : ∀ s ∈ Icc m 1, g s ≠ 0 := by
    intro z hz hz0
    have hzs₀ : z < s₀ := by
      by_contra h
      push Not at h
      have := hpos1 z ⟨h, hz.2⟩
      rw [hz0, mul_zero] at this
      exact lt_irrefl _ this
    have hmz : m < z := lt_of_le_of_ne hz.1 (fun h => hgm (h ▸ hz0))
    have hsub' : Icc z s₀ ⊆ Icc (-1) 1 := Icc_subset_Icc (by linarith [hmS.1.1]) hs₀1.le
    obtain ⟨m', hm', hm'max⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hzs₀.le) ((hgc.mono hsub').pow 2)
    have hgs₀ : g s₀ ≠ 0 := fun h => by
      have := hpos1 s₀ ⟨le_rfl, hs₀1.le⟩
      rw [h, mul_zero] at this
      exact lt_irrefl _ this
    have hge : g s₀ ^ 2 ≤ g m' ^ 2 := isMaxOn_iff.1 hm'max s₀ ⟨hzs₀.le, le_rfl⟩
    have hgm' : g m' ≠ 0 := fun h => by
      rw [h] at hge
      have : 0 < g s₀ ^ 2 := by positivity
      linarith
    have hm'z : z < m' := lt_of_le_of_ne hm'.1 (fun h => hgm' (h ▸ hz0))
    have hm's₀ : m' < s₀ := by
      refine lt_of_le_of_ne hm'.2 (fun h => ?_)
      have hder := (hasDerivAt_sq (hd s₀ ⟨by linarith, hs₀1.le⟩)).neg
      have := Cvs.Prolate.EdgeCentreSign.deriv_nonpos_of_left hder (by
        filter_upwards [Ioo_mem_nhdsLT hzs₀] with t ht
        have : g t ^ 2 ≤ g m' ^ 2 := isMaxOn_iff.1 hm'max t (Ioo_subset_Icc_self ht)
        rw [h] at this
        show -(g s₀ ^ 2) ≤ -(g t ^ 2)
        linarith)
      linarith [hfd s₀ ⟨le_rfl, hs₀1.le⟩]
    have hg₁m' := deriv_eq_zero_of_isMaxOn ⟨hm'z, hm's₀⟩ (hd m' (hsub' hm')) hm'max hgm'
    have hF := amp_mono hd hd₁ heq hc hχc hs₀1 hcs hmS.1.1 (hmz.trans hm'z).le hm's₀
    simp only [amp, hg₁m, hg₁m', mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, add_zero] at hF
    have hm'01 : m' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hmS.1.1], by linarith⟩
    have := hlargest m' hm'01 (le_antisymm (hmM ▸ isMaxOn_iff.1 hmax m' hm'01) (hmM ▸ hF))
    linarith
  have hsign : ∀ s ∈ Icc m 1, 0 < g m * g s :=
    Cvs.Prolate.EdgeCentreSign.mul_pos_of_ne_zero
      (hgc.mono (Icc_subset_Icc (by linarith [hmS.1.1]) le_rfl)) hnz
  refine ⟨m, ⟨hmS.1.1, hms₀⟩, hmM ▸ hM, hsign, fun s hs => ?_, fun s hs => isMaxOn_iff.1 hmax s hs⟩
  rcases le_or_gt s₀ s with h | h
  · exact (hfd s ⟨h, hs.2⟩).le
  · -- before the turning point the flux starts at `0` at the peak and moves against `g(m)`
    have hanti : AntitoneOn (fun t => (1 - t ^ 2) * g₁ t * g m) (Icc m s) := by
      refine antitoneOn_Icc (f' := fun t => (c ^ 2 * t ^ 2 - χ) * g t * g m)
        (fun x hx => (hasDerivAt_flux hd₁ heq ⟨by linarith [hmS.1.1, hx.1], by linarith [hx.2]⟩).mul_const _)
        (fun x hx => ?_)
      have h1 : c ^ 2 * x ^ 2 - χ ≤ 0 := by
        rw [pot_eq hcs]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (by linarith [hmS.1.1, hx.1]))
      have h2 := hsign x ⟨hx.1.le, by linarith [hx.2]⟩
      have : (c ^ 2 * x ^ 2 - χ) * g x * g m = (c ^ 2 * x ^ 2 - χ) * (g m * g x) := by ring
      simp only [this]
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2.le
    have := hanti ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
    simp only [hg₁m, mul_zero, zero_mul] at this
    have hp : 0 < 1 - s ^ 2 := by nlinarith [hmS.1.1, hs.1]
    have h2 := hsign s hs
    have h3 : g₁ s * g m ≤ 0 := by nlinarith
    have h4 : 0 < g m ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h3 h2.le]

end Cvs.Prolate.EvenAngularPeak
