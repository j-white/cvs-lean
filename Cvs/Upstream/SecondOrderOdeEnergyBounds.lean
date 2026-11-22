import Mathlib
import Cvs.Upstream.LowerRiccatiBarrier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Energy bounds for `g'' + Q g = 0` and the Coulomb amplitude

For a solution of `g'' + Qg = 0`: `Qg² + g'²` moves by `∫Q'g²`, `√Q g² + g'²/√Q` by at most `exp(½∫|Q'|/Q)`, and
`μg² + g'²/μ` by at most `exp(∫(μ + |Q|/μ))`; the Coulomb energy `G² + xG'²/(k + x/4)` is nonincreasing, so `|G| ≤ 1`.
-/

noncomputable section

open Real Set Filter Topology

namespace Cvs.Upstream.SecondOrderOdeEnergyBounds

/-! ### Exponential comparison -/

/-- **Gronwall with a variable rate**: `F' ≤ τ' F` on `(a, b)` gives `F(b) ≤ F(a) e^{τ(b) − τ(a)}`. -/
theorem le_mul_exp_of_deriv_le {F F₁ τ τ₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hτ : ContinuousOn τ (Icc a b)) (hF' : ∀ x ∈ Ioo a b, HasDerivAt F (F₁ x) x)
    (hτ' : ∀ x ∈ Ioo a b, HasDerivAt τ (τ₁ x) x) (hd : ∀ x ∈ Ioo a b, F₁ x ≤ τ₁ x * F x) :
    F b ≤ F a * exp (τ b - τ a) := by
  have h := Cvs.Upstream.LowerRiccatiBarrier.mul_exp_le_rev (g := F) (g₁ := F₁) (h := fun x => -τ x)
    (h₁ := fun x => -τ₁ x) hab hF hτ.neg hF' (fun x hx => (hτ' x hx).neg)
    (fun x hx => by have := hd x hx; linarith)
  have e : F b = F b * exp (-τ b) * exp (τ b) := by rw [mul_assoc, ← exp_add]; simp
  rw [e, show τ b - τ a = -τ a + τ b by ring, exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (exp_pos _).le

/-- A function with nonpositive derivative on `(a, b)`, continuous on `[a, b]`, has `F(b) ≤ F(a)`. -/
theorem le_of_deriv_nonpos {F F₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hF' : ∀ x ∈ Ioo a b, HasDerivAt F (F₁ x) x) (hd : ∀ x ∈ Ioo a b, F₁ x ≤ 0) : F b ≤ F a := by
  have h := le_mul_exp_of_deriv_le (τ := fun _ => 0) (τ₁ := fun _ => 0) hab hF continuousOn_const hF'
    (fun x _ => hasDerivAt_const x 0) (fun x hx => by simpa using hd x hx)
  simpa using h

/-! ### The plain energy `Qg² + g'²` -/

/-- **The plain energy**: for `g'' = −Qg`, `(Qg² + g'²)' = Q'g²`. -/
theorem hasDerivAt_energyQ {g g₁ Q Q₁ : ℝ → ℝ} {x : ℝ} (hg : HasDerivAt g (g₁ x) x)
    (hg₁ : HasDerivAt g₁ (-(Q x * g x)) x) (hQ : HasDerivAt Q (Q₁ x) x) :
    HasDerivAt (fun y => Q y * g y ^ 2 + g₁ y ^ 2) (Q₁ x * g x ^ 2) x := by
  have h := (hQ.fun_mul (hg.fun_pow 2)).fun_add (hg₁.fun_pow 2)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- **Kernel bound, `Q` nonincreasing**: if `g'' = −Qg`, `Q' ≤ 0`, `g(a) = 0` and `g'(a) = 1`, then
`Q(x)g(x)² + g'(x)² ≤ 1` on `[a, b]`. -/
theorem energyQ_le_one {g g₁ Q Q₁ : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g₁ x) x) (hg₁ : ∀ x ∈ Icc a b, HasDerivAt g₁ (-(Q x * g x)) x)
    (hQ : ∀ x ∈ Icc a b, HasDerivAt Q (Q₁ x) x) (hQ₁ : ∀ x ∈ Icc a b, Q₁ x ≤ 0)
    (ha : g a = 0) (ha₁ : g₁ a = 1) : ∀ x ∈ Icc a b, Q x * g x ^ 2 + g₁ x ^ 2 ≤ 1 := by
  intro x hx
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hd : ∀ y ∈ Icc a x, HasDerivAt (fun y => Q y * g y ^ 2 + g₁ y ^ 2) (Q₁ y * g y ^ 2) y :=
    fun y hy => hasDerivAt_energyQ (hg y (hsub hy)) (hg₁ y (hsub hy)) (hQ y (hsub hy))
  have h := le_of_deriv_nonpos hx.1 (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => hd y (Ioo_subset_Icc_self hy))
    (fun y hy => mul_nonpos_of_nonpos_of_nonneg (hQ₁ y (hsub (Ioo_subset_Icc_self hy))) (sq_nonneg _))
  simpa [ha, ha₁] using h

/-- **Kernel bound, `Q` nonincreasing**: `|g(x)| ≤ Q(x)^{−1/2}` and `|g'(x)| ≤ 1`. -/
theorem abs_kernel_le_of_antitone {g g₁ Q Q₁ : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g₁ x) x) (hg₁ : ∀ x ∈ Icc a b, HasDerivAt g₁ (-(Q x * g x)) x)
    (hQ : ∀ x ∈ Icc a b, HasDerivAt Q (Q₁ x) x) (hQ₁ : ∀ x ∈ Icc a b, Q₁ x ≤ 0)
    (hQ0 : ∀ x ∈ Icc a b, 0 < Q x) (ha : g a = 0) (ha₁ : g₁ a = 1) :
    ∀ x ∈ Icc a b, |g x| ≤ 1 / √(Q x) ∧ |g₁ x| ≤ 1 := by
  intro x hx
  have h := energyQ_le_one hg hg₁ hQ hQ₁ ha ha₁ x hx
  have hq := hQ0 x hx
  have hgq : Q x * g x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (g₁ x)]
  refine ⟨?_, ?_⟩
  · have hs : 0 < √(Q x) := sqrt_pos.mpr hq
    rw [le_div_iff₀ hs, ← abs_of_pos hs, ← abs_mul, abs_le_one_iff_mul_self_le_one]
    calc g x * √(Q x) * (g x * √(Q x)) = Q x * g x ^ 2 := by
          rw [show g x * √(Q x) * (g x * √(Q x)) = g x ^ 2 * (√(Q x) * √(Q x)) by ring,
            mul_self_sqrt hq.le]; ring
      _ ≤ 1 := hgq
  · rw [abs_le_one_iff_mul_self_le_one]
    nlinarith [mul_nonneg hq.le (sq_nonneg (g x))]

/-! ### The Liouville–Green energy `√Q g² + g'²/√Q` -/

/-! ### The constant-weight energy `μg² + g'²/μ` -/

/-! ### The Coulomb amplitude -/

/-- The Coulomb energy `G² + xG'²/(k + x/4)`. -/
def coulombEnergy (k : ℝ) (G G₁ : ℝ → ℝ) (x : ℝ) : ℝ := G x ^ 2 + x * G₁ x ^ 2 / (k + x / 4)

/-- **Its derivative**: for `xG'' + G' + (k + x/4)G = 0`, `E' = −G'²/(k + x/4) − xG'²/(4(k + x/4)²)`. -/
theorem hasDerivAt_coulombEnergy {G G₁ G₂ : ℝ → ℝ} {k x : ℝ} (hk : 0 ≤ k) (hx : 0 < x)
    (hG : HasDerivAt G (G₁ x) x) (hG₁ : HasDerivAt G₁ (G₂ x) x)
    (hode : x * G₂ x + G₁ x + (k + x / 4) * G x = 0) :
    HasDerivAt (coulombEnergy k G G₁)
      (-(G₁ x ^ 2 / (k + x / 4)) - x * G₁ x ^ 2 / (4 * (k + x / 4) ^ 2)) x := by
  have hd : k + x / 4 ≠ 0 := by positivity
  have hD : HasDerivAt (fun y => k + y / 4) (1 / 4) x := ((hasDerivAt_id x).div_const 4).const_add k
  have h := (hG.fun_pow 2).fun_add (((hasDerivAt_id' x).fun_mul (hG₁.fun_pow 2)).fun_div hD hd)
  unfold coulombEnergy
  refine h.congr_deriv ?_
  have e : G₂ x = -(G₁ x + (k + x / 4) * G x) / x := by field_simp; linarith
  rw [e]
  push_cast
  field_simp
  ring

/-- The Coulomb energy is nonincreasing on `(0, ∞)`. -/
theorem coulombEnergy_le {G G₁ G₂ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hG : ∀ x, 0 < x → HasDerivAt G (G₁ x) x) (hG₁ : ∀ x, 0 < x → HasDerivAt G₁ (G₂ x) x)
    (hode : ∀ x, 0 < x → x * G₂ x + G₁ x + (k + x / 4) * G x = 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    coulombEnergy k G G₁ b ≤ coulombEnergy k G G₁ a := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt (coulombEnergy k G G₁)
      (-(G₁ x ^ 2 / (k + x / 4)) - x * G₁ x ^ 2 / (4 * (k + x / 4) ^ 2)) x := fun x hx =>
    hasDerivAt_coulombEnergy hk (by linarith [hx.1]) (hG x (by linarith [hx.1])) (hG₁ x (by linarith [hx.1]))
      (hode x (by linarith [hx.1]))
  refine le_of_deriv_nonpos hab (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Ioo_subset_Icc_self hx)) (fun x hx => ?_)
  have hx0 : 0 < x := by linarith [hx.1]
  have : 0 ≤ G₁ x ^ 2 / (k + x / 4) := by positivity
  have : 0 ≤ x * G₁ x ^ 2 / (4 * (k + x / 4) ^ 2) := by positivity
  linarith

/-- The Coulomb energy tends to `1` at `0⁺` when `G → 1` and `G' → −k` there. -/
theorem tendsto_coulombEnergy {G G₁ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hG0 : Tendsto G (𝓝[>] 0) (𝓝 1))
    (hG₁0 : Tendsto G₁ (𝓝[>] 0) (𝓝 (-k))) : Tendsto (coulombEnergy k G G₁) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun x => G x ^ 2) (𝓝[>] 0) (𝓝 1) := by simpa using hG0.pow 2
  suffices h2 : Tendsto (fun x => x * G₁ x ^ 2 / (k + x / 4)) (𝓝[>] 0) (𝓝 0) by
    have := h1.add h2
    rw [add_zero] at this
    exact this
  rcases hk.eq_or_lt with h0 | hpos
  · subst h0
    have hG₁' : Tendsto (fun x => 4 * G₁ x ^ 2) (𝓝[>] 0) (𝓝 0) := by simpa using (hG₁0.pow 2).const_mul 4
    refine hG₁'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    field_simp
    ring
  · have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hden : Tendsto (fun x : ℝ => k + x / 4) (𝓝[>] 0) (𝓝 (k + 0 / 4)) := (hx.div_const 4).const_add k
    have := (hx.mul (hG₁0.pow 2)).div hden (by simpa using hpos.ne')
    rw [zero_mul, zero_div] at this
    exact this

/-- **`|G| ≤ 1`**: a solution of `xG'' + G' + (k + x/4)G = 0` on `(0, ∞)` with `G → 1`, `G' → −k` at `0⁺`
(`k ≥ 0`) satisfies `|G(x)| ≤ 1` for every `x > 0`. -/
theorem abs_le_one_of_coulomb {G G₁ G₂ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hG : ∀ x, 0 < x → HasDerivAt G (G₁ x) x) (hG₁ : ∀ x, 0 < x → HasDerivAt G₁ (G₂ x) x)
    (hode : ∀ x, 0 < x → x * G₂ x + G₁ x + (k + x / 4) * G x = 0)
    (hG0 : Tendsto G (𝓝[>] 0) (𝓝 1)) (hG₁0 : Tendsto G₁ (𝓝[>] 0) (𝓝 (-k))) {x : ℝ} (hx : 0 < x) :
    |G x| ≤ 1 := by
  have hE : coulombEnergy k G G₁ x ≤ 1 := by
    refine ge_of_tendsto (tendsto_coulombEnergy hk hG0 hG₁0) ?_
    filter_upwards [Ioo_mem_nhdsGT hx] with a ha
    exact coulombEnergy_le hk hG hG₁ hode ha.1 ha.2.le
  have : 0 ≤ x * G₁ x ^ 2 / (k + x / 4) := by positivity
  rw [abs_le_one_iff_mul_self_le_one]
  unfold coulombEnergy at hE
  nlinarith

end Cvs.Upstream.SecondOrderOdeEnergyBounds
