import Mathlib
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.WeilForm.OddPoleTermBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lemma E: the edge remainder in closed form

In `x = c²(ξ² − 1)/σ²`, `σ² = c² − χ`, `ε = σ²/c²`, `ω = w/c²`: `(pA')' = (c²/σ⁴)N/B³`, `f = 2F/(ξσ²B²)`,
`N = N₀ + εxR`; Minkowski and the rational integrals `2/15, 1/5, 1/30, 1/5, 1/3` give, for `t² + ¼ ≤ rc²`,
`r < 1`, `s = σ²/c ≥ 5`: `∫₁²|ρ_t|² ≤ (√(32/15) + εe₁)²/(2cs³) + 2rĪ₂(ε)/(cs) + √(Ī₁Ī₂)/(c²s²)`.
-/

namespace Cvs.Prolate.Mellin.EdgeRemainderClosedForm

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.EdgeGreenIdentity

/-- `e₁ = (2/√5 + r(14/√30 + 32/√5))/(1 − r)³`. -/
noncomputable def e1 (r : ℝ) : ℝ := (2 / √5 + r * (14 / √30 + 32 / √5)) / (1 - r) ^ 3

/-- `Ī₁ = (√(32/15) + e₁)²`. -/
noncomputable def I1bar (r : ℝ) : ℝ := (√(32 / 15) + e1 r) ^ 2

/-- `Ī₂ = 1/(3(1 − r)) + (2(2 + r) + (2 + r)²/2)/(1 − r)⁴`. -/
noncomputable def I2bar (r : ℝ) : ℝ := 1 / (3 * (1 - r)) + (2 * (2 + r) + (2 + r) ^ 2 / 2) / (1 - r) ^ 4

/-- `L_c = log(c/5)/(1 − 5/c)`. -/
noncomputable def Lc (c : ℝ) : ℝ := Real.log (c / 5) / (1 - 5 / c)

/-- Lemma E's majorant of `∫₁²|ρ_t|²` at `s = (c² − χ)/c`. -/
noncomputable def lemmaEBound (c r s : ℝ) : ℝ :=
  (√(32 / 15) + s / c * e1 r) ^ 2 / (2 * c * s ^ 3)
    + 2 * r * (1 / (3 * (1 - r)) + (2 * (2 + r) * (s / c) * Lc c + s / c * (2 + r) ^ 2 / 2) / (1 - r) ^ 4)
      / (c * s)
    + √(I1bar r * I2bar r) / (c ^ 2 * s ^ 2)

/-- `B(x) = 1 + x(1 − ω/ℓ)`, `ℓ = 1 + εx`. -/
noncomputable def Bx (ε ω x : ℝ) : ℝ := 1 + x * (1 - ω / (1 + ε * x))

/-- `N(x)`, with `(pA')' = (c²/σ⁴)N/B³`. -/
noncomputable def Nx (ε ω x : ℝ) : ℝ :=
  -(4 + 6 * ε * x) * (1 - ω / (1 + ε * x) ^ 2) * Bx ε ω x - 8 * ε * x * ω * Bx ε ω x / (1 + ε * x) ^ 2
    + 8 * x * (1 + ε * x) * (1 - ω / (1 + ε * x) ^ 2) ^ 2

/-- `F(x) = 1 − x + ωx/ℓ − 2εx²`, with `f = 2F/(ξσ²B²)`. -/
noncomputable def Fx (ε ω x : ℝ) : ℝ := 1 - x + ω * x / (1 + ε * x) - 2 * ε * x ^ 2

/-- `R(x)`, with `N = N₀ + εxR`. -/
noncomputable def Rx (ε ω x : ℝ) : ℝ :=
  2 * (x - 3) + ω * (-10 + 8 * x - 4 * ε * x + 14 * ε * x ^ 2) / (1 + ε * x) ^ 2
    - 2 * ω ^ 2 * x * (5 + 6 * ε * x + 2 * ε ^ 2 * x ^ 2) / (1 + ε * x) ^ 3

theorem Bx_eq {c χ w ξ : ℝ} (hc : c ≠ 0) (hσ : c ^ 2 - χ ≠ 0) (hξ : ξ ≠ 0) :
    Bx ((c ^ 2 - χ) / c ^ 2) (w / c ^ 2) ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2))
      = DM c χ w ξ / ((c ^ 2 - χ) * ξ ^ 2) := by
  have hl : 1 + (c ^ 2 - χ) / c ^ 2 * ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2)) = ξ ^ 2 := by
    field_simp; ring
  unfold Bx
  rw [hl]
  unfold DM pP qP
  field_simp
  ring

theorem Nx_eq_add (ε ω x : ℝ) (hl : 1 + ε * x ≠ 0) :
    Nx ε ω x = -4 * (1 - ω) * (1 - x * (1 - ω)) + ε * x * Rx ε ω x := by
  unfold Nx Rx Bx
  field_simp
  ring

theorem gEdge_eq {c χ w ξ : ℝ} (hc : c ≠ 0) (hσ : c ^ 2 - χ ≠ 0) (hξ : 0 < ξ) (hD : DM c χ w ξ ≠ 0) :
    gEdge c χ w ξ
      = c ^ 2 / (c ^ 2 - χ) ^ 2 * Nx ((c ^ 2 - χ) / c ^ 2) (w / c ^ 2) ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2))
        / Bx ((c ^ 2 - χ) / c ^ 2) (w / c ^ 2) ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2)) ^ 3 := by
  have hξ0 : ξ ≠ 0 := hξ.ne'
  have hl : 1 + (c ^ 2 - χ) / c ^ 2 * ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2)) = ξ ^ 2 := by
    field_simp; ring
  have hB := Bx_eq (w := w) hc hσ hξ0
  set x := (ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2) with hx
  unfold Nx
  rw [hB, hl]
  have hx' : x = c ^ 2 * (ξ ^ 2 - 1) / (c ^ 2 - χ) := by rw [hx]; field_simp
  rw [hx']
  unfold gEdge dbetaM betaM dDM
  field_simp
  unfold DM pP qP
  ring

theorem fEdge_eq {c χ w ξ : ℝ} (hc : c ≠ 0) (hσ : c ^ 2 - χ ≠ 0) (hξ : 0 < ξ) (hD : DM c χ w ξ ≠ 0) :
    fEdge c χ w ξ
      = 2 * Fx ((c ^ 2 - χ) / c ^ 2) (w / c ^ 2) ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2))
        / (ξ * (c ^ 2 - χ) * Bx ((c ^ 2 - χ) / c ^ 2) (w / c ^ 2) ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2)) ^ 2) := by
  have hξ0 : ξ ≠ 0 := hξ.ne'
  have hl : 1 + (c ^ 2 - χ) / c ^ 2 * ((ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2)) = ξ ^ 2 := by
    field_simp; ring
  have hB := Bx_eq (w := w) hc hσ hξ0
  rw [hB]
  unfold Fx
  rw [hl]
  have hx' : (ξ ^ 2 - 1) / ((c ^ 2 - χ) / c ^ 2) = c ^ 2 * (ξ ^ 2 - 1) / (c ^ 2 - χ) := by field_simp
  rw [hx']
  unfold fEdge betaM
  field_simp
  unfold DM pP qP
  ring

theorem Fx_eq {ε ω x : ℝ} (hl : 1 + ε * x ≠ 0) :
    Fx ε ω x = (1 - (1 - ω) * x) - ε * x ^ 2 * (2 + ω / (1 + ε * x)) := by
  unfold Fx
  have e : ω * x / (1 + ε * x) = ω * x - ε * x ^ 2 * (ω / (1 + ε * x)) := by
    rw [eq_sub_iff_add_eq, mul_div_assoc', ← add_div, div_eq_iff hl]
    ring
  rw [e]
  ring

/-- `B ≥ 1 + (1 − ω)x` for `ε, x ≥ 0`, `ω ≥ 0`. -/
theorem Bx_ge_lin {ε ω x : ℝ} (hε : 0 ≤ ε) (hω0 : 0 ≤ ω) (hx : 0 ≤ x) :
    1 + (1 - ω) * x ≤ Bx ε ω x := by
  have hl : 1 ≤ 1 + ε * x := le_add_of_nonneg_right (mul_nonneg hε hx)
  have h : ω / (1 + ε * x) ≤ ω := div_le_self hω0 hl
  unfold Bx; nlinarith

theorem Bx_ge {ε ω x : ℝ} (hε : 0 ≤ ε) (hω0 : 0 ≤ ω) (hx : 0 ≤ x) :
    (1 - ω) * (1 + x) ≤ Bx ε ω x := by
  have := Bx_ge_lin hε hω0 hx; nlinarith

theorem abs_Rx_le {ε ω x : ℝ} (hε : 0 ≤ ε) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hx : 0 ≤ x) :
    |Rx ε ω x| ≤ 2 * |x - 3| + ω * (14 + 32 * x) := by
  set a := ε * x with ha
  have ha0 : 0 ≤ a := mul_nonneg hε hx
  have hl : 0 < 1 + a := by linarith
  have hA : |-10 + 8 * x - 4 * a + 14 * a * x| / (1 + a) ^ 2 ≤ 14 + 22 * x := by
    rw [div_le_iff₀ (by positivity), abs_le]
    constructor <;> nlinarith [mul_nonneg ha0 hx, mul_nonneg (mul_nonneg ha0 ha0) hx]
  have hB : (5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3 ≤ 5 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg ha0 ha0, mul_nonneg (mul_nonneg ha0 ha0) ha0]
  have hB0 : 0 ≤ (5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3 := by positivity
  have e : Rx ε ω x = 2 * (x - 3) + ω * ((-10 + 8 * x - 4 * a + 14 * a * x) / (1 + a) ^ 2)
      - 2 * ω ^ 2 * x * ((5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3) := by
    unfold Rx; rw [ha]; ring
  rw [e]
  have h1 : |ω * ((-10 + 8 * x - 4 * a + 14 * a * x) / (1 + a) ^ 2)| ≤ ω * (14 + 22 * x) := by
    rw [abs_mul, abs_of_nonneg hω0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + a) ^ 2)]
    exact mul_le_mul_of_nonneg_left hA hω0
  have h2 : |2 * ω ^ 2 * x * ((5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3)| ≤ ω * (10 * x) := by
    rw [abs_of_nonneg (by positivity)]
    have : ω ^ 2 ≤ ω := by nlinarith
    calc 2 * ω ^ 2 * x * ((5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3) ≤ 2 * ω * x * 5 := by
          gcongr
      _ = ω * (10 * x) := by ring
  calc |2 * (x - 3) + ω * ((-10 + 8 * x - 4 * a + 14 * a * x) / (1 + a) ^ 2)
        - 2 * ω ^ 2 * x * ((5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3)|
      ≤ |2 * (x - 3)| + |ω * ((-10 + 8 * x - 4 * a + 14 * a * x) / (1 + a) ^ 2)|
        + |2 * ω ^ 2 * x * ((5 + 6 * a + 2 * a ^ 2) / (1 + a) ^ 3)| := by
        refine (abs_sub _ _).trans ?_
        gcongr; exact abs_add_le _ _
    _ ≤ 2 * |x - 3| + ω * (14 + 22 * x) + ω * (10 * x) := by
        rw [abs_mul, abs_two]; linarith
    _ = 2 * |x - 3| + ω * (14 + 32 * x) := by ring

/-- An antiderivative `F` of `f` on `[0, M]` with `F(M) ≤ 0` and `F(0) = −V` bounds `∫₀^M f ≤ V`. -/
theorem integral_le_of_antideriv {f F : ℝ → ℝ} {M V : ℝ} (hM : 0 ≤ M)
    (hd : ∀ x ∈ uIcc (0 : ℝ) M, HasDerivAt F (f x) x) (hc : ContinuousOn f (uIcc 0 M))
    (hFM : F M ≤ 0) (hF0 : F 0 = -V) : ∫ x in (0 : ℝ)..M, f x ≤ V := by
  have := hM
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]; linarith

theorem pos_of_mem_uIcc {k M x : ℝ} (hk : 0 ≤ k) (hM : 0 ≤ M) (hx : x ∈ uIcc (0 : ℝ) M) :
    0 < 1 + k * x := by
  rw [uIcc_of_le hM] at hx; nlinarith [hx.1]

theorem hasDerivAt_lin_pow (k x : ℝ) (n : ℕ) :
    HasDerivAt (fun x => (1 + k * x) ^ n) (n * (1 + k * x) ^ (n - 1) * k) x := by
  have hl : HasDerivAt (fun x => 1 + k * x) k x := by
    simpa using ((hasDerivAt_id' x).const_mul k).const_add 1
  exact hl.pow n

theorem integral_comp_sub_sq {ε : ℝ} (hε : 0 < ε) {G : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 (3 / ε))) :
    ∫ ξ in (1 : ℝ)..2, G ((ξ ^ 2 - 1) / ε) * (2 * ξ / ε) = ∫ x in (0 : ℝ)..3 / ε, G x := by
  have hd : ∀ x ∈ uIcc (1 : ℝ) 2, HasDerivAt (fun ξ : ℝ => (ξ ^ 2 - 1) / ε) (2 * x / ε) x := by
    intro x _
    have h := ((hasDerivAt_pow 2 x).sub_const 1).div_const ε
    refine h.congr_deriv ?_
    push_cast; ring
  have hc : ContinuousOn (fun x : ℝ => 2 * x / ε) (uIcc 1 2) := by fun_prop
  have himg : (fun ξ : ℝ => (ξ ^ 2 - 1) / ε) '' uIcc 1 2 ⊆ Icc 0 (3 / ε) := by
    rintro _ ⟨ξ, hξ, rfl⟩
    rw [uIcc_of_le (by norm_num)] at hξ
    constructor
    · apply div_nonneg _ hε.le; nlinarith [hξ.1]
    · apply div_le_div_of_nonneg_right _ hε.le; nlinarith [hξ.1, hξ.2]
  have h := intervalIntegral.integral_comp_mul_deriv' hd hc (hG.mono himg)
  simp only [Function.comp_def] at h
  rw [h]
  norm_num

theorem integral_lead_le {k M : ℝ} (hk : 0 < k) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, (1 - k * x) ^ 2 / (1 + k * x) ^ 6 ≤ 2 / (15 * k) := by
  have hpos := fun x (hx : x ∈ uIcc (0 : ℝ) M) => pos_of_mem_uIcc hk.le hM hx
  refine integral_le_of_antideriv (F := fun x =>
    -(5 * (1 + k * x) ^ 2 - 15 * (1 + k * x) + 12) / (15 * k * (1 + k * x) ^ 5)) hM ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hn : HasDerivAt (fun x => -(5 * (1 + k * x) ^ 2 - 15 * (1 + k * x) + 12))
        (-(5 * (2 * (1 + k * x) * k) - 15 * k)) x := by
      have h := ((((hasDerivAt_lin_pow k x 2).const_mul 5).sub
        ((hasDerivAt_lin_pow k x 1).const_mul 15)).add_const 12).neg
      simp only [pow_one] at h
      refine h.congr_deriv ?_; push_cast; ring
    have hden : HasDerivAt (fun x => 15 * k * (1 + k * x) ^ 5) (15 * k * (5 * (1 + k * x) ^ 4 * k)) x := by
      refine ((hasDerivAt_lin_pow k x 5).const_mul (15 * k)).congr_deriv ?_; push_cast; ring
    refine (hn.div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun x : ℝ => (1 - k * x) ^ 2 := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + k * x) ^ 6 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 6 (hpos x hx).ne'
  · have hU : 0 < 1 + k * M := by nlinarith
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [sq_nonneg (1 + k * M - 3 / 2)]
  · field_simp; ring

theorem integral_x2_x3_le {M : ℝ} (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, x ^ 2 * (x - 3) ^ 2 / (1 + x) ^ 6 ≤ 1 / 5 := by
  have hpos : ∀ x ∈ uIcc (0 : ℝ) M, 0 < 1 + x := fun x hx => by
    simpa using pos_of_mem_uIcc (k := 1) zero_le_one hM hx
  refine integral_le_of_antideriv (F := fun x =>
    -(5 * x ^ 4 - 5 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1) / (5 * (1 + x) ^ 5)) hM ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hn : HasDerivAt (fun x => -(5 * x ^ 4 - 5 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1))
        (-(20 * x ^ 3 - 15 * x ^ 2 + 20 * x + 5)) x := by
      have h := ((((((hasDerivAt_pow 4 x).const_mul 5).sub ((hasDerivAt_pow 3 x).const_mul 5)).add
        ((hasDerivAt_pow 2 x).const_mul 10)).add ((hasDerivAt_id' x).const_mul 5)).add_const 1).neg
      refine h.congr_deriv ?_; push_cast; ring
    have hden : HasDerivAt (fun x => 5 * (1 + x) ^ 5) (5 * (5 * (1 + x) ^ 4)) x := by
      refine ((hasDerivAt_lin_pow 1 x 5).const_mul 5).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · push_cast; ring
      · exact Filter.Eventually.of_forall fun y => by simp
    refine (hn.div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun x : ℝ => x ^ 2 * (x - 3) ^ 2 := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + x) ^ 6 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 6 (hpos x hx).ne'
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [sq_nonneg (M ^ 2 - M / 2), sq_nonneg M, pow_nonneg hM 3]
  · norm_num

theorem integral_x2_le {M : ℝ} (hM : 0 ≤ M) : ∫ x in (0 : ℝ)..M, x ^ 2 / (1 + x) ^ 6 ≤ 1 / 30 := by
  have hpos : ∀ x ∈ uIcc (0 : ℝ) M, 0 < 1 + x := fun x hx => by
    simpa using pos_of_mem_uIcc (k := 1) zero_le_one hM hx
  refine integral_le_of_antideriv (F := fun x => -(10 * x ^ 2 + 5 * x + 1) / (30 * (1 + x) ^ 5)) hM
    ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hn : HasDerivAt (fun x => -(10 * x ^ 2 + 5 * x + 1)) (-(20 * x + 5)) x := by
      have h := ((((hasDerivAt_pow 2 x).const_mul 10).add ((hasDerivAt_id' x).const_mul 5)).add_const 1).neg
      refine h.congr_deriv ?_; push_cast; ring
    have hden : HasDerivAt (fun x => 30 * (1 + x) ^ 5) (30 * (5 * (1 + x) ^ 4)) x := by
      refine ((hasDerivAt_lin_pow 1 x 5).const_mul 30).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · push_cast; ring
      · exact Filter.Eventually.of_forall fun y => by simp
    refine (hn.div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun x : ℝ => x ^ 2 := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + x) ^ 6 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 6 (hpos x hx).ne'
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [sq_nonneg M]
  · norm_num

theorem integral_x4_le {M : ℝ} (hM : 0 ≤ M) : ∫ x in (0 : ℝ)..M, x ^ 4 / (1 + x) ^ 6 ≤ 1 / 5 := by
  have hpos : ∀ x ∈ uIcc (0 : ℝ) M, 0 < 1 + x := fun x hx => by
    simpa using pos_of_mem_uIcc (k := 1) zero_le_one hM hx
  refine integral_le_of_antideriv (F := fun x =>
    -(5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1) / (5 * (1 + x) ^ 5)) hM ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hn : HasDerivAt (fun x => -(5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1))
        (-(20 * x ^ 3 + 30 * x ^ 2 + 20 * x + 5)) x := by
      have h := ((((((hasDerivAt_pow 4 x).const_mul 5).add ((hasDerivAt_pow 3 x).const_mul 10)).add
        ((hasDerivAt_pow 2 x).const_mul 10)).add ((hasDerivAt_id' x).const_mul 5)).add_const 1).neg
      refine h.congr_deriv ?_; push_cast; ring
    have hden : HasDerivAt (fun x => 5 * (1 + x) ^ 5) (5 * (5 * (1 + x) ^ 4)) x := by
      refine ((hasDerivAt_lin_pow 1 x 5).const_mul 5).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · push_cast; ring
      · exact Filter.Eventually.of_forall fun y => by simp
    refine (hn.div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun x : ℝ => x ^ 4 := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + x) ^ 6 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 6 (hpos x hx).ne'
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [sq_nonneg M, pow_nonneg hM 3, pow_nonneg hM 4]
  · norm_num

theorem integral_lead2_le {k M : ℝ} (hk : 0 < k) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, (1 - k * x) ^ 2 / (1 + k * x) ^ 4 ≤ 1 / (3 * k) := by
  have hpos := fun x (hx : x ∈ uIcc (0 : ℝ) M) => pos_of_mem_uIcc hk.le hM hx
  refine integral_le_of_antideriv (F := fun x => -(3 * k ^ 2 * x ^ 2 + 1) / (3 * k * (1 + k * x) ^ 3))
    hM ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hn : HasDerivAt (fun x => -(3 * k ^ 2 * x ^ 2 + 1)) (-(6 * k ^ 2 * x)) x := by
      have h := (((hasDerivAt_pow 2 x).const_mul (3 * k ^ 2)).add_const 1).neg
      refine h.congr_deriv ?_; push_cast; ring
    have hden : HasDerivAt (fun x => 3 * k * (1 + k * x) ^ 3) (3 * k * (3 * (1 + k * x) ^ 2 * k)) x := by
      refine ((hasDerivAt_lin_pow k x 3).const_mul (3 * k)).congr_deriv ?_; push_cast; ring
    refine (hn.div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun x : ℝ => (1 - k * x) ^ 2 := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + k * x) ^ 4 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 4 (hpos x hx).ne'
  · have hU : 0 < 1 + k * M := by nlinarith
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [sq_nonneg (k * M)]
  · field_simp; ring

theorem integral_inv_cube_le {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, 1 / (1 + ε * x) ^ 3 ≤ 1 / (2 * ε) := by
  have hpos := fun x (hx : x ∈ uIcc (0 : ℝ) M) => pos_of_mem_uIcc hε.le hM hx
  refine integral_le_of_antideriv (F := fun x => -1 / (2 * ε * (1 + ε * x) ^ 2)) hM ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hden : HasDerivAt (fun x => 2 * ε * (1 + ε * x) ^ 2) (2 * ε * (2 * (1 + ε * x) * ε)) x := by
      refine ((hasDerivAt_lin_pow ε x 2).const_mul (2 * ε)).congr_deriv ?_; push_cast; ring
    refine ((hasDerivAt_const x (-1 : ℝ)).div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun _ : ℝ => (1 : ℝ) := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + ε * x) ^ 3 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 3 (hpos x hx).ne'
  · have hU : 0 < 1 + ε * M := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  · field_simp; ring

/-- `∫₀^M dx/(1 + εx)² ≤ 1/ε`. -/
theorem integral_inv_sq_le {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, 1 / (1 + ε * x) ^ 2 ≤ 1 / ε := by
  have hpos := fun x (hx : x ∈ uIcc (0 : ℝ) M) => pos_of_mem_uIcc hε.le hM hx
  refine integral_le_of_antideriv (F := fun x => -1 / (ε * (1 + ε * x))) hM ?_ ?_ ?_ ?_
  · intro x hx
    have hu := hpos x hx
    have hden : HasDerivAt (fun x => ε * (1 + ε * x)) (ε * ε) x := by
      refine ((hasDerivAt_lin_pow ε x 1).const_mul ε).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · push_cast; ring
      · exact Filter.Eventually.of_forall fun y => by simp
    refine ((hasDerivAt_const x (-1 : ℝ)).div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  · have hn : Continuous fun _ : ℝ => (1 : ℝ) := by fun_prop
    have hd : Continuous fun x : ℝ => (1 + ε * x) ^ 2 := by fun_prop
    exact hn.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero 2 (hpos x hx).ne'
  · have hU : 0 < 1 + ε * M := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  · field_simp; ring

theorem continuousOn_inv_mul {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) :
    ContinuousOn (fun x => 1 / ((1 + x) * (1 + ε * x))) (uIcc 0 M) := by
  have hd : Continuous fun x : ℝ => (1 + x) * (1 + ε * x) := by fun_prop
  refine continuousOn_const.div₀ hd.continuousOn fun x hx => ?_
  have h1 := pos_of_mem_uIcc zero_le_one hM hx
  have h2 := pos_of_mem_uIcc hε hM hx
  rw [one_mul] at h1
  positivity

theorem integral_inv_mul_le_log {ε ε₀ M : ℝ} (h0 : 0 < ε₀) (h1 : ε₀ < 1) (hε : ε₀ ≤ ε) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x)) ≤ Real.log (1 / ε₀) / (1 - ε₀) := by
  have hpos : ∀ {k}, 0 ≤ k → ∀ x ∈ uIcc (0 : ℝ) M, 0 < 1 + k * x := fun hk x hx => pos_of_mem_uIcc hk hM hx
  have hmono : ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x))
      ≤ ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε₀ * x)) := by
    refine integral_mono_on hM (continuousOn_inv_mul (h0.le.trans hε) hM).intervalIntegrable
      (continuousOn_inv_mul h0.le hM).intervalIntegrable fun x hx => ?_
    have hx' : x ∈ uIcc (0 : ℝ) M := by rw [uIcc_of_le hM]; exact hx
    have a := hpos zero_le_one x hx'
    rw [one_mul] at a
    have b := hpos h0.le x hx'
    have hx0 : 0 ≤ x := hx.1
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith) a.le
  refine hmono.trans ?_
  have hd : ∀ x ∈ uIcc (0 : ℝ) M, HasDerivAt
      (fun x => (Real.log (1 + x) - Real.log (1 + ε₀ * x)) / (1 - ε₀)) (1 / ((1 + x) * (1 + ε₀ * x))) x := by
    intro x hx
    have a := hpos zero_le_one x hx
    rw [one_mul] at a
    have b := hpos h0.le x hx
    have ha : HasDerivAt (fun x => 1 + x) 1 x := by simpa using (hasDerivAt_id' x).const_add 1
    have hb : HasDerivAt (fun x => 1 + ε₀ * x) ε₀ x := by
      simpa using ((hasDerivAt_id' x).const_mul ε₀).const_add 1
    have h := ((ha.log a.ne').sub (hb.log b.ne')).div_const (1 - ε₀)
    refine h.congr_deriv ?_
    have : (1 : ℝ) - ε₀ ≠ 0 := by linarith
    have b' : 1 + x * ε₀ ≠ 0 := by rw [mul_comm]; exact b.ne'
    have a' : 1 + x ≠ 0 := a.ne'
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hd (continuousOn_inv_mul h0.le hM).intervalIntegrable]
  simp only [mul_zero, add_zero, Real.log_one, sub_zero, zero_div]
  have hA : 0 < 1 + ε₀ * M := by positivity
  rw [← Real.log_div (by positivity) hA.ne']
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ hA h0]
  nlinarith

theorem mul_integral_inv_mul_le_one {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M) :
    ε * ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x)) ≤ 1 := by
  have h : ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x)) ≤ ∫ x in (0 : ℝ)..M, 1 / (1 + ε * x) ^ 2 := by
    refine integral_mono_on hM (continuousOn_inv_mul hε0.le hM).intervalIntegrable
      (ContinuousOn.intervalIntegrable (ContinuousOn.div₀ continuousOn_const
          ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn
        fun x hx => pow_ne_zero 2 (pos_of_mem_uIcc hε0.le hM hx).ne')) fun x hx => ?_
    have hx0 : 0 ≤ x := hx.1
    have b : 0 < 1 + ε * x := by positivity
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_right (by nlinarith) b.le
  calc ε * ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x)) ≤ ε * (1 / ε) :=
        mul_le_mul_of_nonneg_left (h.trans (integral_inv_sq_le hε0 hM)) hε0.le
    _ = 1 := by field_simp

/-- Minkowski on `[0, M]`: `∫p² ≤ a²`, `∫q² ≤ b²` give `∫(p + q)² ≤ (a + b)²` (Cvs.WeilForm.OddPoleTermBound Cauchy–Schwarz). -/
theorem integral_add_sq_le {p q : ℝ → ℝ} {M a b : ℝ} (hM : 0 ≤ M) (hp : ContinuousOn p (uIcc 0 M))
    (hq : ContinuousOn q (uIcc 0 M)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpa : ∫ x in (0 : ℝ)..M, p x ^ 2 ≤ a ^ 2) (hqb : ∫ x in (0 : ℝ)..M, q x ^ 2 ≤ b ^ 2) :
    ∫ x in (0 : ℝ)..M, (p x + q x) ^ 2 ≤ (a + b) ^ 2 := by
  have i1 : IntervalIntegrable (fun x => p x ^ 2) MeasureTheory.volume 0 M := (hp.pow 2).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => q x ^ 2) MeasureTheory.volume 0 M := (hq.pow 2).intervalIntegrable
  have i12 : IntervalIntegrable (fun x => p x * q x) MeasureTheory.volume 0 M :=
    (hp.mul hq).intervalIntegrable
  have e : (fun x => (p x + q x) ^ 2) = fun x => (p x ^ 2 + 2 * (p x * q x)) + q x ^ 2 := by
    funext x; ring
  rw [e, integral_add (i1.add (i12.const_mul 2)) i2, integral_add i1 (i12.const_mul 2),
    integral_const_mul]
  have cs := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le hM i1 i2 i12
  have hP : 0 ≤ ∫ x in (0 : ℝ)..M, p x ^ 2 := integral_nonneg hM fun x _ => sq_nonneg _
  have hQ : 0 ≤ ∫ x in (0 : ℝ)..M, q x ^ 2 := integral_nonneg hM fun x _ => sq_nonneg _
  have h2 : (∫ x in (0 : ℝ)..M, p x * q x) ^ 2 ≤ (a * b) ^ 2 := by
    rw [mul_pow]; exact cs.trans (mul_le_mul hpa hqb hQ (sq_nonneg a))
  have h3 := (abs_le_of_sq_le_sq' h2 (mul_nonneg ha hb)).2
  nlinarith

theorem continuousOn_gEdge {c χ w b : ℝ} (hχ : χ < c ^ 2) (hw : w ≤ c ^ 2) :
    ContinuousOn (gEdge c χ w) (Icc 1 b) := by
  have hD : ∀ ξ ∈ Icc (1 : ℝ) b, DM c χ w ξ ≠ 0 := fun ξ hξ => (DM_pos_of_le hχ hw hξ.1).ne'
  have hDc : ContinuousOn (DM c χ w) (Icc 1 b) := (continuous_DM c χ w).continuousOn
  have hdD : ContinuousOn (dDM c χ w) (Icc 1 b) := Continuous.continuousOn (by unfold dDM qP; fun_prop)
  have hp : ContinuousOn pP (Icc 1 b) := Continuous.continuousOn (by unfold pP; fun_prop)
  have hβ : ContinuousOn (betaM c χ w) (Icc 1 b) :=
    Cvs.Prolate.Mellin.GreenBoundaryBound.continuousOn_betaM fun ξ hξ => DM_pos_of_le hχ hw hξ.1
  have hdβ : ContinuousOn (dbetaM c χ w) (Icc 1 b) := by
    unfold dbetaM
    have h1 : Continuous fun ξ : ℝ => -(2 * (5 * c ^ 2 * ξ ^ 4 - w)) := by fun_prop
    have h2 : Continuous fun ξ : ℝ => 4 * ξ * (c ^ 2 * ξ ^ 4 - w) := by fun_prop
    exact ContinuousOn.add (ContinuousOn.div₀ h1.continuousOn (hDc.pow 2)
      fun ξ hξ => pow_ne_zero 2 (hD ξ hξ))
      (ContinuousOn.div₀ (h2.continuousOn.mul hdD) (hDc.pow 3) fun ξ hξ => pow_ne_zero 3 (hD ξ hξ))
  unfold gEdge
  exact ((continuousOn_const.mul continuousOn_id).mul hβ).add (hp.mul hdβ)

theorem continuousOn_fEdge {c χ w b : ℝ} (hχ : χ < c ^ 2) (hw : w ≤ c ^ 2) :
    ContinuousOn (fEdge c χ w) (Icc 1 b) := by
  have hD : ∀ ξ ∈ Icc (1 : ℝ) b, DM c χ w ξ ≠ 0 := fun ξ hξ => (DM_pos_of_le hχ hw hξ.1).ne'
  have hDc : ContinuousOn (DM c χ w) (Icc 1 b) := (continuous_DM c χ w).continuousOn
  have hp : ContinuousOn pP (Icc 1 b) := Continuous.continuousOn (by unfold pP; fun_prop)
  have hβ : ContinuousOn (betaM c χ w) (Icc 1 b) :=
    Cvs.Prolate.Mellin.GreenBoundaryBound.continuousOn_betaM fun ξ hξ => DM_pos_of_le hχ hw hξ.1
  unfold fEdge
  exact ((continuousOn_const.mul hp).mul hβ).add ((continuousOn_const.mul continuousOn_id).div hDc hD)

/-- Transfer to `x = (ξ² − 1)/ε`: a pointwise majorant `K·G(x)·dx/dξ` on `[1, 2]` gives `∫₁² f ≤ K∫₀^{3/ε} G`. -/
theorem integral_le_of_sub_sq {ε K : ℝ} (hε : 0 < ε) {f G : ℝ → ℝ} (hf : ContinuousOn f (Icc 1 2))
    (hG : ContinuousOn G (Icc 0 (3 / ε)))
    (h : ∀ ξ ∈ Icc (1 : ℝ) 2, f ξ ≤ K * (G ((ξ ^ 2 - 1) / ε) * (2 * ξ / ε))) :
    ∫ ξ in (1 : ℝ)..2, f ξ ≤ K * ∫ x in (0 : ℝ)..3 / ε, G x := by
  have hmap : MapsTo (fun ξ : ℝ => (ξ ^ 2 - 1) / ε) (Icc 1 2) (Icc 0 (3 / ε)) := by
    intro ξ hξ
    constructor
    · apply div_nonneg _ hε.le; nlinarith [hξ.1]
    · apply div_le_div_of_nonneg_right _ hε.le; nlinarith [hξ.1, hξ.2]
  have hc : ContinuousOn (fun ξ => G ((ξ ^ 2 - 1) / ε) * (2 * ξ / ε)) (Icc 1 2) :=
    (hG.comp (by fun_prop) hmap).mul (by fun_prop)
  rw [← integral_comp_sub_sq hε hG, ← integral_const_mul]
  refine integral_mono_on (by norm_num) ?_ ?_ h
  · exact hf.intervalIntegrable_of_Icc (by norm_num)
  · exact (continuousOn_const.mul hc).intervalIntegrable_of_Icc (by norm_num)

/-- Pointwise `N²/(ℓB⁶) ≤ (4k|1 − kx|/(1 + kx)³ + (ε/k³)x(2|x − 3| + ω(14 + 32x))/(1 + x)³)²`,
`k = 1 − ω`, split for Minkowski. -/
theorem sq_Nx_div_le {ε ω x : ℝ} (hε : 0 ≤ ε) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hx : 0 ≤ x) :
    Nx ε ω x ^ 2 / ((1 + ε * x) * Bx ε ω x ^ 6)
      ≤ (4 * (1 - ω) * |1 - (1 - ω) * x| / (1 + (1 - ω) * x) ^ 3
        + (2 * ε / (1 - ω) ^ 3 * (x * |x - 3| / (1 + x) ^ 3)
          + (14 * ε * ω / (1 - ω) ^ 3 * (x / (1 + x) ^ 3)
            + 32 * ε * ω / (1 - ω) ^ 3 * (x ^ 2 / (1 + x) ^ 3)))) ^ 2 := by
  set k := 1 - ω with hk
  have hk0 : 0 < k := by linarith
  have hL : 1 ≤ 1 + ε * x := le_add_of_nonneg_right (mul_nonneg hε hx)
  have hB1 : 1 + k * x ≤ Bx ε ω x := by have := Bx_ge_lin hε hω0 hx; rw [hk]; linarith
  have hB2 : k * (1 + x) ≤ Bx ε ω x := Bx_ge hε hω0 hx
  have hkx : 0 < 1 + k * x := by positivity
  have hB : 0 < Bx ε ω x := lt_of_lt_of_le hkx hB1
  set S := 2 * |x - 3| + ω * (14 + 32 * x) with hS
  have hS0 : 0 ≤ S := by positivity
  have hN : |Nx ε ω x| ≤ 4 * k * |1 - k * x| + ε * x * S := by
    rw [Nx_eq_add ε ω x (by linarith)]
    refine (abs_add_le _ _).trans ?_
    have e1 : |-4 * (1 - ω) * (1 - x * (1 - ω))| = 4 * k * |1 - k * x| := by
      rw [show -4 * (1 - ω) * (1 - x * (1 - ω)) = -(4 * k) * (1 - k * x) by rw [hk]; ring, abs_mul, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 4 * k)]
    rw [e1, abs_mul, abs_of_nonneg (mul_nonneg hε hx)]
    have := abs_Rx_le hε hω0 hω1.le hx
    have h0 : 0 ≤ ε * x := mul_nonneg hε hx
    nlinarith
  have hq : |Nx ε ω x| / Bx ε ω x ^ 3
      ≤ 4 * k * |1 - k * x| / (1 + k * x) ^ 3 + ε * x * S / (k * (1 + x)) ^ 3 := by
    calc |Nx ε ω x| / Bx ε ω x ^ 3 ≤ (4 * k * |1 - k * x| + ε * x * S) / Bx ε ω x ^ 3 := by gcongr
      _ = 4 * k * |1 - k * x| / Bx ε ω x ^ 3 + ε * x * S / Bx ε ω x ^ 3 := add_div _ _ _
      _ ≤ _ := by gcongr
  have e : ε * x * S / (k * (1 + x)) ^ 3
      = 2 * ε / k ^ 3 * (x * |x - 3| / (1 + x) ^ 3)
        + (14 * ε * ω / k ^ 3 * (x / (1 + x) ^ 3) + 32 * ε * ω / k ^ 3 * (x ^ 2 / (1 + x) ^ 3)) := by
    rw [hS]; field_simp
  rw [e] at hq
  have h6 : Nx ε ω x ^ 2 / ((1 + ε * x) * Bx ε ω x ^ 6) ≤ (|Nx ε ω x| / Bx ε ω x ^ 3) ^ 2 := by
    rw [div_pow, sq_abs, ← pow_mul]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (le_mul_of_one_le_left (by positivity) hL)
  exact h6.trans (pow_le_pow_left₀ (by positivity) hq 2)

theorem continuousOn_frac {k M : ℝ} {n : ℕ} (hk : 0 ≤ k) (hM : 0 ≤ M) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun x => g x / (1 + k * x) ^ n) (uIcc 0 M) := by
  have hd : Continuous fun x : ℝ => (1 + k * x) ^ n := by fun_prop
  exact hg.continuousOn.div₀ hd.continuousOn fun x hx => pow_ne_zero n (pos_of_mem_uIcc hk hM hx).ne'

/-- The `L²(0, M)` Minkowski bound on the majorant of `N/(√ℓB³)`. -/
theorem integral_Nx_major_le {ε ω M : ℝ} (hε : 0 ≤ ε) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, (4 * (1 - ω) * |1 - (1 - ω) * x| / (1 + (1 - ω) * x) ^ 3
        + (2 * ε / (1 - ω) ^ 3 * (x * |x - 3| / (1 + x) ^ 3)
          + (14 * ε * ω / (1 - ω) ^ 3 * (x / (1 + x) ^ 3)
            + 32 * ε * ω / (1 - ω) ^ 3 * (x ^ 2 / (1 + x) ^ 3)))) ^ 2
      ≤ (√(32 / 15) + ε * ((2 / √5 + ω * (14 / √30 + 32 / √5)) / (1 - ω) ^ 3)) ^ 2 := by
  set k := 1 - ω with hk
  have hk0 : 0 < k := by linarith
  have hk1 : k ≤ 1 := by linarith
  have c1 : ContinuousOn (fun x => (1 : ℝ) * x) (uIcc 0 M) := by fun_prop
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h30 : √30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  have h5p : 0 < √5 := by positivity
  have h30p : 0 < √30 := by positivity
  -- the four pieces
  have hc0 : ContinuousOn (fun x => 4 * k * |1 - k * x| / (1 + k * x) ^ 3) (uIcc 0 M) :=
    continuousOn_frac (g := fun x => 4 * k * |1 - k * x|) hk0.le hM (by fun_prop)
  have hfr : ∀ {g : ℝ → ℝ}, Continuous g → ContinuousOn (fun x => g x / (1 + x) ^ 3) (uIcc 0 M) :=
    fun hg => by simpa using continuousOn_frac (k := 1) (n := 3) zero_le_one hM hg
  have hc1 : ContinuousOn (fun x => 2 * ε / k ^ 3 * (x * |x - 3| / (1 + x) ^ 3)) (uIcc 0 M) :=
    continuousOn_const.mul (hfr (g := fun x => x * |x - 3|) (by fun_prop))
  have hc2 : ContinuousOn (fun x => 14 * ε * ω / k ^ 3 * (x / (1 + x) ^ 3)) (uIcc 0 M) :=
    continuousOn_const.mul (hfr (by fun_prop))
  have hc3 : ContinuousOn (fun x => 32 * ε * ω / k ^ 3 * (x ^ 2 / (1 + x) ^ 3)) (uIcc 0 M) :=
    continuousOn_const.mul (hfr (continuous_pow 2))
  have b0 : ∫ x in (0 : ℝ)..M, (4 * k * |1 - k * x| / (1 + k * x) ^ 3) ^ 2 ≤ √(32 / 15) ^ 2 := by
    have e : (fun x => (4 * k * |1 - k * x| / (1 + k * x) ^ 3) ^ 2)
        = fun x => 16 * k ^ 2 * ((1 - k * x) ^ 2 / (1 + k * x) ^ 6) := by
      funext x; rw [div_pow, mul_pow, sq_abs]; ring
    rw [e, integral_const_mul, Real.sq_sqrt (by norm_num)]
    have := integral_lead_le hk0 hM
    calc 16 * k ^ 2 * ∫ x in (0 : ℝ)..M, (1 - k * x) ^ 2 / (1 + k * x) ^ 6 ≤ 16 * k ^ 2 * (2 / (15 * k)) := by
          gcongr
      _ = 32 * k / 15 := by field_simp; ring
      _ ≤ 32 / 15 := by linarith
  have b1 : ∫ x in (0 : ℝ)..M, (2 * ε / k ^ 3 * (x * |x - 3| / (1 + x) ^ 3)) ^ 2 ≤ (2 * ε / k ^ 3 / √5) ^ 2 := by
    have e : (fun x => (2 * ε / k ^ 3 * (x * |x - 3| / (1 + x) ^ 3)) ^ 2)
        = fun x => (2 * ε / k ^ 3) ^ 2 * (x ^ 2 * (x - 3) ^ 2 / (1 + x) ^ 6) := by
      funext x; rw [mul_pow, div_pow (x * |x - 3|), mul_pow x, sq_abs]; ring
    rw [e, integral_const_mul, div_pow _ √5, h5]
    have := integral_x2_x3_le hM
    calc _ ≤ (2 * ε / k ^ 3) ^ 2 * (1 / 5) := by gcongr
      _ = _ := by ring
  have b2 : ∫ x in (0 : ℝ)..M, (14 * ε * ω / k ^ 3 * (x / (1 + x) ^ 3)) ^ 2
      ≤ (14 * ε * ω / k ^ 3 / √30) ^ 2 := by
    have e : (fun x => (14 * ε * ω / k ^ 3 * (x / (1 + x) ^ 3)) ^ 2)
        = fun x => (14 * ε * ω / k ^ 3) ^ 2 * (x ^ 2 / (1 + x) ^ 6) := by
      funext x; rw [mul_pow, div_pow x]; ring
    rw [e, integral_const_mul, div_pow _ √30, h30]
    have := integral_x2_le hM
    calc _ ≤ (14 * ε * ω / k ^ 3) ^ 2 * (1 / 30) := by gcongr
      _ = _ := by ring
  have b3 : ∫ x in (0 : ℝ)..M, (32 * ε * ω / k ^ 3 * (x ^ 2 / (1 + x) ^ 3)) ^ 2
      ≤ (32 * ε * ω / k ^ 3 / √5) ^ 2 := by
    have e : (fun x => (32 * ε * ω / k ^ 3 * (x ^ 2 / (1 + x) ^ 3)) ^ 2)
        = fun x => (32 * ε * ω / k ^ 3) ^ 2 * (x ^ 4 / (1 + x) ^ 6) := by
      funext x; rw [mul_pow, div_pow (x ^ 2)]; ring
    rw [e, integral_const_mul, div_pow _ √5, h5]
    have := integral_x4_le hM
    calc _ ≤ (32 * ε * ω / k ^ 3) ^ 2 * (1 / 5) := by gcongr
      _ = _ := by ring
  have m23 := integral_add_sq_le hM hc2 hc3 (by positivity) (by positivity) b2 b3
  have m123 := integral_add_sq_le hM hc1 (hc2.add hc3) (by positivity) (by positivity) b1 m23
  have m := integral_add_sq_le hM hc0 (hc1.add (hc2.add hc3)) (by positivity) (by positivity) b0 m123
  refine m.trans_eq (congrArg (· ^ 2) ?_)
  ring

theorem e1_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : 0 ≤ e1 r := by
  unfold e1; have : 0 < 1 - r := by linarith
  positivity

/-- `(2/√5 + ω(14/√30 + 32/√5))/(1 − ω)³ ≤ e₁(r)` for `0 ≤ ω ≤ r < 1`. -/
theorem e1_mono {ω r : ℝ} (hω0 : 0 ≤ ω) (hωr : ω ≤ r) (hr : r < 1) :
    (2 / √5 + ω * (14 / √30 + 32 / √5)) / (1 - ω) ^ 3 ≤ e1 r := by
  unfold e1
  have h1 : 0 < 1 - r := by linarith
  have hr0 : 0 ≤ r := hω0.trans hωr
  have h2 : 0 < 1 - ω := by linarith
  apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
  exact pow_le_pow_left₀ h1.le (by linarith) 3

/-- **E1**: `∫₁² g²/ξ ≤ (√(32/15) + εe₁)²c²/(2σ⁶)`, `σ² = c² − χ`, `ε = σ²/c²`, for `w ≤ rc²`, `r < 1`. -/
theorem integral_gEdge_sq_le {c χ w r : ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hw0 : 0 ≤ w) (hr : r < 1)
    (hw : w ≤ r * c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, gEdge c χ w ξ ^ 2 / ξ
      ≤ (√(32 / 15) + (c ^ 2 - χ) / c ^ 2 * e1 r) ^ 2 * c ^ 2 / (2 * (c ^ 2 - χ) ^ 3) := by
  have hσ : 0 < c ^ 2 - χ := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hε : 0 < (c ^ 2 - χ) / c ^ 2 := div_pos hσ hc2
  have hω0 : 0 ≤ w / c ^ 2 := div_nonneg hw0 hc2.le
  have hωr : w / c ^ 2 ≤ r := (div_le_iff₀ hc2).mpr hw
  have hω1 : w / c ^ 2 < 1 := hωr.trans_lt hr
  have hwc : w ≤ c ^ 2 := by nlinarith
  set ε := (c ^ 2 - χ) / c ^ 2 with hεd
  set ω := w / c ^ 2 with hωd
  have hcont := integral_Nx_major_le hε.le hω0 hω1 (le_of_lt (div_pos three_pos hε))
  have hmaj := fun x (hx : 0 ≤ x) => sq_Nx_div_le hε.le hω0 hω1 hx
  have hf : ContinuousOn (fun ξ => gEdge c χ w ξ ^ 2 / ξ) (Icc 1 2) :=
    ((continuousOn_gEdge hχ hwc).pow 2).div continuousOn_id fun ξ hξ =>
      (by linarith [hξ.1] : (0 : ℝ) < ξ).ne'
  have hM : (0 : ℝ) ≤ 3 / ε := by positivity
  have hG : ContinuousOn (fun x => (4 * (1 - ω) * |1 - (1 - ω) * x| / (1 + (1 - ω) * x) ^ 3
        + (2 * ε / (1 - ω) ^ 3 * (x * |x - 3| / (1 + x) ^ 3)
          + (14 * ε * ω / (1 - ω) ^ 3 * (x / (1 + x) ^ 3)
            + 32 * ε * ω / (1 - ω) ^ 3 * (x ^ 2 / (1 + x) ^ 3)))) ^ 2) (Icc 0 (3 / ε)) := by
    rw [← uIcc_of_le hM]
    have hk : 0 ≤ 1 - ω := by linarith
    have hfr : ∀ {g : ℝ → ℝ}, Continuous g → ContinuousOn (fun x => g x / (1 + x) ^ 3) (uIcc 0 (3 / ε)) :=
      fun hg => by simpa using continuousOn_frac (k := 1) (n := 3) zero_le_one hM hg
    have q0 : ContinuousOn (fun x => 4 * (1 - ω) * |1 - (1 - ω) * x| / (1 + (1 - ω) * x) ^ 3)
        (uIcc 0 (3 / ε)) := continuousOn_frac hk hM (by fun_prop)
    have q1 : ContinuousOn (fun x => 2 * ε / (1 - ω) ^ 3 * (x * |x - 3| / (1 + x) ^ 3)) (uIcc 0 (3 / ε)) :=
      continuousOn_const.mul (hfr (g := fun x => x * |x - 3|) (by fun_prop))
    have q2 : ContinuousOn (fun x => 14 * ε * ω / (1 - ω) ^ 3 * (x / (1 + x) ^ 3)) (uIcc 0 (3 / ε)) :=
      continuousOn_const.mul (hfr (g := fun x => x) (by fun_prop))
    have q3 : ContinuousOn (fun x => 32 * ε * ω / (1 - ω) ^ 3 * (x ^ 2 / (1 + x) ^ 3)) (uIcc 0 (3 / ε)) :=
      continuousOn_const.mul (hfr (continuous_pow 2))
    exact (q0.add (q1.add (q2.add q3))).pow 2
  have key := integral_le_of_sub_sq (K := c ^ 2 / (2 * (c ^ 2 - χ) ^ 3)) hε hf hG (fun ξ hξ => by
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hx0 : 0 ≤ (ξ ^ 2 - 1) / ε := div_nonneg (by nlinarith [hξ.1]) hε.le
    have hD : DM c χ w ξ ≠ 0 := (DM_pos_of_le hχ hwc hξ.1).ne'
    have hl : 1 + ε * ((ξ ^ 2 - 1) / ε) = ξ ^ 2 := by field_simp; ring
    have hB : 0 < Bx ε ω ((ξ ^ 2 - 1) / ε) :=
      lt_of_lt_of_le (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ω) hx0])
        (Bx_ge_lin hε.le hω0 hx0)
    have e : gEdge c χ w ξ ^ 2 / ξ = c ^ 2 / (2 * (c ^ 2 - χ) ^ 3)
        * (Nx ε ω ((ξ ^ 2 - 1) / ε) ^ 2 / ((1 + ε * ((ξ ^ 2 - 1) / ε)) * Bx ε ω ((ξ ^ 2 - 1) / ε) ^ 6)
          * (2 * ξ / ε)) := by
      rw [gEdge_eq hc.ne' hσ.ne' hξ0 hD, hl]
      generalize Nx ε ω ((ξ ^ 2 - 1) / ε) = N
      generalize Bx ε ω ((ξ ^ 2 - 1) / ε) = B at hB
      rw [hεd]
      field_simp
    rw [e]
    gcongr
    exact hmaj _ hx0)
  refine key.trans ?_
  have hb : (√(32 / 15) + ε * ((2 / √5 + ω * (14 / √30 + 32 / √5)) / (1 - ω) ^ 3)) ^ 2
      ≤ (√(32 / 15) + ε * e1 r) ^ 2 := by
    have : 0 < 1 - ω := by linarith
    gcongr
    exact e1_mono hω0 hωr hr
  calc c ^ 2 / (2 * (c ^ 2 - χ) ^ 3) * _ ≤ c ^ 2 / (2 * (c ^ 2 - χ) ^ 3) * (√(32 / 15) + ε * e1 r) ^ 2 := by
        gcongr; exact hcont.trans hb
    _ = _ := by ring

/-- Pointwise `F²/(ℓ³B⁴) ≤ (1 − kx)²/(1 + kx)⁴ + (2ε(2 + ω)/k³)/((1 + x)ℓ) + (ε²(2 + ω)²/k⁴)/ℓ³`,
`k = 1 − ω`, `ℓ = 1 + εx`. -/
theorem sq_Fx_div_le {ε ω x : ℝ} (hε : 0 ≤ ε) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hx : 0 ≤ x) :
    Fx ε ω x ^ 2 / ((1 + ε * x) ^ 3 * Bx ε ω x ^ 4)
      ≤ (1 - (1 - ω) * x) ^ 2 / (1 + (1 - ω) * x) ^ 4
        + (2 * ε * (2 + ω) / (1 - ω) ^ 3 * (1 / ((1 + x) * (1 + ε * x)))
          + ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * (1 / (1 + ε * x) ^ 3)) := by
  set k := 1 - ω with hk
  have hk0 : 0 < k := by linarith
  set L := 1 + ε * x with hLd
  have hL : 1 ≤ L := le_add_of_nonneg_right (mul_nonneg hε hx)
  have hL0 : 0 < L := by linarith
  set B := Bx ε ω x with hBd
  have hB1 : 1 + k * x ≤ B := by have := Bx_ge_lin hε hω0 hx; rw [hk]; linarith
  have hB2 : k * (1 + x) ≤ B := Bx_ge hε hω0 hx
  have hkx : 0 < 1 + k * x := by positivity
  have hB : 0 < B := lt_of_lt_of_le hkx hB1
  set m' := ε * x ^ 2 * (2 + ω) with hm'
  have hm'0 : 0 ≤ m' := by positivity
  set m := ε * x ^ 2 * (2 + ω / L) with hmd
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ m' := by
    have : ω / L ≤ ω := div_le_self hω0 hL
    have : 0 ≤ ε * x ^ 2 := by positivity
    rw [hmd, hm']; nlinarith
  have hF : Fx ε ω x = (1 - k * x) - m := by rw [Fx_eq (by linarith), hmd]
  have hF0 : |1 - k * x| ≤ B := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hk0.le hx]
  have hsq : Fx ε ω x ^ 2 ≤ (1 - k * x) ^ 2 + 2 * B * m' + m' ^ 2 := by
    rw [hF]
    have a1 : -((1 - k * x) * m) ≤ |1 - k * x| * m := by
      rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs _) hm0
    have a2 : |1 - k * x| * m ≤ B * m' := mul_le_mul hF0 hm1 hm0 hB.le
    have a3 : m ^ 2 ≤ m' ^ 2 := pow_le_pow_left₀ hm0 hm1 2
    nlinarith
  have hden : 0 < L ^ 3 * B ^ 4 := by positivity
  have ha : (1 - k * x) ^ 2 / (L ^ 3 * B ^ 4) ≤ (1 - k * x) ^ 2 / (1 + k * x) ^ 4 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    calc (1 + k * x) ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hkx.le hB1 4
      _ ≤ L ^ 3 * B ^ 4 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hL)
  have hx1 : x ^ 2 / (1 + x) ^ 2 ≤ 1 := div_le_one_of_le₀ (by nlinarith) (by positivity)
  have hb : 2 * B * m' / (L ^ 3 * B ^ 4) ≤ 2 * ε * (2 + ω) / k ^ 3 * (1 / ((1 + x) * L)) := by
    have s1 : 2 * B * m' / (L ^ 3 * B ^ 4) = 2 * m' / (L ^ 3 * B ^ 3) := by field_simp
    have s2 : 2 * m' / (L ^ 3 * B ^ 3) ≤ 2 * m' / (L * (k * (1 + x)) ^ 3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul (le_self_pow₀ hL (by norm_num)) (pow_le_pow_left₀ (by positivity) hB2 3)
        (by positivity) (by positivity)
    have s3 : 2 * m' / (L * (k * (1 + x)) ^ 3)
        = 2 * ε * (2 + ω) / k ^ 3 * (1 / ((1 + x) * L)) * (x ^ 2 / (1 + x) ^ 2) := by
      rw [hm']; field_simp
    rw [s1]; refine s2.trans ?_; rw [s3]
    exact mul_le_of_le_one_right (by positivity) hx1
  have hc : m' ^ 2 / (L ^ 3 * B ^ 4) ≤ ε ^ 2 * (2 + ω) ^ 2 / k ^ 4 * (1 / L ^ 3) := by
    have s2 : m' ^ 2 / (L ^ 3 * B ^ 4) ≤ m' ^ 2 / (L ^ 3 * (k * (1 + x)) ^ 4) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB2 4) (by positivity)
    have s3 : m' ^ 2 / (L ^ 3 * (k * (1 + x)) ^ 4)
        = ε ^ 2 * (2 + ω) ^ 2 / k ^ 4 * (1 / L ^ 3) * (x ^ 2 / (1 + x) ^ 2) ^ 2 := by
      rw [hm']; field_simp
    refine s2.trans ?_; rw [s3]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hx1)
  calc Fx ε ω x ^ 2 / (L ^ 3 * B ^ 4) ≤ ((1 - k * x) ^ 2 + 2 * B * m' + m' ^ 2) / (L ^ 3 * B ^ 4) := by
        gcongr
    _ = (1 - k * x) ^ 2 / (L ^ 3 * B ^ 4) + 2 * B * m' / (L ^ 3 * B ^ 4) + m' ^ 2 / (L ^ 3 * B ^ 4) := by
        rw [add_div, add_div]
    _ ≤ _ := by
        have := add_le_add (add_le_add ha hb) hc
        linarith

theorem integral_Fx_major_le {ε ω M : ℝ} (hε : 0 < ε) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hM : 0 ≤ M) :
    ∫ x in (0 : ℝ)..M, ((1 - (1 - ω) * x) ^ 2 / (1 + (1 - ω) * x) ^ 4
        + (2 * ε * (2 + ω) / (1 - ω) ^ 3 * (1 / ((1 + x) * (1 + ε * x)))
          + ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * (1 / (1 + ε * x) ^ 3)))
      ≤ 1 / (3 * (1 - ω)) + 2 * (2 + ω) / (1 - ω) ^ 3 * (ε * ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x)))
        + ε * (2 + ω) ^ 2 / (2 * (1 - ω) ^ 4) := by
  have hk0 : 0 < 1 - ω := by linarith
  have i0 : IntervalIntegrable (fun x => (1 - (1 - ω) * x) ^ 2 / (1 + (1 - ω) * x) ^ 4) MeasureTheory.volume 0 M :=
    (continuousOn_frac (g := fun x => (1 - (1 - ω) * x) ^ 2) hk0.le hM (by fun_prop)).intervalIntegrable
  have i1 : IntervalIntegrable (fun x => 1 / ((1 + x) * (1 + ε * x))) MeasureTheory.volume 0 M :=
    (continuousOn_inv_mul hε.le hM).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => 1 / (1 + ε * x) ^ 3) MeasureTheory.volume 0 M :=
    (continuousOn_frac (g := fun _ => (1 : ℝ)) hε.le hM (by fun_prop)).intervalIntegrable
  rw [integral_add i0 ((i1.const_mul _).add (i2.const_mul _)), integral_add (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul]
  have b0 := integral_lead2_le hk0 hM
  have b2 := integral_inv_cube_le hε hM
  have hJ : 0 ≤ ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x)) := integral_nonneg hM fun x hx => by
    have : 0 ≤ x := hx.1
    positivity
  have e1 : 2 * ε * (2 + ω) / (1 - ω) ^ 3 * ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x))
      = 2 * (2 + ω) / (1 - ω) ^ 3 * (ε * ∫ x in (0 : ℝ)..M, 1 / ((1 + x) * (1 + ε * x))) := by ring
  have e2 : ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * (1 / (2 * ε)) = ε * (2 + ω) ^ 2 / (2 * (1 - ω) ^ 4) := by
    field_simp
  have b2' : ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * ∫ x in (0 : ℝ)..M, 1 / (1 + ε * x) ^ 3
      ≤ ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * (1 / (2 * ε)) := by gcongr
  rw [e1]; linarith

/-- `∫₁² f²/ξ³ ≤ (2/(c²σ²))(1/(3k) + 2(2 + ω)εJ/k³ + ε(2 + ω)²/(2k⁴))`, `J = ∫₀^{3/ε}dx/((1 + x)(1 + εx))`. -/
theorem integral_fEdge_sq_le_J {c χ w : ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hw0 : 0 ≤ w) (hw1 : w < c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, fEdge c χ w ξ ^ 2 / ξ ^ 3
      ≤ 2 / (c ^ 2 * (c ^ 2 - χ)) * (1 / (3 * (1 - w / c ^ 2)) + 2 * (2 + w / c ^ 2) / (1 - w / c ^ 2) ^ 3
          * ((c ^ 2 - χ) / c ^ 2 * ∫ x in (0 : ℝ)..3 / ((c ^ 2 - χ) / c ^ 2),
            1 / ((1 + x) * (1 + (c ^ 2 - χ) / c ^ 2 * x)))
        + (c ^ 2 - χ) / c ^ 2 * (2 + w / c ^ 2) ^ 2 / (2 * (1 - w / c ^ 2) ^ 4)) := by
  have hσ : 0 < c ^ 2 - χ := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hε : 0 < (c ^ 2 - χ) / c ^ 2 := div_pos hσ hc2
  have hω0 : 0 ≤ w / c ^ 2 := div_nonneg hw0 hc2.le
  have hω1 : w / c ^ 2 < 1 := (div_lt_one hc2).mpr hw1
  set ε := (c ^ 2 - χ) / c ^ 2 with hεd
  set ω := w / c ^ 2 with hωd
  have hM : (0 : ℝ) ≤ 3 / ε := by positivity
  have hf : ContinuousOn (fun ξ => fEdge c χ w ξ ^ 2 / ξ ^ 3) (Icc 1 2) :=
    ((continuousOn_fEdge hχ hw1.le).pow 2).div (continuousOn_id.pow 3) fun ξ hξ =>
      pow_ne_zero 3 (by linarith [hξ.1] : (0 : ℝ) < ξ).ne'
  have hk : 0 ≤ 1 - ω := by linarith
  have hG : ContinuousOn (fun x => (1 - (1 - ω) * x) ^ 2 / (1 + (1 - ω) * x) ^ 4
        + (2 * ε * (2 + ω) / (1 - ω) ^ 3 * (1 / ((1 + x) * (1 + ε * x)))
          + ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * (1 / (1 + ε * x) ^ 3))) (Icc 0 (3 / ε)) := by
    rw [← uIcc_of_le hM]
    have q0 : ContinuousOn (fun x => (1 - (1 - ω) * x) ^ 2 / (1 + (1 - ω) * x) ^ 4) (uIcc 0 (3 / ε)) :=
      continuousOn_frac hk hM (by fun_prop)
    have q1 : ContinuousOn (fun x => 2 * ε * (2 + ω) / (1 - ω) ^ 3 * (1 / ((1 + x) * (1 + ε * x))))
        (uIcc 0 (3 / ε)) := continuousOn_const.mul (continuousOn_inv_mul hε.le hM)
    have q2 : ContinuousOn (fun x => 1 / (1 + ε * x) ^ 3) (uIcc 0 (3 / ε)) :=
      continuousOn_frac hε.le hM continuous_const
    have q2' : ContinuousOn (fun x => ε ^ 2 * (2 + ω) ^ 2 / (1 - ω) ^ 4 * (1 / (1 + ε * x) ^ 3))
        (uIcc 0 (3 / ε)) := continuousOn_const.mul q2
    exact q0.add (q1.add q2')
  have key := integral_le_of_sub_sq (K := 2 / (c ^ 2 * (c ^ 2 - χ))) hε hf hG (fun ξ hξ => by
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hx0 : 0 ≤ (ξ ^ 2 - 1) / ε := div_nonneg (by nlinarith [hξ.1]) hε.le
    have hD : DM c χ w ξ ≠ 0 := (DM_pos_of_le hχ hw1.le hξ.1).ne'
    have hl : 1 + ε * ((ξ ^ 2 - 1) / ε) = ξ ^ 2 := by field_simp; ring
    have hB : 0 < Bx ε ω ((ξ ^ 2 - 1) / ε) :=
      lt_of_lt_of_le (by nlinarith [mul_nonneg hk hx0]) (Bx_ge_lin hε.le hω0 hx0)
    have e : fEdge c χ w ξ ^ 2 / ξ ^ 3 = 2 / (c ^ 2 * (c ^ 2 - χ))
        * (Fx ε ω ((ξ ^ 2 - 1) / ε) ^ 2 / ((1 + ε * ((ξ ^ 2 - 1) / ε)) ^ 3 * Bx ε ω ((ξ ^ 2 - 1) / ε) ^ 4)
          * (2 * ξ / ε)) := by
      rw [fEdge_eq hc.ne' hσ.ne' hξ0 hD, hl]
      generalize Fx ε ω ((ξ ^ 2 - 1) / ε) = F
      generalize Bx ε ω ((ξ ^ 2 - 1) / ε) = B at hB
      rw [hεd]
      field_simp
    rw [e]
    gcongr
    exact sq_Fx_div_le hε.le hω0 hω1 hx0)
  refine key.trans ?_
  gcongr
  exact integral_Fx_major_le hε hω0 hω1 hM

/-- The `ω ≤ r` comparison behind E2 and E2′, with `εJ ≤ Λ`. -/
theorem fEdge_coeff_le {ω r ε J Λ : ℝ} (hω0 : 0 ≤ ω) (hωr : ω ≤ r) (hr : r < 1) (hε : 0 ≤ ε) (hJ0 : 0 ≤ ε * J)
    (hJ : ε * J ≤ Λ) :
    1 / (3 * (1 - ω)) + 2 * (2 + ω) / (1 - ω) ^ 3 * (ε * J) + ε * (2 + ω) ^ 2 / (2 * (1 - ω) ^ 4)
      ≤ 1 / (3 * (1 - r)) + (2 * (2 + r) * Λ + ε * (2 + r) ^ 2 / 2) / (1 - r) ^ 4 := by
  have h1 : 0 < 1 - r := by linarith
  have h2 : 0 < 1 - ω := by linarith
  have hr0 : 0 ≤ r := hω0.trans hωr
  have hk : 1 - r ≤ 1 - ω := by linarith
  have h43 : (1 - r) ^ 4 ≤ (1 - r) ^ 3 := pow_le_pow_of_le_one h1.le (by linarith) (by norm_num)
  have a : 1 / (3 * (1 - ω)) ≤ 1 / (3 * (1 - r)) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have b0 : 2 * (2 + ω) / (1 - ω) ^ 3 ≤ 2 * (2 + r) / (1 - r) ^ 4 :=
    div_le_div₀ (by positivity) (by linarith) (by positivity)
      (h43.trans (pow_le_pow_left₀ h1.le hk 3))
  have b : 2 * (2 + ω) / (1 - ω) ^ 3 * (ε * J) ≤ 2 * (2 + r) / (1 - r) ^ 4 * Λ :=
    mul_le_mul b0 hJ hJ0 (by positivity)
  have c0 : ε * (2 + ω) ^ 2 / (2 * (1 - ω) ^ 4) ≤ ε * (2 + r) ^ 2 / (2 * (1 - r) ^ 4) := by
    have : (1 - r) ^ 4 ≤ (1 - ω) ^ 4 := pow_le_pow_left₀ h1.le hk 4
    gcongr
  have e : 1 / (3 * (1 - r)) + (2 * (2 + r) * Λ + ε * (2 + r) ^ 2 / 2) / (1 - r) ^ 4
      = 1 / (3 * (1 - r)) + 2 * (2 + r) / (1 - r) ^ 4 * Λ + ε * (2 + r) ^ 2 / (2 * (1 - r) ^ 4) := by
    field_simp; ring
  rw [e]; linarith

/-- **E2**: `∫₁² f²/ξ³ ≤ 2(1/(3(1 − r)) + (2(2 + r)εL_c + ε(2 + r)²/2)/(1 − r)⁴)/(c²σ²)` for `σ² ≥ 5c`. -/
theorem integral_fEdge_sq_le {c χ w r : ℝ} (hc : 5 < c) (hσ : 5 * c ≤ c ^ 2 - χ) (hw0 : 0 ≤ w) (hr : r < 1)
    (hw : w ≤ r * c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, fEdge c χ w ξ ^ 2 / ξ ^ 3
      ≤ 2 * (1 / (3 * (1 - r)) + (2 * (2 + r) * ((c ^ 2 - χ) / c ^ 2) * Lc c
        + (c ^ 2 - χ) / c ^ 2 * (2 + r) ^ 2 / 2) / (1 - r) ^ 4) / (c ^ 2 * (c ^ 2 - χ)) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hS : 0 < c ^ 2 - χ := by nlinarith
  have hχ : χ < c ^ 2 := by linarith
  have hωr : w / c ^ 2 ≤ r := (div_le_iff₀ hc2).mpr hw
  have hw1 : w < c ^ 2 := by nlinarith [div_lt_one hc2 |>.mp (hωr.trans_lt hr)]
  have key := integral_fEdge_sq_le_J hc0 hχ hw0 hw1
  set ε := (c ^ 2 - χ) / c ^ 2 with hεd
  have hε : 0 < ε := div_pos hS hc2
  have hε0 : 5 / c ≤ ε := by
    rw [hεd, div_le_div_iff₀ hc0 hc2]; nlinarith
  have hJ := integral_inv_mul_le_log (M := 3 / ε) (by positivity : (0 : ℝ) < 5 / c)
    ((div_lt_one hc0).mpr hc) hε0 (by positivity)
  rw [one_div_div] at hJ
  have hJ0 : 0 ≤ ∫ x in (0 : ℝ)..3 / ε, 1 / ((1 + x) * (1 + ε * x)) :=
    integral_nonneg (by positivity) fun x hx => by have : 0 ≤ x := hx.1; positivity
  have hco := fEdge_coeff_le (div_nonneg hw0 hc2.le) hωr hr hε.le (mul_nonneg hε.le hJ0)
    (mul_le_mul_of_nonneg_left hJ hε.le)
  refine key.trans ?_
  calc 2 / (c ^ 2 * (c ^ 2 - χ)) * _ ≤ 2 / (c ^ 2 * (c ^ 2 - χ)) * (1 / (3 * (1 - r))
        + (2 * (2 + r) * (ε * (Real.log (c / 5) / (1 - 5 / c))) + ε * (2 + r) ^ 2 / 2) / (1 - r) ^ 4) := by
        gcongr
    _ = _ := by unfold Lc; ring

/-- **E2′**: `∫₁² f²/ξ³ ≤ 2Ī₂/(c²σ²)` for `0 ≤ χ < c²`. -/
theorem integral_fEdge_sq_le_I2bar {c χ w r : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hw0 : 0 ≤ w)
    (hr : r < 1) (hw : w ≤ r * c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, fEdge c χ w ξ ^ 2 / ξ ^ 3 ≤ 2 * I2bar r / (c ^ 2 * (c ^ 2 - χ)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hS : 0 < c ^ 2 - χ := by linarith
  have hωr : w / c ^ 2 ≤ r := (div_le_iff₀ hc2).mpr hw
  have hw1 : w < c ^ 2 := by nlinarith [div_lt_one hc2 |>.mp (hωr.trans_lt hr)]
  have key := integral_fEdge_sq_le_J hc hχ hw0 hw1
  set ε := (c ^ 2 - χ) / c ^ 2 with hεd
  have hε : 0 < ε := div_pos hS hc2
  have hε1 : ε ≤ 1 := by rw [hεd, div_le_one hc2]; linarith
  have hJ := mul_integral_inv_mul_le_one (M := 3 / ε) hε hε1 (by positivity)
  have hJ0 : 0 ≤ ∫ x in (0 : ℝ)..3 / ε, 1 / ((1 + x) * (1 + ε * x)) :=
    integral_nonneg (by positivity) fun x hx => by have : 0 ≤ x := hx.1; positivity
  have hco := fEdge_coeff_le (div_nonneg hw0 hc2.le) hωr hr hε.le (mul_nonneg hε.le hJ0) hJ
  have hr0 : 0 ≤ r := (div_nonneg hw0 hc2.le).trans hωr
  have hI : 1 / (3 * (1 - r)) + (2 * (2 + r) * 1 + ε * (2 + r) ^ 2 / 2) / (1 - r) ^ 4 ≤ I2bar r := by
    unfold I2bar
    have : 0 < 1 - r := by linarith
    have hn : 2 * (2 + r) * 1 + ε * (2 + r) ^ 2 / 2 ≤ 2 * (2 + r) + (2 + r) ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hε1 (sq_nonneg (2 + r))]
    have := div_le_div_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (1 - r) ^ 4)
    linarith
  refine key.trans ?_
  calc 2 / (c ^ 2 * (c ^ 2 - χ)) * _ ≤ 2 / (c ^ 2 * (c ^ 2 - χ)) * I2bar r := by
        gcongr; exact hco.trans hI
    _ = _ := by ring

/-- **Lemma E**: `∫₁²|ρ_t|² ≤ (√(32/15) + εe₁)²/(2cs³) + 2rĪ₂(ε)/(cs) + √(Ī₁Ī₂)/(c²s²)`, `s = σ²/c`,
`ε = s/c`, for `c > 5`, `0 ≤ χ`, `s ≥ 5`, `t² + ¼ ≤ rc²`, `r < 1`. -/
theorem integral_norm_rhoEdge_sq_le {c χ r t : ℝ} (hc : 5 < c) (hχ0 : 0 ≤ χ) (hσ : 5 * c ≤ c ^ 2 - χ)
    (hr : r < 1) (hw : t ^ 2 + 1 / 4 ≤ r * c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χ t ξ‖ ^ 2 ≤ lemmaEBound c r ((c ^ 2 - χ) / c) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hS : 0 < c ^ 2 - χ := by nlinarith
  have hχ : χ < c ^ 2 := by linarith
  set w := t ^ 2 + 1 / 4 with hwd
  have hw0 : 0 < w := by positivity
  have hr0 : 0 ≤ r := (div_nonneg hw0.le hc2.le).trans ((div_le_iff₀ hc2).mpr hw)
  have hwc : w ≤ c ^ 2 := hw.trans (by nlinarith)
  have hg := continuousOn_gEdge (b := 2) hχ hwc
  have hf := continuousOn_fEdge (b := 2) hχ hwc
  have hpos : ∀ ξ ∈ Icc (1 : ℝ) 2, 0 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hne : ∀ {n : ℕ}, ∀ ξ ∈ Icc (1 : ℝ) 2, ξ ^ n ≠ 0 := fun ξ hξ => pow_ne_zero _ (hpos ξ hξ).ne'
  have cA : ContinuousOn (fun ξ => gEdge c χ w ξ ^ 2 / ξ) (Icc 1 2) :=
    (hg.pow 2).div continuousOn_id fun ξ hξ => (hpos ξ hξ).ne'
  have cB : ContinuousOn (fun ξ => fEdge c χ w ξ ^ 2 / ξ ^ 3) (Icc 1 2) :=
    (hf.pow 2).div (continuousOn_id.pow 3) fun ξ hξ => hne ξ hξ
  have cC : ContinuousOn (fun ξ => gEdge c χ w ξ * fEdge c χ w ξ / ξ ^ 2) (Icc 1 2) :=
    (hg.mul hf).div (continuousOn_id.pow 2) fun ξ hξ => hne ξ hξ
  have iA := cA.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (1 : ℝ) ≤ 2)
  have iB := cB.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (1 : ℝ) ≤ 2)
  have iC := cC.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (1 : ℝ) ≤ 2)
  set A := ∫ ξ in (1 : ℝ)..2, gEdge c χ w ξ ^ 2 / ξ with hAd
  set B := ∫ ξ in (1 : ℝ)..2, fEdge c χ w ξ ^ 2 / ξ ^ 3 with hBd
  set C := ∫ ξ in (1 : ℝ)..2, gEdge c χ w ξ * fEdge c χ w ξ / ξ ^ 2 with hCd
  have hU : uIcc (1 : ℝ) 2 = Icc 1 2 := uIcc_of_le (by norm_num)
  -- the exact split `∫|ρ|² = A + wB − C`
  have hsplit : ∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χ t ξ‖ ^ 2 = A + w * B - C := by
    have e : ∀ ξ ∈ uIcc (1 : ℝ) 2, ‖rhoEdge c χ t ξ‖ ^ 2
        = gEdge c χ w ξ ^ 2 / ξ + w * (fEdge c χ w ξ ^ 2 / ξ ^ 3) - gEdge c χ w ξ * fEdge c χ w ξ / ξ ^ 2 := by
      intro ξ hξ; rw [hU] at hξ
      rw [norm_rhoEdge_sq c χ t (hpos ξ hξ), mul_div_assoc]
    rw [integral_congr e, integral_sub (iA.add (iB.const_mul w)) iC, integral_add iA (iB.const_mul w),
      integral_const_mul]
  -- Cauchy–Schwarz on the cross term
  have hcs : -C ≤ √(A * B) := by
    have csq : ContinuousOn (fun ξ : ℝ => √ξ) (Icc 1 2) := continuous_sqrt.continuousOn
    have hsq : ∀ ξ ∈ Icc (1 : ℝ) 2, √ξ ≠ 0 := fun ξ hξ => (Real.sqrt_pos.mpr (hpos ξ hξ)).ne'
    have cF : ContinuousOn (fun ξ => gEdge c χ w ξ / √ξ) (Icc 1 2) := hg.div csq hsq
    have cW : ContinuousOn (fun ξ => fEdge c χ w ξ / (ξ * √ξ)) (Icc 1 2) :=
      hf.div (continuousOn_id.mul csq) fun ξ hξ => mul_ne_zero (hpos ξ hξ).ne' (hsq ξ hξ)
    have h := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (a := 1) (b := 2) (by norm_num)
      ((cF.pow 2).intervalIntegrable_of_Icc (by norm_num)) ((cW.pow 2).intervalIntegrable_of_Icc (by norm_num))
      ((cF.mul cW).intervalIntegrable_of_Icc (by norm_num))
    have e1 : ∫ ξ in (1 : ℝ)..2, gEdge c χ w ξ / √ξ * (fEdge c χ w ξ / (ξ * √ξ)) = C := by
      refine integral_congr fun ξ hξ => ?_
      rw [hU] at hξ
      have h1 := Real.mul_self_sqrt (hpos ξ hξ).le
      have h2 := hsq ξ hξ
      have h3 := (hpos ξ hξ).ne'
      field_simp
      rw [Real.sq_sqrt (hpos ξ hξ).le]; ring
    have e2 : ∫ ξ in (1 : ℝ)..2, (gEdge c χ w ξ / √ξ) ^ 2 = A := by
      refine integral_congr fun ξ hξ => ?_
      rw [hU] at hξ
      rw [div_pow, Real.sq_sqrt (hpos ξ hξ).le]
    have e3 : ∫ ξ in (1 : ℝ)..2, (fEdge c χ w ξ / (ξ * √ξ)) ^ 2 = B := by
      refine integral_congr fun ξ hξ => ?_
      rw [hU] at hξ
      rw [div_pow, mul_pow, Real.sq_sqrt (hpos ξ hξ).le]; ring
    rw [e1, e2, e3] at h
    exact (neg_le_abs C).trans (Real.abs_le_sqrt h)
  -- the three bounds
  have hA := integral_gEdge_sq_le hc0 hχ hw0.le hr hw
  have hB := integral_fEdge_sq_le hc hσ hw0.le hr hw
  have hB' := integral_fEdge_sq_le_I2bar hc0 hχ0 hχ hw0.le hr hw
  have hA0 : 0 ≤ A := integral_nonneg (by norm_num) fun ξ hξ => by have := hpos ξ hξ; positivity
  have hB0 : 0 ≤ B := integral_nonneg (by norm_num) fun ξ hξ => by have := hpos ξ hξ; positivity
  set S := c ^ 2 - χ with hSd
  set ε := S / c ^ 2 with hεd
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hεd, div_le_one hc2]; linarith
  have he1 := e1_nonneg hr0 hr
  have hI1 : (√(32 / 15) + ε * e1 r) ^ 2 ≤ I1bar r := by
    unfold I1bar; gcongr; exact mul_le_of_le_one_left he1 hε1
  have hAB : A * B ≤ I1bar r * I2bar r / (S ^ 2) ^ 2 := by
    calc A * B ≤ (√(32 / 15) + ε * e1 r) ^ 2 * c ^ 2 / (2 * S ^ 3) * (2 * I2bar r / (c ^ 2 * S)) :=
          mul_le_mul hA hB' hB0 (by positivity)
      _ ≤ I1bar r * c ^ 2 / (2 * S ^ 3) * (2 * I2bar r / (c ^ 2 * S)) := by
          have : 0 ≤ I2bar r := by
            unfold I2bar; have : 0 < 1 - r := by linarith
            positivity
          gcongr
      _ = I1bar r * I2bar r / (S ^ 2) ^ 2 := by field_simp
  have hsAB : √(A * B) ≤ √(I1bar r * I2bar r) / (c ^ 2 * (S / c) ^ 2) := by
    refine (Real.sqrt_le_sqrt hAB).trans_eq ?_
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    congr 1; field_simp
  have hwB : w * B ≤ r * c ^ 2 * (2 * (1 / (3 * (1 - r)) + (2 * (2 + r) * ε * Lc c
      + ε * (2 + r) ^ 2 / 2) / (1 - r) ^ 4) / (c ^ 2 * S)) :=
    mul_le_mul hw hB hB0 (by positivity)
  rw [hsplit]
  have hfin : (√(32 / 15) + ε * e1 r) ^ 2 * c ^ 2 / (2 * S ^ 3)
      + r * c ^ 2 * (2 * (1 / (3 * (1 - r)) + (2 * (2 + r) * ε * Lc c + ε * (2 + r) ^ 2 / 2) / (1 - r) ^ 4)
        / (c ^ 2 * S))
      + √(I1bar r * I2bar r) / (c ^ 2 * (S / c) ^ 2) = lemmaEBound c r (S / c) := by
    unfold lemmaEBound
    rw [hεd]
    field_simp
  rw [← hfin]
  linarith

end Cvs.Prolate.Mellin.EdgeRemainderClosedForm
