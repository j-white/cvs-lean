import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1GapParametricRH
import Cvs.WeilForm.ApproxWindowPositivityRH
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SimpleGroundEvenOrOdd
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TwoIndependentClasses
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `L1GapL` gives RH through near-positivity, given a ceiling on the floor

With `0 ≤ L x`, clause (iii) of `L1GapL L x` gives `(K − 1)s < μ`, `K = √x log x`; a floor ceiling `μ ≤ s + M x`
gives `s < M x/(K − 2)`, so `M = o(K)` makes near-positivity approximate window positivity (Cvs.WeilForm.ApproxWindowPositivityRH). Two orthogonal
nonzero even classes with Rayleigh quotients `≤ M x` give the ceiling `μ ≤ s + 2M x`.
-/

noncomputable section

open MeasureTheory Real Filter Topology
open scoped InnerProductSpace

namespace Cvs.Route.L1GapCeilingRH
open Cvs.ZeroCounting

open Cvs.ZeroCounting
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.JointGapConnesFromL1 (connesEven connesOdd)

/-- The inner product with a combination of two classes. -/
theorem inner_comb {L : ℝ} (hL : 0 ≤ L) (η a b : Cvs.WeilForm.FormDomain.formDomain hL) (t u : ℝ) :
    ⟪η, t • a + u • b⟫_ℝ = t * ⟪η, a⟫_ℝ + u * ⟪η, b⟫_ℝ := by
  rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe, Cvs.WeilForm.TwoIndependentClasses.inner_coe, Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_add, Submodule.coe_add,
    Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul,
    inner_add_right, real_inner_smul_right, real_inner_smul_right]

/-- Pythagoras for a combination of two orthogonal classes. -/
theorem norm_sq_comb {L : ℝ} (hL : 0 ≤ L) {a b : Cvs.WeilForm.FormDomain.formDomain hL} (hab : ⟪a, b⟫_ℝ = 0) (t u : ℝ) :
    ‖t • a + u • b‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 + u ^ 2 * ‖b‖ ^ 2 := by
  rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe] at hab
  show ‖(((t • a + u • b : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2 =
    t ^ 2 * ‖((a : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2
      + u ^ 2 * ‖((b : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2
  rw [Submodule.coe_add, Submodule.coe_add,
    Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul,
    norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hab, norm_smul, norm_smul,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

/-- **The floor is below twice the Rayleigh ceiling of an orthogonal even pair, plus `s`**. -/
theorem floor_le_of_pair {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {s μ M : ℝ} (η : Cvs.WeilForm.FormDomain.formDomain hL)
    (hneg : ∀ φ : Cvs.WeilForm.FormDomain.formDomain hL, -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ)
    (hfloor : ∀ φ : Cvs.WeilForm.FormDomain.formDomain hL, Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ = φ → ⟪η, φ⟫_ℝ = 0 →
      μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ)
    {a b : Cvs.WeilForm.FormDomain.formDomain hL} (hae : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL a = a) (hbe : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL b = b)
    (hab : ⟪a, b⟫_ℝ = 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hQa : Cvs.WeilForm.InfimumAttainedSphere.Q hL P R a ≤ M * ‖a‖ ^ 2) (hQb : Cvs.WeilForm.InfimumAttainedSphere.Q hL P R b ≤ M * ‖b‖ ^ 2) :
    μ ≤ s + 2 * M := by
  have ha2 : 0 < ‖a‖ ^ 2 := by positivity
  have hb2 : 0 < ‖b‖ ^ 2 := by positivity
  have hMs : -s ≤ M := by
    have := (hneg a).trans hQa
    nlinarith
  by_cases hηa : ⟪η, a⟫_ℝ = 0
  · have h := (hfloor a hae hηa).trans hQa
    have : μ ≤ M := le_of_mul_le_mul_right h ha2
    linarith
  set α := ⟪η, b⟫_ℝ
  set β := -⟪η, a⟫_ℝ
  have hβ : β ≠ 0 := neg_ne_zero.mpr hηa
  set B := Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R with hBd
  have hsymm : B b a = B a b := (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq b a
  have hQ : ∀ t u : ℝ, Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (t • a + u • b)
      = t ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R a + 2 * t * u * B a b + u ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R b := by
    intro t u
    rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self hL P R a, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self hL P R b, ← hBd]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm]; ring
  have hN : ∀ t u : ℝ, ‖t • a + u • b‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 + u ^ 2 * ‖b‖ ^ 2 :=
    fun t u => norm_sq_comb hL hab t u
  set φ := α • a + β • b with hφd
  have hφe : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ = φ := by
    rw [hφd, Cvs.WeilForm.EvenOddSplitForm.reflD_add, Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, hae, hbe]
  have hφη : ⟪η, φ⟫_ℝ = 0 := by
    rw [hφd, inner_comb]; ring
  have h1 := hfloor φ hφe hφη
  have h2 := hneg (α • a + (-β) • b)
  rw [hN] at h1 h2
  rw [hQ] at h1 h2
  have hNpos : 0 < α ^ 2 * ‖a‖ ^ 2 + β ^ 2 * ‖b‖ ^ 2 := by
    have : 0 < β ^ 2 := by positivity
    nlinarith [sq_nonneg α]
  have hQa' : α ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R a ≤ α ^ 2 * (M * ‖a‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hQa (sq_nonneg α)
  have hQb' : β ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R b ≤ β ^ 2 * (M * ‖b‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hQb (sq_nonneg β)
  have key : μ * (α ^ 2 * ‖a‖ ^ 2 + β ^ 2 * ‖b‖ ^ 2)
      ≤ (s + 2 * M) * (α ^ 2 * ‖a‖ ^ 2 + β ^ 2 * ‖b‖ ^ 2) := by
    have e : (-β) ^ 2 = β ^ 2 := by ring
    rw [e] at h2
    nlinarith
  exact le_of_mul_le_mul_right key hNpos

/-- **RH from `L1GapL` and a floor ceiling `μ ≤ s + M x` with `M x = o(√x log x)`**, for `L ≥ 0` eventually. -/
theorem riemannHypothesis_of_L1GapL_of_bound {L M : ℕ → ℝ} (hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ L x)
    (hM : ∀ᶠ x : ℕ in atTop, ∀ (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
      (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) →
      (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
          μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) →
      μ ≤ s + M x)
    (hMK : Tendsto (fun x : ℕ => M x / (√(x : ℝ) * Real.log x)) atTop (𝓝 0))
    (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.L1GapParametricRH.L1GapL L x) : RiemannHypothesis := by
  refine Cvs.WeilForm.ApproxWindowPositivityRH.rh_of_approx_windowPos fun ε hε x₀ => ?_
  have hK : Tendsto (fun x : ℕ => √(x : ℝ) * Real.log x) atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ ?_ ?_
    · exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ x : ℕ in atTop, x₀ ≤ x ∧ 0 ≤ L x ∧ 6 ≤ √(x : ℝ) * Real.log x ∧
      M x / (√(x : ℝ) * Real.log x) ≤ ε / 3 := by
    filter_upwards [eventually_ge_atTop x₀, hL0, hK.eventually (eventually_ge_atTop 6),
      hMK.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < ε / 3))] with x a b c d
      using ⟨a, b, c, d⟩
  obtain ⟨x, ⟨⟨hx, s, μ, η, hneg, hfloor, hlt⟩, hMx⟩, hx₀, hLx, hK6, hMKx⟩ :=
    ((h.and_eventually hM).and_eventually hev).exists
  refine ⟨x, hx₀, fun φ => ?_⟩
  set K := √(x : ℝ) * Real.log x with hKd
  have hK0 : 0 < K := by linarith
  have hsle : s ≤ ε := by
    by_contra hcon
    push Not at hcon
    have hs0 : 0 ≤ s := by linarith
    have hμ := hMx s μ η hneg hfloor
    have hfirst : 0 ≤ K * ((L x + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
        / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2) := by positivity
    have hMle : M x ≤ ε / 3 * K := by rwa [div_le_iff₀ hK0] at hMKx
    nlinarith
  have := hneg φ
  have hn : 0 ≤ ‖φ‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **RH from `L1GapL` and an orthogonal pair of nonzero even classes with Rayleigh quotients `≤ M x = o(√x log x)`**,
for `L ≥ 0` eventually. -/
theorem riemannHypothesis_of_L1GapL_of_pair {L M : ℕ → ℝ} (hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ L x)
    (hpair : ∀ᶠ x : ℕ in atTop, ∃ a b : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) a = a ∧ Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) b = b ∧
      ⟪a, b⟫_ℝ = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) a ≤ M x * ‖a‖ ^ 2 ∧
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) b ≤ M x * ‖b‖ ^ 2)
    (hMK : Tendsto (fun x : ℕ => M x / (√(x : ℝ) * Real.log x)) atTop (𝓝 0))
    (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.L1GapParametricRH.L1GapL L x) : RiemannHypothesis := by
  refine riemannHypothesis_of_L1GapL_of_bound (M := fun x => 2 * M x) hL0 ?_ ?_ h
  · filter_upwards [hpair] with x ⟨a, b, hae, hbe, hab, ha, hb, hQa, hQb⟩ s μ η hneg hfloor
    exact floor_le_of_pair _ _ _ η hneg hfloor hae hbe hab ha hb hQa hQb
  · simpa [mul_div_assoc] using hMK.const_mul 2

end Cvs.Route.L1GapCeilingRH
