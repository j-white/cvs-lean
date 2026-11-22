import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.DirichletDualFloorShifted
import Cvs.Prolate.Gram.EquilibriumPotential
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The deep cell floor from the endpoint amplitude and the discrete potential (eq-cpb §4)

At an endpoint `a ∈ [½, ½ + ρ]` with `h_{4j}(a)² ≥ e^{−2c·Ag(T_j, a) − δc}` (`Ag` the Agmon integral) and a set `S ⊇ x`
Dirichlet nodes whose residues obey `r_σ² ≤ R_j²e^{2cΨ_a(T_j) + δc}`, Cvs.Prolate.Gram.DirichletDualFloorShifted and `g_σ² ≥ ¼` give
`σ'_j ≥ e^{−2c(Ag + Ψ_a) − 2δc}/(4|S|)`, and `Ag + Ψ_a = Δ_a ≤ Δ + 2(t_e(a) − √3/2)`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)

namespace Cvs.Prolate.Gram.DeepCellFloorAmplitude
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.EquilibriumPotential (tE wA psiA)

/-! ### The Agmon integral and `Δ_a` -/

/-- The Agmon integral `Ag(T, a) = ∫_{√T}^a √(t² − T)/√(1 − t²) dt` (zero when `a ≤ √T`). -/
def agmonInt (T a : ℝ) : ℝ := ∫ t in √T..a, √(t ^ 2 - T) / √(1 - t ^ 2)

theorem integral_zero_of_le {T α β : ℝ} (hαβ : α ≤ β) (hβ : β ^ 2 ≤ T) (hα : 0 ≤ α) :
    ∫ t in α..β, √(t ^ 2 - T) / √(1 - t ^ 2) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · simp
  · rw [uIcc_of_le hαβ] at ht
    simp only
    rw [Real.sqrt_eq_zero_of_nonpos (show t ^ 2 - T ≤ 0 by nlinarith [ht.1, ht.2]), zero_div]

theorem intervalIntegrable_f {T α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1) :
    IntervalIntegrable (fun t => √(t ^ 2 - T) / √(1 - t ^ 2)) volume α β := by
  refine (ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_).intervalIntegrable
  rw [uIcc_of_le hαβ] at ht
  exact (Real.sqrt_pos.mpr (by nlinarith [ht.1, ht.2])).ne'

/-- **`Ag + Ψ_a = Δ_a`**: for `0 ≤ a`, `2a² < 1` and `0 ≤ T ≤ t_e(a)²`,
`Ag(T, a) + Ψ_a(T) = ½∫_{√T}^{t_e} √(t² − T)/√(1 − t²) dt`. -/
theorem agmonInt_add_psiA {a T : ℝ} (ha : 0 ≤ a) (ha2 : 2 * a ^ 2 < 1) (hT : 0 ≤ T) (hTe : T ≤ tE a ^ 2) :
    agmonInt T a + psiA a T = 1 / 2 * ∫ t in √T..tE a, √(t ^ 2 - T) / √(1 - t ^ 2) := by
  have hte := Cvs.Prolate.Gram.EquilibriumPotential.tE_lt_one ha2
  have hat := Cvs.Prolate.Gram.EquilibriumPotential.le_tE ha (by linarith)
  have hsT : √T ≤ tE a := by rw [← Real.sqrt_sq (Cvs.Prolate.Gram.EquilibriumPotential.tE_nonneg ha)]; exact Real.sqrt_le_sqrt hTe
  have hsT2 : √T ^ 2 = T := Real.sq_sqrt hT
  obtain ⟨-, hsplit⟩ := Cvs.Prolate.Gram.EquilibriumPotential.integral_wA_mul ha ha2 (g := fun t => √(t ^ 2 - T)) (by fun_prop)
  have hpsi : psiA a T = 1 / 2 * (-(∫ t in (0 : ℝ)..a, √(t ^ 2 - T) / √(1 - t ^ 2)) +
      ∫ t in a..tE a, √(t ^ 2 - T) / √(1 - t ^ 2)) := by
    unfold psiA
    rw [hsplit]
    congr 2
    · congr 1; refine intervalIntegral.integral_congr fun t _ => ?_; ring
    · refine intervalIntegral.integral_congr fun t _ => ?_; ring
  rw [hpsi]
  unfold agmonInt
  rcases le_total (√T) a with h | h
  · have e0 : ∫ t in (0 : ℝ)..a, √(t ^ 2 - T) / √(1 - t ^ 2) =
        ∫ t in √T..a, √(t ^ 2 - T) / √(1 - t ^ 2) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := √T)
        (intervalIntegrable_f le_rfl (Real.sqrt_nonneg T) (h.trans_lt (hat.trans_lt hte)))
        (intervalIntegrable_f (Real.sqrt_nonneg T) h (hat.trans_lt hte)),
        integral_zero_of_le (Real.sqrt_nonneg T) hsT2.le le_rfl, zero_add]
    rw [e0, ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (intervalIntegrable_f (Real.sqrt_nonneg T) h (hat.trans_lt hte)) (intervalIntegrable_f ha hat hte)]
    ring
  · have e0 : ∫ t in (0 : ℝ)..a, √(t ^ 2 - T) / √(1 - t ^ 2) = 0 :=
      integral_zero_of_le ha (by nlinarith [Real.sqrt_nonneg T]) le_rfl
    have e1 : ∫ t in √T..a, √(t ^ 2 - T) / √(1 - t ^ 2) = 0 := by
      rw [intervalIntegral.integral_symm, integral_zero_of_le h hsT2.le ha, neg_zero]
    have e2 : ∫ t in a..tE a, √(t ^ 2 - T) / √(1 - t ^ 2) = ∫ t in √T..tE a, √(t ^ 2 - T) / √(1 - t ^ 2) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := √T)
        (intervalIntegrable_f ha h (hsT.trans_lt hte)) (intervalIntegrable_f (ha.trans h) hsT hte),
        integral_zero_of_le h hsT2.le ha, zero_add]
    rw [e0, e1, e2]; ring

/-- `t_e(a) ≤ 24/25` for `a² ≤ 9/25`. -/
theorem tE_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ^ 2 ≤ 9 / 25) : tE a ≤ 24 / 25 := by
  have h1 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hsq : tE a ^ 2 ≤ (24 / 25) ^ 2 := by
    unfold tE; rw [mul_pow, mul_pow, Real.sq_sqrt h1]; nlinarith
  exact (pow_le_pow_iff_left₀ (Cvs.Prolate.Gram.EquilibriumPotential.tE_nonneg ha) (by norm_num) two_ne_zero).mp hsq

/-- **`Δ_a ≤ Δ + 2(t_e − √3/2)`**: for `½ ≤ a`, `a² ≤ 9/25` and `0 ≤ T ≤ ¾`,
`Ag(T, a) + Ψ_a(T) ≤ Δ(T) + 2(t_e(a) − √3/2)`. -/
theorem agmonInt_add_psiA_le {a T : ℝ} (ha : 1 / 2 ≤ a) (ha2 : a ^ 2 ≤ 9 / 25) (hT : 0 ≤ T) (hT3 : T ≤ 3 / 4) :
    agmonInt T a + psiA a T ≤ Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta T + 2 * (tE a - √3 / 2) := by
  have ha0 : 0 ≤ a := by linarith
  have ha2' : 2 * a ^ 2 < 1 := by linarith
  have hte := Cvs.Prolate.Gram.EquilibriumPotential.tE_lt_one ha2'
  have hte96 := tE_le ha0 ha2
  have hs3 : (√3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs3le : √3 / 2 ≤ tE a := by
    have hmono : tE (1 / 2) ≤ tE a := by
      unfold tE
      have h1 : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
      have hsq : (2 * (1 / 2) * √(1 - (1 / 2) ^ 2)) ^ 2 ≤ (2 * a * √(1 - a ^ 2)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by nlinarith)]
        have hq : 1 / 4 ≤ a ^ 2 := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show (0 : ℝ) ≤ 3 / 4 - a ^ 2 by linarith)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have h12 : tE (1 / 2) = √3 / 2 := by
      unfold tE
      rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num, show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num,
        Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
      ring
    linarith
  have hTe : T ≤ tE a ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hs3le 2
    linarith
  rw [agmonInt_add_psiA ha0 ha2' hT hTe, Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta_eq_integral hT3]
  have hsT : √T ≤ √3 / 2 := by rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ √3 / 2), hs3]; exact Real.sqrt_le_sqrt hT3
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := √3 / 2)
    (intervalIntegrable_f (Real.sqrt_nonneg T) hsT (by linarith)) (intervalIntegrable_f (by positivity) hs3le hte)]
  have hb : ∫ t in √3 / 2..tE a, √(t ^ 2 - T) / √(1 - t ^ 2) ≤ ∫ t in √3 / 2..tE a, (4 : ℝ) := by
    refine intervalIntegral.integral_mono_on hs3le (intervalIntegrable_f (by positivity) hs3le hte)
      intervalIntegrable_const fun t ht => ?_
    have ht1 : t ≤ 24 / 25 := ht.2.trans hte96
    have hp : (7 / 25 : ℝ) ≤ √(1 - t ^ 2) := by
      rw [show (7 / 25 : ℝ) = √((7 / 25) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [ht.1, Real.sqrt_nonneg 3])
    have ht0 : 0 ≤ t := (by positivity : (0 : ℝ) ≤ √3 / 2).trans ht.1
    have hn : √(t ^ 2 - T) ≤ 1 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by nlinarith)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hb
  linarith

/-! ### The two analytic inputs -/

/-- The rung polynomial `Q_j = ∏_{b ≠ j}(X − χ_b)`. -/
def Qj (x : ℕ) (j : Fin x) : ℝ[X] := ∏ b ∈ univ.erase j, (X - C (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b))

/-- `R_j(S) = Q_j(χ_j)/∏_{σ ∈ S}(χ_j − σ)`. -/
def Rj (x : ℕ) (j : Fin x) (S : Finset ℝ) : ℝ := (Qj x j).eval (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) / ∏ σ ∈ S, (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ)

theorem degree_Qj (x : ℕ) (j : Fin x) : (Qj x j).degree = ((x - 1 : ℕ) : WithBot ℕ) := by
  unfold Qj
  rw [degree_prod]
  simp only [degree_X_sub_C, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem eval_Qj_eq_zero (x : ℕ) (j : Fin x) {b : Fin x} (hb : b ≠ j) : (Qj x j).eval (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) = 0 := by
  unfold Qj
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩) (by simp)

/-- **The endpoint amplitude** (eq-cpb Lemma 9): for every `ρ, δ > 0`, eventually every deep rung has an endpoint
`a ∈ [½, ½ + ρ]` with `Y_j(a)² ≥ e^{−2c·Ag(T_j, a) − δc}`, `Y_j = √2h_{4j}`. -/
def AmpFloor : Prop :=
  ∀ ρ > 0, ∀ δ > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 3 / 4 →
    ∃ a ∈ Icc (1 / 2 : ℝ) (1 / 2 + ρ),
      Real.exp (-(2 * (2 * π * x) * agmonInt (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) a) - δ * (2 * π * x)) ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2

/-- **The discrete potential** (eq-cpb Lemmas 10, 11, Proposition 3 and §4): for every `δ > 0`, eventually for every
deep rung and every `a ∈ [½, 3/5]` there are at least `x` (and at most `x²`) Dirichlet nodes `y_σ(a) = 0` with
`R_j ≠ 0` and every residue `r_σ² ≤ R_j²e^{2cΨ_a(T_j) + δc}`. -/
def PotFloor : Prop :=
  ∀ δ > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 3 / 4 → ∀ a ∈ Icc (1 / 2 : ℝ) (3 / 5),
    ∃ S : Finset ℝ, (∀ σ ∈ S, regSol (sqC (2 * π * x)) σ a = 0) ∧ x ≤ S.card ∧ (S.card : ℝ) ≤ (x : ℝ) ^ 2 ∧
      Rj x j S ≠ 0 ∧ ∀ σ ∈ S, Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ ^ 2 ≤
        Rj x j S ^ 2 * Real.exp (2 * (2 * π * x) * psiA a (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) + δ * (2 * π * x))

/-! ### The assembly -/

/-- `4x² ≤ e^{ηx}` eventually, for `η > 0`. -/
theorem eventually_sq_le_exp {η : ℝ} (hη : 0 < η) : ∀ᶠ x : ℕ in atTop, 4 * (x : ℝ) ^ 2 ≤ Real.exp (η * x) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hη)
  have h2 := h.const_mul (4 / η ^ 2)
  rw [mul_zero] at h2
  filter_upwards [h2.eventually (gt_mem_nhds one_pos), eventually_gt_atTop 0] with x hx hx0
  simp only [Function.comp] at hx
  have hx' : 4 * (x : ℝ) ^ 2 * Real.exp (-(η * x)) < 1 := by
    have e : 4 / η ^ 2 * ((η * x) ^ 2 * Real.exp (-(η * x))) = 4 * (x : ℝ) ^ 2 * Real.exp (-(η * x)) := by
      field_simp
    rwa [e] at hx
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)] at hx'
  exact hx'.le

/-- **The deep cell floor from the endpoint amplitude and the discrete potential.** -/
theorem deepCellFloor_of_amp_pot (hA : AmpFloor) (hP : PotFloor) : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor := by
  intro ε hε
  -- the endpoint window
  have hcont : ContinuousAt tE (1 / 2) := by unfold tE; fun_prop
  obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := Metric.continuousAt_iff.mp hcont (ε / 16) (by positivity)
  set ρ := min (ρ₀ / 2) (1 / 10) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by norm_num)
  have h12 : tE (1 / 2) = √3 / 2 := by
    unfold tE
    rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num, show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num,
      Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
    ring
  have htE : ∀ a ∈ Icc (1 / 2 : ℝ) (1 / 2 + ρ), tE a - √3 / 2 ≤ ε / 16 := fun a ha => by
    have hd : dist a (1 / 2) < ρ₀ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [ha.1])]
      linarith [ha.2, min_le_left (ρ₀ / 2) (1 / 10)]
    have := hρ₀' hd
    rw [Real.dist_eq, h12] at this
    linarith [le_abs_self (tE a - √3 / 2)]
  set δ := ε / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsq := eventually_sq_le_exp (η := ε / 4 * (2 * π)) (by positivity)
  filter_upwards [hA ρ hρ0 δ hδ0, hP δ hδ0, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hsq] with x hAx hPx hx hsqx
  intro j hj
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  obtain ⟨a, ha, hamp⟩ := hAx j hj
  have ha35 : a ≤ 3 / 5 := ha.2.trans (by linarith [min_le_right (ρ₀ / 2) (1 / 10)])
  obtain ⟨S, hS, hxS, hSx, hR, hres⟩ := hPx j hj a ⟨ha.1, ha35⟩
  have ha1 : a < 1 := by linarith
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; exact j.elim0
    · exact h
  have hdeg : (Qj x j).degree < S.card := by
    rw [degree_Qj]
    exact_mod_cast (show x - 1 < S.card by omega)
  have hkey := Cvs.Prolate.Gram.DirichletDualFloorShifted.dirichlet_le_sigmaP hx j ha.1 ha1 S hS hdeg (fun b hb => eval_Qj_eq_zero x j hb)
  -- the levels
  have hT0 : 0 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j := by
    unfold Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT
    exact div_nonneg (Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec _ (Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j)).1)
      (by positivity)
  set T := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j with hT
  set K := 2 * c * psiA a T + δ * c with hK
  set R := Rj x j S with hRdef
  have hR2 : 0 < R ^ 2 := by positivity
  -- the denominator
  have hg : ∀ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2 ≤ 4 * (R ^ 2 * Real.exp K) := by
    intro σ hσ
    have hg4 := Cvs.Prolate.RegularSolutionEnergyComparability.quarter_le_dirG_sq (c := c) (by linarith [ha.1]) ha1 (hS σ hσ)
    have hg0 : 0 < Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ ^ 2 := by linarith
    rw [div_pow, div_le_iff₀ hg0]
    have := hres σ hσ
    have hRe : 0 ≤ R ^ 2 * Real.exp K := by positivity
    nlinarith
  have hD : ∑ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2 ≤ S.card * (4 * (R ^ 2 * Real.exp K)) := by
    have := Finset.sum_le_sum hg
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  -- the denominator is positive: some residue is nonzero
  have hDpos : 0 < ∑ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2 := by
    have hProd : ∏ σ ∈ S, (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ) ≠ 0 := by
      intro h0; apply hR; rw [hRdef, Rj, h0, div_zero]
    have hnot : ∀ σ ∈ S, Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≠ id σ := fun σ hσ h =>
      hProd (Finset.prod_eq_zero hσ (by rw [h]; simp))
    have hsum := Cvs.Prolate.Gram.RobinDualCertificate.sum_resid_div (Set.injOn_id (S : Set ℝ)) hdeg hnot
    obtain ⟨σ, hσ, hrσ⟩ : ∃ σ ∈ S, Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hR
      simp only [id] at hsum
      rw [hRdef, Rj, ← hsum]
      exact Finset.sum_eq_zero fun σ hσ => by rw [hall σ hσ, zero_div]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun σ _ => sq_nonneg _) hσ)
    have hgne := Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG_ne_zero (c := c) (by linarith [ha.1]) ha1 (hS σ hσ)
    positivity
  have hSpos : (0 : ℝ) < S.card := by
    have : 0 < S.card := lt_of_lt_of_le hx1 hxS
    exact_mod_cast this
  have hlow : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) / (4 * S.card) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) j := by
    refine le_trans ?_ hkey
    rw [mul_pow, div_le_div_iff₀ (by positivity) hDpos]
    have hexp : Real.exp (-K) * Real.exp K = 1 := by rw [← Real.exp_add]; simp
    calc Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) *
          ∑ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2
        ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) * (S.card * (4 * (R ^ 2 * Real.exp K))) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * R ^ 2 * (4 * S.card) * (Real.exp (-K) * Real.exp K) := by ring
      _ = _ := by rw [hexp, mul_one, hRdef, Rj]
  -- the exponent
  have hΔ := agmonInt_add_psiA_le ha.1 (by nlinarith [ha.1]) hT0 hj
  have htEa := htE a ha
  have hlog4 : Real.log (4 * S.card) ≤ ε / 4 * c := by
    have h1 : 4 * (S.card : ℝ) ≤ 4 * (x : ℝ) ^ 2 := by linarith
    have h2 := h1.trans hsqx
    rw [← Real.log_exp (ε / 4 * c)]
    have : ε / 4 * (2 * π) * (x : ℝ) = ε / 4 * c := by rw [hc]; ring
    rw [this] at h2
    exact Real.log_le_log (by positivity) h2
  have hfin : Real.exp (-(2 * c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta T) - ε * c) ≤
      Real.exp (-(2 * c * agmonInt T a) - δ * c) * Real.exp (-K) / (4 * S.card) := by
    rw [le_div_iff₀ (by positivity), ← Real.exp_add,
      show 4 * (S.card : ℝ) = Real.exp (Real.log (4 * S.card)) from (Real.exp_log (by positivity)).symm,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hK, hδ]
    nlinarith [mul_le_mul_of_nonneg_left hΔ hc0.le]
  calc Real.exp (-(2 * c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta T) - ε * c)
      ≤ Real.exp (-(2 * c * agmonInt T a) - δ * c) * Real.exp (-K) / (4 * S.card) := hfin
    _ ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) / (4 * S.card) := by
        gcongr
    _ ≤ _ := hlow

end Cvs.Prolate.Gram.DeepCellFloorAmplitude

end
