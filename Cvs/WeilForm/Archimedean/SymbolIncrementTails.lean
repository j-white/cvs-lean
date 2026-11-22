import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The symbol's increment, trapped by its integral tails

The deficit terms whose series is the symbol's increment from the origin are a decreasing function
of the pole with an elementary antiderivative, so `K` explicit terms plus the integral from the
next pole trap `archSymbol t − archSymbol 0` from below, and the integral from one pole earlier
traps it from above, for every frequency and every cutoff.
-/

noncomputable section

open Real Finset Filter Topology

namespace Cvs.WeilForm.Archimedean.SymbolIncrementTails

/-- The deficit term as a function of the pole: `b² / ((u + 1/4)((u + 1/4)² + b²))`. -/
def deficitTerm (b u : ℝ) : ℝ := b ^ 2 / ((u + 1 / 4) * ((u + 1 / 4) ^ 2 + b ^ 2))

/-- Its antiderivative, `log(u + 1/4) − log((u + 1/4)² + b²)/2`. -/
def deficitAnti (b u : ℝ) : ℝ := Real.log (u + 1 / 4) - Real.log ((u + 1 / 4) ^ 2 + b ^ 2) / 2

theorem digammaDeficit_eq_deficitTerm (t : ℝ) (k : ℕ) :
    Cvs.Zeta.digammaDeficit t k = deficitTerm (t / 2) k := by
  rw [Cvs.Zeta.digammaDeficit_eq]; unfold deficitTerm; ring

theorem deficitTerm_nonneg {b u : ℝ} (hu : 0 ≤ u) : 0 ≤ deficitTerm b u := by
  unfold deficitTerm; positivity

theorem deficitTerm_antitoneOn (b : ℝ) : AntitoneOn (deficitTerm b) (Set.Ici 0) := by
  intro u hu v hv huv
  unfold deficitTerm
  have hu0 : (0 : ℝ) ≤ u := hu
  have hv0 : (0 : ℝ) ≤ v := hv
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have h1 : u + 1 / 4 ≤ v + 1 / 4 := by linarith
  have h2 : (u + 1 / 4) ^ 2 ≤ (v + 1 / 4) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)

theorem hasDerivAt_deficitAnti (b : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (deficitAnti b) (deficitTerm b u) u := by
  have ha : 0 < u + 1 / 4 := by linarith
  have h1 : HasDerivAt (fun u : ℝ => Real.log (u + 1 / 4)) (1 / (u + 1 / 4)) u := by
    have := ((hasDerivAt_id u).add_const (1 / 4)).log ha.ne'
    simpa using this
  have h2 : HasDerivAt (fun u : ℝ => Real.log ((u + 1 / 4) ^ 2 + b ^ 2) / 2)
      ((2 * (u + 1 / 4)) / ((u + 1 / 4) ^ 2 + b ^ 2) / 2) u := by
    have hD : (u + 1 / 4) ^ 2 + b ^ 2 ≠ 0 := by positivity
    have hp : HasDerivAt (fun u : ℝ => (u + 1 / 4) ^ 2 + b ^ 2) (2 * (u + 1 / 4)) u := by
      have := (((hasDerivAt_id u).add_const (1 / 4)).pow 2).add_const (b ^ 2)
      simpa using this
    exact (hp.log hD).div_const 2
  unfold deficitAnti
  refine (h1.sub h2).congr_deriv ?_
  unfold deficitTerm
  field_simp
  ring

theorem integral_deficitTerm (b : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∫ u in x..y, deficitTerm b u = deficitAnti b y - deficitAnti b x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => ?_)]
  · have hc : ContinuousOn (deficitTerm b) (Set.Icc x y) := by
      unfold deficitTerm
      refine continuousOn_const.div₀ (by fun_prop) fun u hu => ?_
      have : 0 ≤ u := le_trans hx hu.1
      positivity
    exact hc.intervalIntegrable_of_Icc hxy
  · rw [Set.uIcc_of_le hxy] at hu
    exact hasDerivAt_deficitAnti b (le_trans hx hu.1)

/-- `−deficitAnti b u = log(1 + b²/(u + 1/4)²)/2`. -/
theorem neg_deficitAnti {b u : ℝ} (hu : 0 ≤ u) :
    -deficitAnti b u = Real.log (1 + b ^ 2 / (u + 1 / 4) ^ 2) / 2 := by
  unfold deficitAnti
  have ha : 0 < u + 1 / 4 := by linarith
  have e : 1 + b ^ 2 / (u + 1 / 4) ^ 2 = ((u + 1 / 4) ^ 2 + b ^ 2) / (u + 1 / 4) ^ 2 := by
    field_simp
  rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

theorem tendsto_deficitAnti (b : ℝ) : Tendsto (fun u : ℕ => deficitAnti b u) atTop (𝓝 0) := by
  have h : ∀ u : ℕ, deficitAnti b u = -(Real.log (1 + b ^ 2 / ((u : ℝ) + 1 / 4) ^ 2) / 2) := by
    intro u; rw [← neg_deficitAnti (Nat.cast_nonneg u)]; ring
  simp_rw [h]
  rw [show (0 : ℝ) = -(Real.log (1 + 0) / 2) by simp]
  refine (((Real.continuousAt_log (by norm_num)).tendsto.comp ?_).div_const 2).neg
  refine tendsto_const_nhds.add ?_
  have h1 : Tendsto (fun u : ℕ => ((u : ℝ) + 1 / 4) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  exact tendsto_const_nhds.div_atTop h1

/-- **The tail of the deficit series beyond `K`**, trapped by the integrals from `K` and `K − 1`. -/
theorem tail_bounds {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 1 ≤ K) :
    Real.log (1 + (t / 2) ^ 2 / ((K : ℝ) + 1 / 4) ^ 2) / 2
        ≤ ∑' k, Cvs.Zeta.digammaDeficit t (k + K)
      ∧ ∑' k, Cvs.Zeta.digammaDeficit t (k + K)
        ≤ Real.log (1 + (t / 2) ^ 2 / ((K : ℝ) - 3 / 4) ^ 2) / 2 := by
  set b := t / 2 with hb
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : Summable (Cvs.Zeta.digammaDeficit t) :=
    (Cvs.WeilForm.Archimedean.LevyTermsSum.hasSum_digammaDeficit t).summable
  have hs' : Summable fun k => Cvs.Zeta.digammaDeficit t (k + K) := (summable_nat_add_iff K).mpr hs
  have heq : ∀ k : ℕ, Cvs.Zeta.digammaDeficit t (k + K) = deficitTerm b ((K : ℝ) + k) := by
    intro k; rw [digammaDeficit_eq_deficitTerm]; congr 1; push_cast; ring
  have hnn : ∀ k : ℕ, 0 ≤ Cvs.Zeta.digammaDeficit t (k + K) := fun k => by
    rw [heq]; exact deficitTerm_nonneg (by positivity)
  constructor
  · -- lower: the integral from K to K + n, then n → ∞
    have hlim := hs'.hasSum.tendsto_sum_nat
    have hlow : Tendsto (fun n : ℕ => deficitAnti b ((K : ℝ) + n) - deficitAnti b K) atTop
        (𝓝 (0 - deficitAnti b K)) := by
      refine Tendsto.sub ?_ tendsto_const_nhds
      have := (tendsto_deficitAnti b).comp (tendsto_add_atTop_nat K)
      refine this.congr fun n => ?_
      simp [Function.comp, add_comm]
    have hK0 : (0 : ℝ) ≤ K := by linarith
    rw [zero_sub, neg_deficitAnti hK0] at hlow
    refine le_of_tendsto_of_tendsto hlow hlim (Eventually.of_forall fun n => ?_)
    have hmono : AntitoneOn (deficitTerm b) (Set.Icc (K : ℝ) (K + n)) :=
      (deficitTerm_antitoneOn b).mono fun u hu => le_trans hK0 hu.1
    have h := hmono.integral_le_sum
    rw [integral_deficitTerm b hK0 (by linarith)] at h
    refine le_trans h (le_of_eq ?_)
    exact Finset.sum_congr rfl fun k _ => (heq k).symm
  · -- upper: the integral from K − 1
    refine tsum_le_of_sum_range_le hnn fun n => ?_
    have hK1 : (0 : ℝ) ≤ (K : ℝ) - 1 := by linarith
    have hmono : AntitoneOn (deficitTerm b) (Set.Icc ((K : ℝ) - 1) ((K : ℝ) - 1 + n)) :=
      (deficitTerm_antitoneOn b).mono fun u hu => le_trans hK1 hu.1
    have h := hmono.sum_le_integral
    rw [integral_deficitTerm b hK1 (by linarith)] at h
    have e1 : ∑ i ∈ range n, deficitTerm b ((K : ℝ) - 1 + ((i + 1 : ℕ) : ℝ))
        = ∑ k ∈ range n, Cvs.Zeta.digammaDeficit t (k + K) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [heq]; push_cast; ring_nf
    rw [e1] at h
    have hanti : deficitAnti b ((K : ℝ) - 1 + n) ≤ 0 := by
      have hpos : 0 ≤ (K : ℝ) - 1 + n := by positivity
      have := neg_deficitAnti (b := b) hpos
      have hq : 0 ≤ b ^ 2 / ((K : ℝ) - 1 + n + 1 / 4) ^ 2 := by positivity
      have hlog : 0 ≤ Real.log (1 + b ^ 2 / ((K : ℝ) - 1 + n + 1 / 4) ^ 2) :=
        Real.log_nonneg (by linarith)
      linarith
    have e2 : -deficitAnti b ((K : ℝ) - 1) = Real.log (1 + b ^ 2 / ((K : ℝ) - 3 / 4) ^ 2) / 2 := by
      rw [neg_deficitAnti hK1]; ring_nf
    linarith

/-- **The symbol's increment from the origin**, trapped by `K` terms and the integral tails. -/
theorem increment_bounds {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ range K, Cvs.Zeta.digammaDeficit t k
        + Real.log (1 + (t / 2) ^ 2 / ((K : ℝ) + 1 / 4) ^ 2) / 2
      ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
    ∧ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      ≤ ∑ k ∈ range K, Cvs.Zeta.digammaDeficit t k
        + Real.log (1 + (t / 2) ^ 2 / ((K : ℝ) - 3 / 4) ^ 2) / 2 := by
  have hs : Summable (Cvs.Zeta.digammaDeficit t) :=
    (Cvs.WeilForm.Archimedean.LevyTermsSum.hasSum_digammaDeficit t).summable
  have hsplit := hs.sum_add_tsum_nat_add K
  have hsum : ∑' k, Cvs.Zeta.digammaDeficit t k
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 := by
    rw [Cvs.WeilForm.Archimedean.LevyTermsSum.tsum_digammaDeficit]
    unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
    ring
  have h := tail_bounds ht hK
  constructor <;> linarith

end Cvs.WeilForm.Archimedean.SymbolIncrementTails
