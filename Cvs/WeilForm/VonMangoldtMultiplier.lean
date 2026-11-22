import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.EffectiveSymbol
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PolePrimeCosineMultipliers
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormSingleMultiplier
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form at scale `x` as the von Mangoldt multiplier `Φ_x`

`Φ_x(t) = poleSymbol (log x) t + archSymbol t − Σ_{n ≤ x} 2Λ(n) n^{−1/2} cos(t log n)` differs from the
truncated `windowSymbol (log x)` by band-free prime powers `p^r > x`, so `Q_x(w) = ∫ Φ_x ρ_w`; for `h ∈ bandFree
(log x)`, `b ≤ Φ_x + h` gives `b‖w‖² ≤ Q_x(w)`, `Φ_x + h ≥ −ε` at arbitrarily large `x` gives RH, and
`Ψ ≤ Φ_x + h` makes `M_Ψ` an operator floor iff `M_Ψ ≥ 0` on `R_Fᗮ`.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped InnerProductSpace
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open Cvs.WeilForm.WindowRepresentative (rep)
open Cvs.WeilForm.WindowFormSingleMultiplier (windowSymbol)

namespace Cvs.WeilForm.VonMangoldtMultiplier
open Cvs.ZeroCounting

/-! ### The prime channel in von Mangoldt form -/

/-- **The von Mangoldt symbol** `Σ_{n ≤ x} 2Λ(n) n^{−1/2} cos(t log n)`. -/
def vonMangoldtSymbol (x : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1),
    2 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2) : ℝ)) * Real.cos (t * Real.log n)

/-- `primeSymbol P R t = Σ_{k} 2Λ(k) k^{−1/2} cos(t log k)` over the prime powers `k = p^r`, `p ≤ P`, `r ≤ R`. -/
theorem primeSymbol_eq_sum (P R : ℕ) (t : ℝ) :
    Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t = ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
      2 * (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 / 2) : ℝ)) * Real.cos (t * Real.log k) := by
  rw [Cvs.WeilForm.PolePrimeCosineMultipliers.primeSymbol_eq_integral, Cvs.WeilForm.PolePrimeCosineMultipliers.integral_primeMeasure, Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show t * -Real.log k = -(t * Real.log k) by ring, Real.cos_neg]
  ring

/-- `log x ≤ ⌈log₂ x⌉ log 2`. -/
theorem log_le_clog_mul_log_two (x : ℕ) : Real.log x ≤ (Nat.clog 2 x : ℝ) * Real.log 2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [Nat.cast_zero, Real.log_zero]; positivity
  · rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast hx) (by exact_mod_cast Nat.le_pow_clog one_lt_two x)

/-- `log` is monotone on the naturals. -/
theorem log_natCast_le {m n : ℕ} (h : m ≤ n) : Real.log m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-- **The prime powers beyond `x` are band-free**: `primeSymbol P R − vonMangoldtSymbol x ∈ bandFree (log x)`
whenever the truncation reaches every prime power `≤ x`. -/
theorem primeSymbol_sub_mem_bandFree {x P R : ℕ} (hP : x ≤ P) (hR : Real.log x ≤ R * Real.log 2) :
    (fun t => Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t - vonMangoldtSymbol x t) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x) := by
  classical
  set I := Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R
  set c : ℕ → ℝ := fun k => 2 * (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 / 2) : ℝ))
  have hlow : ∀ t, vonMangoldtSymbol x t = ∑ k ∈ I.filter (· ≤ x), c k * Real.cos (t * Real.log k) := by
    intro t
    refine (Finset.sum_subset (fun k hk => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_filter.1 hk).2))
      fun n hn hnI => ?_).symm
    have hnx : n ≤ x := Nat.le_of_lt_succ (Finset.mem_range.1 hn)
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp only [hΛ, zero_mul, mul_zero]
    · exact absurd (Finset.mem_filter.2 ⟨Cvs.WeilForm.ThetaFormWindowIdentification.mem_primePowIndex hΛ (hnx.trans hP)
        ((log_natCast_le hnx).trans hR), hnx⟩) hnI
  have e : (fun t => Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t - vonMangoldtSymbol x t)
      = ∑ k ∈ I.filter (fun k => ¬ k ≤ x), c k • fun t => Real.cos (t * Real.log k) := by
    funext t
    rw [primeSymbol_eq_sum, hlow, ← Finset.sum_filter_add_sum_filter_not I (· ≤ x), Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, c]
    ring
  rw [e]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Cvs.WeilForm.BandFreedomCosine.cos_mem_bandFree ?_)
  have hxk : x < k := not_le.1 (Finset.mem_filter.1 hk).2
  exact (log_natCast_le hxk.le).trans (le_abs_self _)

/-! ### The multiplier at scale `x` -/

/-- **The window multiplier at scale `x`**:
`Φ_x(t) = poleSymbol (log x) t + archSymbol t − Σ_{n ≤ x} 2Λ(n) n^{−1/2} cos(t log n)`. -/
def scaleSymbol (x : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol (Real.log x) t + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - vonMangoldtSymbol x t

/-- `Φ_x` differs from `windowSymbol (log x) P R` by a band-free term whenever the truncation `(P, R)` reaches
every prime power `≤ x`. -/
theorem windowSymbol_sub_scaleSymbol_mem_bandFree {x P R : ℕ} (hP : x ≤ P) (hR : Real.log x ≤ R * Real.log 2) :
    (fun t => windowSymbol (Real.log x) P R t - scaleSymbol x t) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x) := by
  convert neg_mem (primeSymbol_sub_mem_bandFree hP hR) using 1
  funext t
  simp only [Pi.neg_apply, windowSymbol, scaleSymbol, Cvs.WeilForm.EffectiveSymbol.effSymbol]
  ring

/-- The band-free difference `Φ_x^{trunc} − Φ_x` at the project's truncation `(x, ⌈log₂ x⌉)`. -/
theorem windowSymbol_sub_scaleSymbol_mem_bandFree_clog (x : ℕ) :
    (fun t => windowSymbol (Real.log x) x (Nat.clog 2 x) t - scaleSymbol x t) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree (Real.log x) :=
  windowSymbol_sub_scaleSymbol_mem_bandFree le_rfl (log_le_clog_mul_log_two x)

/-- `Φ_x` is an admissible multiplier on `Dom x`. -/
theorem scaleSymbol_mem_admissible (x : ℕ) :
    scaleSymbol x ∈ Cvs.WeilForm.AdmissibleMultiplierMinorants.admissible (Cvs.WeilForm.AdmissibleMultiplierMinorants.formSpec (Real.log_natCast_nonneg x)) volume := by
  convert sub_mem (Cvs.WeilForm.WindowFormSingleMultiplier.windowSymbol_mem_admissible (Real.log_natCast_nonneg x) x (Nat.clog 2 x))
    (Cvs.WeilForm.AdmissibleMultiplierMinorants.bandFree_le_admissible _ (windowSymbol_sub_scaleSymbol_mem_bandFree_clog x)) using 1
  funext t; simp only [Pi.sub_apply]; ring

/-- **The window form at scale `x` is the multiplier `Φ_x`**: `Q_x(w) = ∫ Φ_x ρ_w`. -/
theorem Qx_eq_integral (x : ℕ) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x w = ∫ t, scaleSymbol x t * specDensity (rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) t := by
  set f := rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  have hb := windowSymbol_sub_scaleSymbol_mem_bandFree_clog x
  have hf1 := Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  have hf2 := Cvs.WeilForm.WindowRepresentative.memLp_rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  have hfs := Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero (Real.log_natCast_nonneg x) w
  have iW : Integrable fun t => windowSymbol (Real.log x) x (Nat.clog 2 x) t * specDensity f t := by
    simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using
      Cvs.WeilForm.WindowFormSingleMultiplier.integrable_windowSymbol_mul_crossSpec (Real.log x) x (Nat.clog 2 x) hf1 hf2 (Cvs.WeilForm.FormDomain.hdom_of_mem w)
        hf1 hf2 (Cvs.WeilForm.FormDomain.hdom_of_mem w)
  have iD : Integrable fun t => (windowSymbol (Real.log x) x (Nat.clog 2 x) t - scaleSymbol x t)
      * specDensity f t := by
    simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using Cvs.WeilForm.BandFreedomCosine.integrable_mul_crossSpec hb hf1 hf2 hf1 hf2
  have h0 := Cvs.WeilForm.BandFreedomCosine.integral_mul_specDensity_eq_zero hb hf1 hf2 hfs (sub_zero _).le
  show Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) w = _
  rw [Cvs.WeilForm.WindowFormSingleMultiplier.Q_eq_integral, show (fun t => scaleSymbol x t * specDensity f t)
      = fun t => windowSymbol (Real.log x) x (Nat.clog 2 x) t * specDensity f t
        - (windowSymbol (Real.log x) x (Nat.clog 2 x) t - scaleSymbol x t) * specDensity f t
      from funext fun t => by ring, integral_sub iW iD, h0, sub_zero]

end Cvs.WeilForm.VonMangoldtMultiplier
