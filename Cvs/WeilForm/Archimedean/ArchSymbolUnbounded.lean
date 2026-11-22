import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolTwiceScore
import Cvs.Zeta.Digamma
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth

/-!
# The archimedean symbol grows without bound

    ∀ c, ∃ T > 0, ∀ t, T ≤ |t| → c ≤ archSymbol t

Each digamma deficit reaches half its ceiling once `|t|` passes twice the depth, and the
ceilings sum like the harmonic series.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter

namespace Cvs.WeilForm.Archimedean.ArchSymbolUnbounded

/-- **Past twice the depth, a deficit is at least half its ceiling.** -/
theorem deficit_ge_half {k K : ℕ} (hk : k < K) {y : ℝ}
    (hy : 2 * (1 / 4 + (K : ℝ)) ≤ |y|) :
    (1 / 2) * (1 / (1 / 4 + (k : ℝ))) ≤ Cvs.Zeta.digammaDeficit y k := by
  have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk.le
  have ha : (0:ℝ) < 1 / 4 + (k : ℝ) := by positivity
  have hy2 : 1 / 4 + (k : ℝ) ≤ |y| / 2 := by
    have : 2 * (1 / 4 + (k : ℝ)) ≤ |y| := le_trans (by linarith) hy
    linarith
  have hsq : (1 / 4 + (k : ℝ)) ^ 2 ≤ (y / 2) ^ 2 := by
    have h1 : (0:ℝ) ≤ 1 / 4 + (k : ℝ) := ha.le
    have h2 : (|y| / 2) ^ 2 = (y / 2) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
    nlinarith [hy2, h1]
  rw [Cvs.Zeta.digammaDeficit_eq]
  have hden : (0:ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (y / 2) ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)]
  field_simp
  nlinarith [hsq, ha, hden]

/-- **The bank reaches half its ceiling.** -/
theorem bank_ge_half {K : ℕ} {y : ℝ} (hy : 2 * (1 / 4 + (K : ℝ)) ≤ |y|) :
    Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bankCeil K / 2 ≤ Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bank K y := by
  have hsum : ∑ k ∈ Finset.range K, (1 / 2) * (1 / (1 / 4 + (k : ℝ)))
      ≤ ∑ k ∈ Finset.range K, Cvs.Zeta.digammaDeficit y k :=
    Finset.sum_le_sum fun k hk => deficit_ge_half (Finset.mem_range.mp hk) hy
  rw [← Finset.mul_sum] at hsum
  rw [Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bank, Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bankCeil]
  linarith [hsum]

/-- **The ceilings diverge**, like the harmonic series. -/
theorem tendsto_bankCeil :
    Tendsto (fun K : ℕ => Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bankCeil K) atTop atTop := by
  have hcomp : ∀ K : ℕ, (∑ i ∈ Finset.range K, (1 / ((i : ℝ) + 1)))
      ≤ ∑ k ∈ Finset.range K, 1 / (1 / 4 + (k : ℝ)) := by
    intro K
    refine Finset.sum_le_sum fun k _ => ?_
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have hharm : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, 1 / (1 / 4 + (k : ℝ)))
      atTop atTop :=
    tendsto_atTop_mono hcomp Real.tendsto_sum_range_one_div_nat_succ_atTop
  have := hharm.atTop_div_const (by norm_num : (0:ℝ) < 2)
  simpa [Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bankCeil] using this

/-- **The archimedean symbol grows without bound.** -/
theorem exists_tail_bound (c : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ |t| → c ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  obtain ⟨K, hK⟩ := (tendsto_bankCeil.eventually_ge_atTop
    (c - 2 * Cvs.Detection.archScore 0)).exists
  refine ⟨max 1 (2 * (1 / 4 + (K : ℝ))), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro t ht
  have ht2 : 2 * (1 / 4 + (K : ℝ)) ≤ |t| := le_trans (le_max_right _ _) ht
  have hbank : Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bankCeil K / 2 ≤ Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.bank K t :=
    bank_ge_half ht2
  have hscore := Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth.archScore_ge K t
  rw [Cvs.WeilForm.Archimedean.SymbolTwiceScore.archSymbol_eq_two_mul_archScore]
  linarith

end Cvs.WeilForm.Archimedean.ArchSymbolUnbounded
