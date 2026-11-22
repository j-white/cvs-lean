import Mathlib
import Cvs.L2a.TailEdgeFarSplit
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Möbius inversion of the edge Poisson sum

The edge Poisson sum `F_e = Σ_m Φ_e(m·)` of the edge part `Φ_e = Φ·1_{[1,k)}` is inverted exactly on `(1, ∞)` by
`Φ_e(θ) = Σ_{d<k} μ(d) F_e(dθ)`, since `Σ_{d ∣ n} μ(d) = [n = 1]`; hence the edge part is bounded by its own Poisson
sum, `∫Φ_e² ≤ Q_k · Σ_{d<k} (1/d)∫_{(d,∞)} F_e² ≤ Q_k H_{k-1} ∫F_e²` with `Q_k` the number of squarefree `d < k`:
a Poisson sum cannot cancel its first mode by more than a factor depending on `k` alone.
-/

namespace Cvs.L2a.EdgePoissonMobius

open Real Set MeasureTheory ArithmeticFunction
open Cvs.L2a.TailOfModes Cvs.L2a.TailEdgeFarSplit

/-- The edge part of `Φ`: `Φ` below `k`, zero from `k` on. -/
noncomputable def edgePart (Φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := Set.indicator {x | x < (k : ℝ)} Φ

/-- For `θ > 1` and `k ≤ b` the edge Poisson sum is the plain sum of the edge part's dilates. -/
theorem edgeF_eq_sum (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} {k : ℕ} (hkb : (k : ℝ) ≤ b) {θ : ℝ} (hθ : 1 < θ) :
    edgeF Φ M b k θ = ∑ m ∈ Finset.Icc 1 M, edgePart Φ k (m * θ) := by
  unfold edgeF edgePart
  by_cases hmem : θ ∈ Ioc 1 b
  · rw [Set.indicator_of_mem hmem]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    by_cases h : (m : ℝ) * θ < k
    · rw [Set.indicator_of_mem (show θ ∈ {θ | θ < (k : ℝ) / m} from by
          show θ < (k : ℝ) / m; rw [lt_div_iff₀ hm0, mul_comm]; exact h),
        Set.indicator_of_mem (show (m : ℝ) * θ ∈ {x | x < (k : ℝ)} from h)]
    · rw [Set.indicator_of_notMem (show θ ∉ {θ | θ < (k : ℝ) / m} from by
          show ¬ θ < (k : ℝ) / m; rw [lt_div_iff₀ hm0, mul_comm]; exact h),
        Set.indicator_of_notMem (show (m : ℝ) * θ ∉ {x | x < (k : ℝ)} from h)]
  · rw [Set.indicator_of_notMem hmem]
    have hθb : b < θ := not_le.mp (fun h => hmem ⟨hθ, h⟩)
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    apply Set.indicator_of_notMem
    show ¬ (m : ℝ) * θ < k
    push Not
    refine le_of_lt ?_
    calc (k : ℝ) ≤ b := hkb
      _ < θ := hθb
      _ ≤ m * θ := le_mul_of_one_le_left (by linarith) hm1

/-- The divisor pairs of `n` inside the index box, when `n < k ≤ M`. -/
theorem fiber_eq_divisorsAntidiagonal {M k n : ℕ} (hkM : k ≤ M) (hn : 1 ≤ n) (hnk : n < k) :
    (Finset.Ico 1 k ×ˢ Finset.Icc 1 M).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have h1 : p.1 ∣ n := ⟨p.2, h.symm⟩
    have h2 : p.2 ∣ n := ⟨p.1, by rw [← h, mul_comm]⟩
    have hp1 := Nat.le_of_dvd (by omega) h1
    have hp2 := Nat.le_of_dvd (by omega) h2
    have hp1' : 1 ≤ p.1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h; omega)
    have hp2' : 1 ≤ p.2 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h; omega)
    exact ⟨⟨⟨hp1', by omega⟩, hp2', by omega⟩, h⟩

/-- **Möbius inversion of the edge Poisson sum**: for `θ > 1`, `k ≤ M` and `k ≤ b`,
`Σ_{d<k} μ(d) F_e(dθ) = Φ_e(θ)`. -/
theorem moebius_edge (Φ : ℝ → ℝ) {M : ℕ} {b : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b)
    {θ : ℝ} (hθ : 1 < θ) :
    ∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) * edgeF Φ M b k (d * θ) = edgePart Φ k θ := by
  -- expand each Poisson sum and write the double sum over the index box
  have hstep : ∀ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) * edgeF Φ M b k (d * θ)
      = ∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) * edgePart Φ k (((d * m : ℕ) : ℝ) * θ) := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Ico.mp hd).1
    rw [edgeF_eq_sum Φ M hkb (by nlinarith), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_product' (Finset.Ico 1 k) (Finset.Icc 1 M)
    (fun d m => (ArithmeticFunction.moebius d : ℝ) * edgePart Φ k (((d * m : ℕ) : ℝ) * θ))]
  -- regroup by the product `n = d m`
  have hmaps : ∀ p ∈ Finset.Ico 1 k ×ˢ Finset.Icc 1 M, p.1 * p.2 ∈ Finset.Icc 1 (k * M) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul (by omega) hp.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- each fiber is a Möbius divisor sum times the edge part at `nθ`
  have hfib : ∀ n ∈ Finset.Icc 1 (k * M),
      ∑ p ∈ (Finset.Ico 1 k ×ˢ Finset.Icc 1 M).filter (fun p : ℕ × ℕ => p.1 * p.2 = n),
        (ArithmeticFunction.moebius p.1 : ℝ) * edgePart Φ k (((p.1 * p.2 : ℕ) : ℝ) * θ)
      = if n = 1 then edgePart Φ k θ else 0 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hnθ : (n : ℝ) * θ < k
    · have hnk : n < k := by
        have : (n : ℝ) < k := lt_of_le_of_lt (le_mul_of_one_le_right (by positivity) hθ.le) hnθ
        exact_mod_cast this
      rw [Finset.sum_congr rfl (fun p hp => by
          rw [(Finset.mem_filter.mp hp).2]), ← Finset.sum_mul, fiber_eq_divisorsAntidiagonal hkM hn1 hnk,
        Nat.sum_divisorsAntidiagonal (fun d _ => (ArithmeticFunction.moebius d : ℝ))]
      have hmob := Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.sum_moebius_divisors n hn1
      have hmob' : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) = if n = 1 then 1 else 0 := by
        rw [← Int.cast_sum, hmob]; split_ifs <;> simp
      rw [hmob']
      split_ifs with h1
      · subst h1; simp
      · simp
    · have hzero : ∀ p ∈ (Finset.Ico 1 k ×ˢ Finset.Icc 1 M).filter (fun p : ℕ × ℕ => p.1 * p.2 = n),
          (ArithmeticFunction.moebius p.1 : ℝ) * edgePart Φ k (((p.1 * p.2 : ℕ) : ℝ) * θ) = 0 := by
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
        unfold edgePart
        rw [Set.indicator_of_notMem (show (n : ℝ) * θ ∉ {x | x < (k : ℝ)} from hnθ), mul_zero]
      rw [Finset.sum_eq_zero hzero]
      split_ifs with h1
      · subst h1
        unfold edgePart
        rw [Set.indicator_of_notMem (show θ ∉ {x | x < (k : ℝ)} from by simpa using hnθ)]
      · rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_ite_eq' (Finset.Icc 1 (k * M)) 1 (fun _ => edgePart Φ k θ),
    ite_eq_left (Finset.mem_Icc.mpr ⟨le_refl 1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))⟩)]

/-- **The edge part is bounded by its own Poisson sum**: `∫_{(1,∞)} Φ_e² ≤ Q_k · Σ_{d<k} (1/d) ∫_{(d,∞)} F_e²`,
`Q_k = Σ_{d<k} μ(d)²`, for an edge Poisson sum whose square is integrable on `(1, ∞)`. -/
theorem edgePart_sq_le (Φ : ℝ → ℝ) {M : ℕ} {b : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b)
    (hFe : IntegrableOn (fun θ => edgeF Φ M b k θ ^ 2) (Ioi 1)) :
    ∫ θ in Ioi 1, edgePart Φ k θ ^ 2
      ≤ (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2)
          * ∑ d ∈ Finset.Ico 1 k, (1 / (d : ℝ)) * ∫ θ in Ioi (d : ℝ), edgeF Φ M b k θ ^ 2 := by
  -- the square of the edge Poisson sum is integrable on the line, and so are its dilates
  have hFe' : Integrable (fun θ => edgeF Φ M b k θ ^ 2) := by
    refine hFe.integrable_of_forall_notMem_eq_zero (fun θ hθ => ?_)
    unfold edgeF
    rw [Set.indicator_of_notMem (fun (h : θ ∈ Ioc 1 b) => hθ (mem_Ioi.mpr h.1))]
    ring
  have hdil : ∀ d ∈ Finset.Ico 1 k, IntegrableOn (fun θ => edgeF Φ M b k ((d : ℝ) * θ) ^ 2) (Ioi 1) := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by
      have : 1 ≤ d := (Finset.mem_Ico.mp hd).1
      positivity
    exact (hFe'.comp_mul_left' hd0).integrableOn
  -- pointwise Cauchy–Schwarz on the Möbius inversion
  have hpt : ∀ θ ∈ Ioi (1 : ℝ), edgePart Φ k θ ^ 2
      ≤ (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2) * ∑ d ∈ Finset.Ico 1 k, edgeF Φ M b k ((d : ℝ) * θ) ^ 2 := by
    intro θ hθ
    rw [← moebius_edge Φ hk hkM hkb (mem_Ioi.mp hθ)]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hint : Integrable (fun θ => (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2)
      * ∑ d ∈ Finset.Ico 1 k, edgeF Φ M b k ((d : ℝ) * θ) ^ 2) (volume.restrict (Ioi 1)) :=
    (integrable_finsetSum _ hdil).const_mul _
  calc ∫ θ in Ioi 1, edgePart Φ k θ ^ 2
      ≤ ∫ θ in Ioi 1, (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2)
          * ∑ d ∈ Finset.Ico 1 k, edgeF Φ M b k ((d : ℝ) * θ) ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hint
          (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    _ = (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2)
          * ∑ d ∈ Finset.Ico 1 k, ∫ θ in Ioi 1, edgeF Φ M b k ((d : ℝ) * θ) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ hdil]
    _ = (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2)
          * ∑ d ∈ Finset.Ico 1 k, (1 / (d : ℝ)) * ∫ θ in Ioi (d : ℝ), edgeF Φ M b k θ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : (0 : ℝ) < d := by
          have : 1 ≤ d := (Finset.mem_Ico.mp hd).1
          positivity
        rw [integral_comp_mul_left_Ioi (fun θ => edgeF Φ M b k θ ^ 2) 1 hd0, mul_one, smul_eq_mul, one_div]

/-- **The cap on the edge cancellation**: `∫_{(1,∞)} Φ_e² ≤ Q_k · H_{k-1} · ∫_{(1,∞)} F_e²`, `H_{k-1} = Σ_{d<k} 1/d`. -/
theorem edgePart_sq_le_harm (Φ : ℝ → ℝ) {M : ℕ} {b : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b)
    (hFe : IntegrableOn (fun θ => edgeF Φ M b k θ ^ 2) (Ioi 1)) :
    ∫ θ in Ioi 1, edgePart Φ k θ ^ 2
      ≤ (∑ d ∈ Finset.Ico 1 k, (ArithmeticFunction.moebius d : ℝ) ^ 2) * (∑ d ∈ Finset.Ico 1 k, 1 / (d : ℝ))
          * ∫ θ in Ioi 1, edgeF Φ M b k θ ^ 2 := by
  refine (edgePart_sq_le Φ hk hkM hkb hFe).trans ?_
  rw [mul_assoc, Finset.sum_mul (Finset.Ico 1 k) (fun d => 1 / (d : ℝ)) (∫ θ in Ioi 1, edgeF Φ M b k θ ^ 2)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d hd => ?_)) (Finset.sum_nonneg (fun d _ => sq_nonneg (ArithmeticFunction.moebius d : ℝ)))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Ico.mp hd).1
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_set hFe (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi hd1))

end Cvs.L2a.EdgePoissonMobius
