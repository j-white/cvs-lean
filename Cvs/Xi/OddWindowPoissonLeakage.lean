import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.ProlateFamilySpine
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.StepA.SpineOddMass
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Poisson on the window: the odd window is the leakage sum plus an exact defect

For `G` even and `C²` on `[−1, 1]`, `ψ = psi c G`, `a = 2π/c`, Poisson at every `θ > 0` off `aℕ` splits on the window
`θ ∈ [a, 1]` into the in-band modes `R_aW_ψ/√a` and the leakage sum `t_G(θ) = Σ_{m≥1} ψ(mθ)·1_{mθ > 1}` (the full
tail on `θ > 1`): `W_G − R_aW_G = t_G − aG(0)/(2θ) + ½∫G − R_aW_{G − ψ/√a}`. For the spine profile at `c = 2πx`
the defect profile is `G − √x·ψ = Σ_j a_j((1 − √λ_{2j})h_{2j} − α_j(1 − √λ₀)h₀)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Xi.OddWindowPoissonLeakage
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.L2a.FullTailConvergence (fullTail poissonPiece)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR)
open Cvs.Approximant.DeepIndexSpineSpan (spineG alpha)

/-! ### The leakage sum -/

/-- The leakage sum `t_G(θ) = Σ_{m ≥ 1} ψ(mθ)·1_{mθ > 1}`, `ψ = psi c G`, as the limit of partial sums. -/
def leak (c : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ :=
  limUnder atTop fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, (Ioi (1 : ℝ)).indicator (psi c G) (m * θ)

/-- **The leakage sum is the full tail beyond the window**: `fullTail (psi c G) = t_G·1_{(1, ∞)}`. -/
theorem fullTail_eq_indicator_leak (c : ℝ) (G : ℝ → ℝ) :
    fullTail (psi c G) = (Ioi (1 : ℝ)).indicator (leak c G) := by
  funext θ
  by_cases hθ : 1 < θ
  · rw [indicator_of_mem (show θ ∈ Ioi (1 : ℝ) from hθ), fullTail, ite_eq_left hθ, leak]
    congr 1
    funext M
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [indicator_of_mem (show (m : ℝ) * θ ∈ Ioi (1 : ℝ) from by
      show 1 < (m : ℝ) * θ; nlinarith)]
  · rw [indicator_of_notMem (show θ ∉ Ioi (1 : ℝ) from hθ), Cvs.Xi.EImageWindowPoisson.fullTail_of_le_one _ (not_lt.mp hθ)]

/-- The cosine transform rescales: `ψ_c(mθ) = ψ_{cθ/2}(2m)`. -/
theorem psi_rescale (c θ : ℝ) (G : ℝ → ℝ) (m : ℝ) : psi (c * θ / 2) G (m * 2) = psi c G (m * θ) := by
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  refine intervalIntegral.integral_congr fun s _ => ?_
  have h : c * θ / 2 * (m * 2) * s = c * (m * θ) * s := by ring
  simp only [h]

/-- **Poisson summation at every `θ > 0`**: for `G` even and `C²` on `[−1, 1]`, `a = 2π/c` and `θ ∉ aℕ`,
`Σ_{m=1}^{M} ψ(mθ) → E_G(θ) + aG(0)/(2θ) − ½∫G`. -/
theorem tendsto_sum_psi {G G₁ G₂ : ℝ → ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hlat : ∀ k : ℕ, θ ≠ k * (2 * π / c)) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c G (m * θ)) atTop
      (𝓝 (eimage (2 * π / c) G θ + 2 * π / c * G 0 / (2 * θ) - 1 / 2 * ∫ s in (-1 : ℝ)..1, G s)) := by
  have hpi := pi_pos
  set k := ⌊c * θ / (2 * π)⌋₊ with hkd
  have hx : 0 ≤ c * θ / (2 * π) := by positivity
  have hk1 : (k : ℝ) ≤ c * θ / (2 * π) := Nat.floor_le hx
  have hk2 : c * θ / (2 * π) < k + 1 := Nat.lt_floor_add_one _
  have hk : (k : ℝ) < c * θ / (2 * π) := by
    refine lt_of_le_of_ne hk1 fun h => hlat k ?_
    field_simp at h ⊢
    linarith
  have hc' : 0 < c * θ / 2 := by positivity
  have e2 : c * θ / 2 * 2 / (2 * π) = c * θ / (2 * π) := by ring
  have hT := Cvs.L2a.FullTailConvergence.tendsto_partial hg hg₁ hg₂c hc' (by norm_num : (1 : ℝ) < 2)
  rw [Cvs.L2a.FullTailConvergence.fullTail_eq_poissonPiece hg hg₁ hg₂c hc' (by norm_num : (1 : ℝ) < 2) (k := k)
    (by rw [e2]; exact hk) (by rw [e2]; exact hk2)] at hT
  have hP : poissonPiece (c * θ / 2) G k 2 = poissonPiece c G k θ := by
    unfold poissonPiece
    rw [show c * θ / 2 * 2 = c * θ by ring]
  rw [hP, Cvs.Xi.EImageWindowPoisson.poissonPiece_eq_eimage heven hc hθ hk hk2] at hT
  exact hT.congr fun M => Finset.sum_congr rfl fun m _ => psi_rescale c θ G m

/-- The modes split at `1/θ`: for `M ≥ ⌊1/θ⌋`, `Σ_{m ≤ M} Φ(mθ) = Σ_{m ≤ 1/θ} Φ(mθ) + Σ_{m ≤ M} Φ(mθ)·1_{mθ > 1}`. -/
theorem sum_split {Φ : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ) {M : ℕ} (hM : ⌊1 / θ⌋₊ ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)
      = ∑ m ∈ Finset.Icc 1 ⌊1 / θ⌋₊, Φ (m * θ)
        + ∑ m ∈ Finset.Icc 1 M, (Ioi (1 : ℝ)).indicator Φ (m * θ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have h0 : ∑ m ∈ Finset.Icc 1 ⌊1 / θ⌋₊, (Ioi (1 : ℝ)).indicator Φ (m * θ) = 0 := by
      refine Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h => ?_) _
      have hm : (m : ℝ) ≤ 1 / θ :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))
      have h1 : (m : ℝ) * θ ≤ 1 := by rwa [le_div_iff₀ hθ] at hm
      exact absurd (show 1 < (m : ℝ) * θ from h) (not_lt.mpr h1)
    rw [h0, add_zero]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    have hlt : 1 / θ < ((n + 1 : ℕ) : ℝ) :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast Nat.succ_le_succ hn)
    rw [div_lt_iff₀ hθ] at hlt
    rw [indicator_of_mem (show ((n + 1 : ℕ) : ℝ) * θ ∈ Ioi (1 : ℝ) from hlt)]
    ring

/-- **The leakage sum is the full sum less the in-band modes**: if `Σ_{m ≤ M} ψ(mθ) → S`, then
`t_G(θ) = S − Σ_{m ≤ 1/θ} ψ(mθ)`. -/
theorem leak_eq_of_tendsto {c : ℝ} {G : ℝ → ℝ} {θ S : ℝ} (hθ : 0 < θ)
    (h : Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c G (m * θ)) atTop (𝓝 S)) :
    leak c G θ = S - ∑ m ∈ Finset.Icc 1 ⌊1 / θ⌋₊, psi c G (m * θ) := by
  unfold leak
  refine Tendsto.limUnder_eq ((h.sub_const _).congr' ?_)
  filter_upwards [eventually_ge_atTop ⌊1 / θ⌋₊] with M hM
  rw [sum_split hθ hM]
  ring

/-- **The reciprocal window samples the profile in band**: on `θ ∈ [a, 1]`,
`R_aW_F(θ) = √a·Σ_{1 ≤ n ≤ 1/θ} F(nθ)`. -/
theorem reciprocal_window_apply {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1) (F : ℝ → ℝ) :
    reciprocal a (window a F) θ = √a * ∑ n ∈ Finset.Icc 1 ⌊1 / θ⌋₊, F (n * θ) := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply ha hθ, window, indicator_of_mem (Cvs.Xi.PhysicalReciprocalReflection.recip_mem_Icc ha hθ), eimage]
  have e1 : a / θ / a = 1 / θ := by field_simp
  have e2 : ∀ n : ℕ, (n : ℝ) * a / (a / θ) = n * θ := fun n => by field_simp
  simp only [e1, e2]
  field_simp

/-! ### The odd window on the window -/

/-- **Poisson on the window**: for `G` even and `C²` on `[−1, 1]`, `a = 2π/c`, `θ ∈ [a, 1]`, `θ ∉ aℕ`,
`W_G(θ) = R_aW_ψ(θ)/√a + t_G(θ) − aG(0)/(2θ) + ½∫G`. -/
theorem window_eq_poisson {G G₁ G₂ : ℝ → ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) {c θ : ℝ} (hc : 0 < c) (hθ : θ ∈ Icc (2 * π / c) 1)
    (hlat : ∀ k : ℕ, θ ≠ k * (2 * π / c)) :
    window (2 * π / c) G θ
      = reciprocal (2 * π / c) (window (2 * π / c) (psi c G)) θ / √(2 * π / c) + leak c G θ
        - 2 * π / c * G 0 / (2 * θ) + 1 / 2 * ∫ s in (-1 : ℝ)..1, G s := by
  have ha : 0 < 2 * π / c := by have := pi_pos; positivity
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hs : √(2 * π / c) ≠ 0 := (sqrt_pos.mpr ha).ne'
  rw [leak_eq_of_tendsto hθ0 (tendsto_sum_psi hg hg₁ hg₂c heven hc hθ0 hlat), reciprocal_window_apply ha hθ,
    window, indicator_of_mem hθ]
  field_simp
  ring

/-- **The odd window in Poisson form**: on `θ ∈ [a, 1]`, `θ ∉ aℕ`,
`W_G − R_aW_G = t_G − aG(0)/(2θ) + ½∫G − R_aW_{G − ψ/√a}`. -/
theorem window_sub_reciprocal {G G₁ G₂ : ℝ → ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) {c θ : ℝ} (hc : 0 < c) (hθ : θ ∈ Icc (2 * π / c) 1)
    (hlat : ∀ k : ℕ, θ ≠ k * (2 * π / c)) :
    window (2 * π / c) G θ - reciprocal (2 * π / c) (window (2 * π / c) G) θ
      = leak c G θ - 2 * π / c * G 0 / (2 * θ) + 1 / 2 * (∫ s in (-1 : ℝ)..1, G s)
        - reciprocal (2 * π / c) (window (2 * π / c) fun s => G s - psi c G s / √(2 * π / c)) θ := by
  have ha : 0 < 2 * π / c := by have := pi_pos; positivity
  have hs : √(2 * π / c) ≠ 0 := (sqrt_pos.mpr ha).ne'
  have h1 := reciprocal_window_apply ha hθ G
  have h2 := reciprocal_window_apply ha hθ (psi c G)
  have h3 := reciprocal_window_apply ha hθ fun s => G s - psi c G s / √(2 * π / c)
  beta_reduce at h3
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at h3
  rw [window_eq_poisson hg hg₁ hg₂c heven hc hθ hlat, h1, h2, h3]
  field_simp
  ring

/-! ### The spine profile -/

/-- The defect profile `Σ_j a_j((1 − √λ_{2j})h_{2j} − α_j(1 − √λ₀)h₀)` at `c = 2πx`. -/
def defectG (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) : ℝ :=
  ∑ j, a j * ((1 - √(lamR (2 * π * x) (2 * (j : ℕ)))) * rung (2 * π * x) (2 * (j : ℕ)) s
    - alpha (2 * π * x) j * (1 - √(lamR (2 * π * x) 0)) * rung (2 * π * x) 0 s)

/-- The rung levels of the spine profile exist at `80 ≤ 2πx`. -/
theorem exists_level {x : ℕ} (hx : 80 ≤ 2 * π * x) (i : Option (Cvs.Approximant.SpineSubspace.SF x)) :
    ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i) χ := by
  rcases i with _ | j
  · exact Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero _
  · exact Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.2 (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)⟩

/-- **`√λ_k = √x·μ_k`** for an even rung index at `c = 2πx`. -/
theorem sqrt_lamR_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : ℕ} (h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) k χ)
    (hk : Even k) : √(lamR (2 * π * x) k) = muR (2 * π * x) k / √(1 / x) := by
  have hc : 0 < 2 * π * (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hm := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h hk
  have e : 2 * π * (x : ℝ) / (2 * π) = x := by field_simp
  rw [lamR, Real.sqrt_sq (by positivity), e, one_div, Real.sqrt_inv, div_inv_eq_mul]

/-- **The defect profile in prolate form**: on `[−1, 1]`, `G_a − √x·ψ_a = Σ_j a_j((1 − √λ_{2j})h_{2j} − α_j(1 −
√λ₀)h₀)`. -/
theorem spineG_sub_psi {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    spineG (2 * π * x) a s - psi (2 * π * x) (spineG (2 * π * x) a) s / √(1 / x) = defectG x a s := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hsx : √(1 / (x : ℝ)) ≠ 0 := (sqrt_pos.mpr (one_div_pos.mpr hx0)).ne'
  have hev : ∀ i : Option (Cvs.Approximant.SpineSubspace.SF x), Even (Cvs.L2a.ProlateFamilySpine.kOf i) := by
    rintro (_ | j)
    · exact ⟨0, rfl⟩
    · exact even_two_mul _
  have h2 : ∀ i : Option (Cvs.Approximant.SpineSubspace.SF x),
      Cvs.L2a.ProlateFamilySpine.bOf (2 * π * x) a i * rung (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i) s
          - Cvs.L2a.ProlateFamilySpine.bOf (2 * π * x) a i * psi (2 * π * x) (rung (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i)) s / √(1 / x)
        = Cvs.L2a.ProlateFamilySpine.bOf (2 * π * x) a i
          * ((1 - √(lamR (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i))) * rung (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i) s) := by
    intro i
    rw [Cvs.Prolate.EvenRungsByIndex.psi_rung (exists_level hx i) s hs, sqrt_lamR_eq hx (exists_level hx i) (hev i)]
    field_simp
  rw [← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG (2 * π * x) a,
    Cvs.L2a.FullTailConvergence.psi_sum _ _ _ (fun i _ => Cvs.Approximant.DeepIndexSpineSpan.intervalIntegrable_rung (2 * π * x) _), Finset.sum_div,
    ← Finset.sum_sub_distrib]
  simp only [h2]
  rw [Fintype.sum_option]
  simp only [Cvs.L2a.ProlateFamilySpine.bOf, Cvs.L2a.ProlateFamilySpine.kOf, Option.elim, defectG]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The odd spine window in Poisson form**: at `80 ≤ 2πx`, almost everywhere,
`W_a − R_{1/x}W_a = 1_{[1/x, 1]}·(t_{G_a} − G_a(0)/(2xθ)) − R_{1/x}W_{D_a}`, `D_a` the defect profile. -/
theorem oddW_ae_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.StepA.SpineOddMass.oddW x a =ᵐ[volume] fun θ =>
      (Icc (1 / (x : ℝ)) 1).indicator (fun θ => leak (2 * π * x) (spineG (2 * π * x) a) θ
          - 1 / x * spineG (2 * π * x) a 0 / (2 * θ)) θ
        - reciprocal (1 / x) (window (1 / x) (defectG x a)) θ := by
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hsc := Cvs.Approximant.SpineFormOwnTailPairing.scale_inv hx
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, heven, hGi⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) a
  have hwin : window (1 / (x : ℝ)) (fun s => spineG (2 * π * x) a s
      - psi (2 * π * x) (spineG (2 * π * x) a) s / √(1 / x)) = window (1 / x) (defectG x a) := by
    unfold window
    rw [Cvs.Xi.EImageWindowPoisson.eimage_congr (one_div_pos.mpr hx0) fun s hs =>
      spineG_sub_psi hx a ⟨by linarith [hs.1], hs.2⟩]
  filter_upwards [Cvs.Xi.EImageWindowPoisson.ae_notMem_lattice (1 / (x : ℝ))] with θ hθ
  unfold Cvs.StepA.SpineOddMass.oddW Cvs.StepA.SpineOddMass.spineW
  by_cases hm : θ ∈ Icc (1 / (x : ℝ)) 1
  · have h := window_sub_reciprocal hg hg₁ hg₂c heven hc (θ := θ) (by rw [hsc]; exact hm)
      (by rw [hsc]; exact hθ)
    rw [hsc, hGi, hwin] at h
    rw [h, indicator_of_mem hm]
    ring
  · rw [indicator_of_notMem hm, Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hm, Cvs.Xi.PhysicalReciprocalReflection.reciprocal_of_notMem hm,
      Cvs.Xi.PhysicalReciprocalReflection.reciprocal_of_notMem hm]

end Cvs.Xi.OddWindowPoissonLeakage
