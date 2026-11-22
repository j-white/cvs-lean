import Mathlib
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.LayerFloorTraceBound
import Cvs.Upstream.PencilLayerBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (EF′) at every cut `T₀ < 1` from the cell floors `σ'_j` and the top plunge

`R_{T₀} = Σ_{T_k < T₀} δ_k/F_k ≤ Σ_{T_k < T₀} Σ_{j ≥ k} μ_k/σ'_j` (trace bound), `μ_k ≤ 2(1 − λ_k)/(1 − λ_t)`.
A deep pair (`T_j ≤ ¾`) uses `μ_k ≤ μ_j`, the sharp plunge and `σ'_j ≥ e^{−2cΔ − o(c)}` with margin
`W − 2Δ ≥ W(¾) − 2Δ(¾) > 0`; a band pair uses `1 − λ_k ≲ ce^{−πc(1 − T₀)/4}` and `σ'_j ≥ e^{−o(c)}`.
Each pair is `O(c e^{−κc/2})`, `κ = min(W(¾) − 2Δ(¾), π(1 − T₀)/4)`, so `R_{T₀} = O(x³e^{−κπx}) → 0`.
-/

noncomputable section

open Real Set Filter Matrix Finset Topology

namespace Cvs.Prolate.Gram.DeepRemainderCellFloors
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram cellGram_posDef mu muInc lam lamTop levT)
open Cvs.Prolate.TunnellingExponentSharpPlunge (tunW tunDelta tunGap)

/-! ### The analytic inputs -/

/-- **Deep cell floor (eq-cpb M25(i)(a))**: for every `ε > 0`, eventually every rung with `T_j ≤ ¾` has
`σ'_j ≥ e^{−2cΔ(T_j) − εc}`, `c = 2πx`. -/
def DeepCellFloor : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, levT x j ≤ 3 / 4 →
    Real.exp (-(2 * (2 * π * x) * tunDelta (levT x j)) - ε * (2 * π * x)) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j

/-- **Band cell floor (eq-cpb M25(i)(c))**: for every `ε > 0`, eventually every rung with `T_j ≥ ¾` has
`σ'_j ≥ e^{−εc}`. -/
def BandCellFloor : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, 3 / 4 ≤ levT x j →
    Real.exp (-(ε * (2 * π * x))) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j

/-- **Top plunge floor (w-kstar Lemma W)**: for every `ε > 0`, eventually `1 − λ_t ≥ e^{−εc}`. -/
def TopPlungeFloor : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, Real.exp (-(ε * (2 * π * x))) ≤ 1 - lamTop x

/-! ### The weights -/

/-- `μ` is monotone along the rungs: `μ_k ≤ μ_j` for `k ≤ j < x`. -/
theorem mu_mono {x : ℕ} (hx : 80 ≤ 2 * π * x) {k j : Fin x} (hkj : k ≤ j) : mu x k ≤ mu x j := by
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_eq_sum x k, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_eq_sum x j]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.muInc_nonneg hx i.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hkj

/-- `δ_k ≤ μ_k`. -/
theorem muInc_le_mu {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : ℕ} (hk : k < x) : muInc x k ≤ mu x k := by
  unfold muInc
  split_ifs with h
  · simp
  · linarith [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_nonneg hx (show k - 1 < x by omega)]

/-- `μ_k ≤ 2(1 − λ_k)/(1 − λ_t)`. -/
theorem mu_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : ℕ} (hk : k < x) :
    mu x k ≤ 2 * (1 - lam x k) / (1 - lamTop x) := by
  have ht := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have hl := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx hk
  have h1 : 1 ≤ (1 + √(lam x k)) ^ 2 := by nlinarith [Real.sqrt_nonneg (lam x k)]
  have hω : 0 ≤ 1 - lam x k := by linarith
  have ht' : 0 < 1 - lamTop x := by linarith
  unfold mu
  rw [div_le_div_iff₀ (mul_pos ht' (by positivity)) ht']
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hω) ht'.le)
  nlinarith

/-! ### Scalar estimates -/

/-- `(y + 2)e^{−y} ≤ 2` for `y ≥ 0`. -/
theorem add_two_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) : (y + 2) * Real.exp (-y) ≤ 2 := by
  have h := Real.add_one_le_exp y
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos y)]
  linarith

/-- **The deep pair**: from the sharp plunge, the deep floor and the top floor,
`2ω/(ω_t σ) ≤ 4Ac·e^{−cg + 2εc}` whenever `W = 2Δ + G` with `G ≥ g` and `W ≥ 0`. -/
theorem deep_pair_le {A c W Δ G g ε ω σ ωt : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hW0 : 0 ≤ W) (hWeq : W = 2 * Δ + G)
    (hG : g ≤ G) (hω : ω ≤ A * c * (c * W + 2) * Real.exp (-(2 * (c * W))))
    (hσ : Real.exp (-(2 * c * Δ) - ε * c) ≤ σ) (hωt : Real.exp (-(ε * c)) ≤ ωt) :
    2 * ω / ωt * (1 / σ) ≤ 4 * A * c * Real.exp (-(c * g) + 2 * (ε * c)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (Real.exp_pos _) hσ
  have hωt0 : 0 < ωt := lt_of_lt_of_le (Real.exp_pos _) hωt
  have i1 : 1 / σ ≤ Real.exp (2 * c * Δ + ε * c) := by
    rw [div_le_iff₀ hσ0]
    calc (1 : ℝ) = Real.exp (2 * c * Δ + ε * c) * Real.exp (-(2 * c * Δ) - ε * c) := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hσ (Real.exp_pos _).le
  have i2 : 1 / ωt ≤ Real.exp (ε * c) := by
    rw [div_le_iff₀ hωt0]
    calc (1 : ℝ) = Real.exp (ε * c) * Real.exp (-(ε * c)) := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hωt (Real.exp_pos _).le
  have hy := add_two_mul_exp_neg_le (mul_nonneg hc.le hW0)
  have e : 2 * ω / ωt * (1 / σ) = 2 * ω * (1 / ωt) * (1 / σ) := by ring
  rw [e]
  have hcg : -(c * W) + 2 * c * Δ = -(c * G) := by rw [hWeq]; ring
  calc 2 * ω * (1 / ωt) * (1 / σ)
      ≤ 2 * (A * c * (c * W + 2) * Real.exp (-(2 * (c * W)))) * Real.exp (ε * c)
          * Real.exp (2 * c * Δ + ε * c) := by
        have h1 : 0 ≤ 1 / ωt := by positivity
        have h2 : 0 ≤ 1 / σ := by positivity
        have h3 : 0 ≤ A * c * (c * W + 2) * Real.exp (-(2 * (c * W))) := by
          have : 0 ≤ c * W := mul_nonneg hc.le hW0
          positivity
        gcongr
    _ = 2 * A * c * ((c * W + 2) * Real.exp (-(c * W)))
          * Real.exp ((-(c * W) + 2 * c * Δ) + 2 * (ε * c)) := by
        rw [show 2 * (A * c * (c * W + 2) * Real.exp (-(2 * (c * W)))) * Real.exp (ε * c)
            * Real.exp (2 * c * Δ + ε * c)
            = 2 * A * c * (c * W + 2) * (Real.exp (-(2 * (c * W))) * Real.exp (ε * c)
              * Real.exp (2 * c * Δ + ε * c)) by ring, ← Real.exp_add, ← Real.exp_add]
        rw [show 2 * A * c * ((c * W + 2) * Real.exp (-(c * W))) * Real.exp (-(c * W) + 2 * c * Δ + 2 * (ε * c))
            = 2 * A * c * (c * W + 2) * (Real.exp (-(c * W)) * Real.exp (-(c * W) + 2 * c * Δ + 2 * (ε * c)))
            by ring, ← Real.exp_add]
        congr 2; ring
    _ ≤ 2 * A * c * 2 * Real.exp (-(c * g) + 2 * (ε * c)) := by
        rw [hcg]
        have hexp : Real.exp (-(c * G) + 2 * (ε * c)) ≤ Real.exp (-(c * g) + 2 * (ε * c)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have : 0 ≤ 2 * A * c := by positivity
        calc 2 * A * c * ((c * W + 2) * Real.exp (-(c * W))) * Real.exp (-(c * G) + 2 * (ε * c))
            ≤ 2 * A * c * 2 * Real.exp (-(c * g) + 2 * (ε * c)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hy this) hexp (Real.exp_pos _).le (by positivity)
          _ = _ := rfl
    _ = 4 * A * c * Real.exp (-(c * g) + 2 * (ε * c)) := by ring

/-- **The band pair**: from the crude plunge on rung `k` and the band and top floors,
`2ω/(ω_t σ) ≤ 2Bc·e^{−πc(1 − T₀)/4 + 2εc}` once `c² − χ ≥ c²(1 − T₀)`. -/
theorem band_pair_le {B c D T₀ ε ω σ ωt : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hD : c ^ 2 * (1 - T₀) ≤ D)
    (hω : ω ≤ B * c * Real.exp (-(π * D / (4 * c))))
    (hσ : Real.exp (-(ε * c)) ≤ σ) (hωt : Real.exp (-(ε * c)) ≤ ωt) :
    2 * ω / ωt * (1 / σ) ≤ 2 * B * c * Real.exp (-(π * (1 - T₀) / 4 * c) + 2 * (ε * c)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (Real.exp_pos _) hσ
  have hωt0 : 0 < ωt := lt_of_lt_of_le (Real.exp_pos _) hωt
  have inv : ∀ {s : ℝ}, 0 < s → Real.exp (-(ε * c)) ≤ s → 1 / s ≤ Real.exp (ε * c) := by
    intro s hs h
    rw [div_le_iff₀ hs]
    calc (1 : ℝ) = Real.exp (ε * c) * Real.exp (-(ε * c)) := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hD' : Real.exp (-(π * D / (4 * c))) ≤ Real.exp (-(π * (1 - T₀) / 4 * c)) := by
    apply Real.exp_le_exp.mpr
    have : π * (1 - T₀) / 4 * c ≤ π * D / (4 * c) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hD Real.pi_pos.le
      nlinarith
    linarith
  have e : 2 * ω / ωt * (1 / σ) = 2 * ω * (1 / ωt) * (1 / σ) := by ring
  rw [e]
  calc 2 * ω * (1 / ωt) * (1 / σ)
      ≤ 2 * (B * c * Real.exp (-(π * (1 - T₀) / 4 * c))) * Real.exp (ε * c) * Real.exp (ε * c) := by
        have h1 : 0 ≤ 1 / ωt := by positivity
        have h2 : 0 ≤ 1 / σ := by positivity
        have h3 : ω ≤ B * c * Real.exp (-(π * (1 - T₀) / 4 * c)) :=
          hω.trans (mul_le_mul_of_nonneg_left hD' (by positivity))
        have h4 : 0 ≤ B * c * Real.exp (-(π * (1 - T₀) / 4 * c)) := by positivity
        gcongr
        · exact inv hωt0 hωt
        · exact inv hσ0 hσ
    _ = 2 * B * c * Real.exp (-(π * (1 - T₀) / 4 * c) + 2 * (ε * c)) := by
        rw [show 2 * (B * c * Real.exp (-(π * (1 - T₀) / 4 * c))) * Real.exp (ε * c) * Real.exp (ε * c)
          = 2 * B * c * (Real.exp (-(π * (1 - T₀) / 4 * c)) * Real.exp (ε * c) * Real.exp (ε * c)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 2; ring

/-! ### The pair bound and (EF′) -/

/-- **Every pair** `T_k < T₀`, `k ≤ j`: `δ_k/σ'_j ≤ (33/10)e⁵·c·e^{−κc/2}` once the three floors hold at `x` with
`4ε ≤ κ ≤ min(W(¾) − 2Δ(¾), π(1 − T₀)/4)` and `5c ≤ c²·min(1 − T₀, ¼)`. -/
theorem pair_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {T₀ ε κ : ℝ} (hκg : κ ≤ tunGap (3 / 4))
    (hκb : κ ≤ π * (1 - T₀) / 4) (hε : 4 * ε ≤ κ)
    (h5 : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 * (1 - T₀)) (h4 : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 / 4)
    (hDx : ∀ j : Fin x, levT x j ≤ 3 / 4 →
      Real.exp (-(2 * (2 * π * x) * tunDelta (levT x j)) - ε * (2 * π * x)) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j)
    (hBx : ∀ j : Fin x, 3 / 4 ≤ levT x j → Real.exp (-(ε * (2 * π * x))) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j)
    (hTx : Real.exp (-(ε * (2 * π * x))) ≤ 1 - lamTop x)
    {k j : Fin x} (hk : levT x k < T₀) (hkj : k ≤ j) :
    muInc x k * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j)
      ≤ 33 / 10 * Real.exp 5 * (2 * π * x) * Real.exp (-(κ / 2 * (2 * π * x))) := by
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hσ := Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos (cellGram_posDef hx) j
  have hinv : 0 ≤ 1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j := by positivity
  have hlevT : ∀ i : Fin x, Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (i : ℕ)) = levT x i * (2 * π * x) ^ 2 := fun i => by
    rw [levT, div_mul_cancel₀ _ (by positivity)]
  have h1 : muInc x k * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j) ≤ mu x k * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j) :=
    mul_le_mul_of_nonneg_right (muInc_le_mu hx k.2) hinv
  refine h1.trans ?_
  by_cases hj : levT x j ≤ 3 / 4
  · -- the deep pair
    have hmu : mu x k ≤ 2 * (1 - lam x j) / (1 - lamTop x) := (mu_mono hx hkj).trans (mu_le hx j.2)
    have hD : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) := by
      rw [hlevT j]; nlinarith
    have hP := Cvs.Prolate.TunnellingExponentSharpPlunge.one_sub_lamR_le_tunW hx (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j) hD
    have hpair := deep_pair_le (A := 33 / 40 * Real.exp 5) (by positivity) hc0 (Cvs.Prolate.TunnellingExponentSharpPlunge.tunW_nonneg _)
      (Cvs.Prolate.TunnellingExponentSharpPlunge.tunW_eq (levT x j)) (Cvs.Prolate.TunnellingExponentSharpPlunge.tunGap_anti hj) hP (hDx j hj) hTx
    calc mu x k * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j)
        ≤ 2 * (1 - lam x j) / (1 - lamTop x) * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j) :=
          mul_le_mul_of_nonneg_right hmu hinv
      _ ≤ 4 * (33 / 40 * Real.exp 5) * (2 * π * x)
            * Real.exp (-((2 * π * x) * tunGap (3 / 4)) + 2 * (ε * (2 * π * x))) := hpair
      _ ≤ 33 / 10 * Real.exp 5 * (2 * π * x) * Real.exp (-(κ / 2 * (2 * π * x))) := by
          rw [show 4 * (33 / 40 * Real.exp 5) = 33 / 10 * Real.exp 5 by ring]
          gcongr
          nlinarith
  · -- the band pair
    have hj' : 3 / 4 ≤ levT x j := (lt_of_not_ge hj).le
    have hmu : mu x k ≤ 2 * (1 - lam x k) / (1 - lamTop x) := mu_le hx k.2
    have hDk : (2 * π * x) ^ 2 * (1 - T₀) ≤ (2 * π * x) ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (k : ℕ)) := by
      rw [hlevT k]; nlinarith [sq_nonneg (2 * π * (x : ℝ))]
    have hP := Cvs.Prolate.Envelope.RungDuhamelRemainder.one_sub_lamR_le_exp hx (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx k) (h5.trans hDk)
    have hpair := band_pair_le (B := 33 / 20 * Real.exp 5) (by positivity) hc0 hDk hP (hBx j hj') hTx
    calc mu x k * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j)
        ≤ 2 * (1 - lam x k) / (1 - lamTop x) * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j) :=
          mul_le_mul_of_nonneg_right hmu hinv
      _ ≤ 2 * (33 / 20 * Real.exp 5) * (2 * π * x)
            * Real.exp (-(π * (1 - T₀) / 4 * (2 * π * x)) + 2 * (ε * (2 * π * x))) := hpair
      _ ≤ 33 / 10 * Real.exp 5 * (2 * π * x) * Real.exp (-(κ / 2 * (2 * π * x))) := by
          rw [show 2 * (33 / 20 * Real.exp 5) = 33 / 10 * Real.exp 5 by ring]
          gcongr
          nlinarith

/-- `x³e^{−ax} → 0` along the naturals for `a > 0`, in the form `x·(x·(K·2πx·e^{−(κ/2)2πx})) → 0`. -/
theorem tendsto_cube_exp {K κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun x : ℕ => (x : ℝ) * ((x : ℝ) * (K * (2 * π * x) * Real.exp (-(κ / 2 * (2 * π * x))))))
      atTop (𝓝 0) := by
  set a := κ * π with ha
  have ha0 : 0 < a := by positivity
  have h1 : Tendsto (fun x : ℕ => a * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha0
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp h1
  have h3 := h2.const_mul (K * 2 * π / a ^ 3)
  rw [mul_zero] at h3
  refine h3.congr fun x => ?_
  simp only [Function.comp]
  have e : -(κ / 2 * (2 * π * (x : ℝ))) = -(a * x) := by rw [ha]; ring
  rw [e]
  field_simp

/-- **(EF′) at every cut `T₀ < 1`** from the deep and band cell floors and the top plunge floor. -/
theorem efprime_of_cellFloors (hD : DeepCellFloor) (hB : BandCellFloor) (hT : TopPlungeFloor) {T₀ : ℝ}
    (hT₀ : T₀ < 1) : Cvs.Route.Visibility.LayerFloorDeepRemainderB.EFprime T₀ := by
  set κ := min (tunGap (3 / 4)) (π * (1 - T₀) / 4) with hκ
  have hκ0 : 0 < κ := lt_min Cvs.Prolate.TunnellingExponentSharpPlunge.tunGap_pos
    (div_pos (mul_pos Real.pi_pos (by linarith)) (by norm_num))
  have hε : 0 < κ / 4 := by positivity
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  set m := min (1 - T₀) (1 / 4) with hmdef
  have hm : 0 < m := lt_min (by linarith) (by norm_num)
  have h5 : ∀ᶠ x : ℕ in atTop, 5 / m ≤ 2 * π * x := hc.eventually_ge_atTop _
  refine squeeze_zero' ?_ ?_ (tendsto_cube_exp (K := 33 / 10 * Real.exp 5) hκ0)
  · filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hx
    exact Finset.sum_nonneg fun k _ => div_nonneg (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.muInc_nonneg hx k.2) (Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC_nonneg x k)
  · filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hD _ hε, hB _ hε, hT _ hε, h5] with x hx hDx hBx hTx h5x
    have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
    have hcm : 5 ≤ 2 * π * (x : ℝ) * m := by rwa [div_le_iff₀ hm] at h5x
    have hm1 : m ≤ 1 - T₀ := min_le_left _ _
    have hm2 : m ≤ 1 / 4 := min_le_right _ _
    have h5' : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 * (1 - T₀) := by nlinarith
    have h4' : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 / 4 := by nlinarith
    set P := 33 / 10 * Real.exp 5 * (2 * π * x) * Real.exp (-(κ / 2 * (2 * π * x))) with hP
    have hP0 : 0 ≤ P := by positivity
    have hk : ∀ k ∈ univ.filter (fun k : Fin x => levT x k < T₀),
        muInc x k / Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC x k ≤ x * P := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC_eq hx, div_eq_mul_one_div]
      calc muInc x k * (1 / Cvs.Upstream.PencilLayerBound.layerFloor (cellGram_posDef hx) k)
          ≤ muInc x k * ∑ j ∈ univ.filter (k ≤ ·), 1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j :=
            mul_le_mul_of_nonneg_left (Cvs.Upstream.LayerFloorTraceBound.inv_layerFloor_le_sum_sigmaP _ k) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.muInc_nonneg hx k.2)
        _ = ∑ j ∈ univ.filter (k ≤ ·), muInc x k * (1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) j) := Finset.mul_sum ..
        _ ≤ ∑ j ∈ univ.filter (k ≤ ·), P := by
            refine Finset.sum_le_sum fun j hj => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact pair_le hx (min_le_left _ _) (min_le_right _ _) (by linarith) h5' h4' hDx hBx hTx hk hj
        _ = (univ.filter (k ≤ ·)).card * P := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ x * P := by
            gcongr
            exact_mod_cast (Finset.card_le_univ _).trans (by simp)
    calc ∑ k ∈ univ.filter (fun k : Fin x => levT x k < T₀), muInc x k / Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC x k
        ≤ ∑ k ∈ univ.filter (fun k : Fin x => levT x k < T₀), (x * P) := Finset.sum_le_sum hk
      _ = (univ.filter (fun k : Fin x => levT x k < T₀)).card * (x * P) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x * (x * P) := by
          gcongr
          exact_mod_cast (Finset.card_le_univ _).trans (by simp)

end Cvs.Prolate.Gram.DeepRemainderCellFloors
