import Mathlib
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopTieTerm
import Cvs.StepA.OddTrialErrorBudget
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.TopQuadruple
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pairings of a top zero with the zeros off its top set, by dominated convergence

For `σ ∈ S`, `FiniteTop S δ`, `b = V_σ` and `L = log x`: `Σ_{ρ ∉ S} m_ρ⟪b, U_ρ⟫²/‖b‖⁴ → 0` and
`Σ_{ρ ∉ S} m_ρ⟪b, V_ρ⟫²/‖b‖⁴ → 0`, through the closed forms of Cvs.StepA.Edge.FiniteTopTieTerm, the domination
`m_ρ(16/γ_ρ² + [|γ_ρ| < 2|γ_σ| + 1]·4/(δ − |del ρ|)²)` and `‖b‖² ≥ (1/δ − 1/|γ_σ|)e^{δL}/16` eventually.
-/

noncomputable section

open Real MeasureTheory Filter Topology Asymptotics
open scoped InnerProductSpace
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop mult mult_nonneg)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopTieTerm (sinSinhC cosCoshC sinSinhInt cosCoshInt pairUe)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.OffTopPairingBound
open Cvs.ZeroCounting

/-! ### Two bounds on each closed window integral -/

/-- `cosh(bL/2)² ≤ e^{|b|L}` for `L ≥ 0`. -/
theorem cosh_half_sq_le_exp (b : ℝ) {L : ℝ} (hL : 0 ≤ L) : cosh (b * L / 2) ^ 2 ≤ exp (|b| * L) := by
  refine (Cvs.StepA.RestEnvelopeSmall.cosh_half_sq_le (b * L)).trans ((Cvs.StepA.OddTrialErrorBudget.cosh_le_exp_abs _).trans_eq ?_)
  rw [abs_mul, abs_of_nonneg hL]

/-- On the window `|t| ≤ L/2`, `L ≥ 0`, `|sinh(bt)| ≤ cosh(bL/2)` and `cosh(bt) ≤ cosh(bL/2)`. -/
theorem cosh_le_of_mem {b L t : ℝ} (hL : 0 ≤ L) (ht : t ∈ Set.uIoc (-(L / 2)) (L / 2)) :
    |sinh (b * t)| ≤ cosh (b * L / 2) ∧ cosh (b * t) ≤ cosh (b * L / 2) := by
  rw [Set.uIoc_of_le (by linarith)] at ht
  have hc : cosh (b * t) ≤ cosh (b * L / 2) := by
    rw [Real.cosh_le_cosh, abs_mul, show b * L / 2 = b * (L / 2) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ L / 2)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨ht.1.le, ht.2⟩) (abs_nonneg b)
  refine ⟨le_trans ?_ hc, hc⟩
  have h1 := Real.cosh_sq (b * t)
  have h2 := Real.cosh_pos (b * t)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (sinh (b * t) + cosh (b * t)), sq_nonneg (sinh (b * t) - cosh (b * t))]

/-- **Short-window bound**: `sinSinhC(a, b, L)² ≤ L² e^{|b|L}` for `L ≥ 0`. -/
theorem sinSinhC_sq_le_mul (a b : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    sinSinhC a b L ^ 2 ≤ L ^ 2 * exp (|b| * L) := by
  have h : ‖sinSinhInt a b L‖ ≤ cosh (b * L / 2) * |L / 2 - -(L / 2)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
      rw [Real.norm_eq_abs, abs_mul]
      have := (cosh_le_of_mem (b := b) hL ht).1
      nlinarith [Real.abs_sin_le_one (a * t), abs_nonneg (sinh (b * t)), abs_nonneg (sin (a * t))]
  rw [Real.norm_eq_abs, show L / 2 - -(L / 2) = L by ring, abs_of_nonneg hL,
    Cvs.StepA.Edge.FiniteTopTieTerm.sinSinhInt_eq] at h
  have hc := Real.cosh_pos (b * L / 2)
  have h2 : sinSinhC a b L ^ 2 ≤ (cosh (b * L / 2) * L) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h3 := cosh_half_sq_le_exp b hL
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg L)]

/-- **Short-window bound**: `cosCoshC(a, b, L)² ≤ L² e^{|b|L}` for `L ≥ 0`. -/
theorem cosCoshC_sq_le_mul (a b : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    cosCoshC a b L ^ 2 ≤ L ^ 2 * exp (|b| * L) := by
  have h : ‖cosCoshInt a b L‖ ≤ cosh (b * L / 2) * |L / 2 - -(L / 2)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos (b * t))]
      have := (cosh_le_of_mem (b := b) hL ht).2
      nlinarith [Real.abs_cos_le_one (a * t), Real.cosh_pos (b * t), abs_nonneg (cos (a * t))]
  rw [Real.norm_eq_abs, show L / 2 - -(L / 2) = L by ring, abs_of_nonneg hL,
    Cvs.StepA.Edge.FiniteTopTieTerm.cosCoshInt_eq] at h
  have h2 : cosCoshC a b L ^ 2 ≤ (cosh (b * L / 2) * L) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h3 := cosh_half_sq_le_exp b hL
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg L)]

/-- **Size of the cosine closed form**: `(a² + b²) cosCoshC(a, b, L)² ≤ 4 cosh²(bL/2)` for `a ≠ 0`. -/
theorem normSq_mul_cosCoshC_sq_le {a : ℝ} (ha : a ≠ 0) (b L : ℝ) :
    (a ^ 2 + b ^ 2) * cosCoshC a b L ^ 2 ≤ 4 * cosh (b * L / 2) ^ 2 := by
  have hpos : 0 < a ^ 2 + b ^ 2 := by positivity
  set s := sin (a * L / 2) with hs
  set c := cos (a * L / 2) with hc
  set C := cosh (b * L / 2) with hC
  set S := sinh (b * L / 2) with hS
  have hsc : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
  have hCS : C ^ 2 = S ^ 2 + 1 := Real.cosh_sq _
  have hN : (a * s * C + b * c * S) ^ 2 ≤ (a ^ 2 + b ^ 2) * C ^ 2 := by
    have h1 : (a * s * C + b * c * S) ^ 2 ≤ (a ^ 2 + b ^ 2) * ((s * C) ^ 2 + (c * S) ^ 2) := by
      nlinarith [sq_nonneg (a * c * S - b * s * C)]
    have h2 : (s * C) ^ 2 + (c * S) ^ 2 ≤ C ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg s]
    nlinarith [mul_le_mul_of_nonneg_left h2 hpos.le]
  have e : (a ^ 2 + b ^ 2) * cosCoshC a b L ^ 2 = 4 * (a * s * C + b * c * S) ^ 2 / (a ^ 2 + b ^ 2) := by
    rw [cosCoshC, if_neg hpos.ne', ← hs, ← hc, ← hC, ← hS]; field_simp; ring
  rw [e, div_le_iff₀ hpos]
  nlinarith [hN]

/-- **Long-window bound**: `sinSinhC(a, b, L)² ≤ (4/a²) cosh²(bL/2)` for `a ≠ 0`. -/
theorem sinSinhC_sq_le_div_cosh {a : ℝ} (ha : a ≠ 0) (b L : ℝ) :
    sinSinhC a b L ^ 2 ≤ 4 / a ^ 2 * cosh (b * L / 2) ^ 2 := by
  have h := Cvs.StepA.Edge.FiniteTopTieTerm.normSq_mul_sinSinhC_sq_le a b L
  have ha2 : 0 < a ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ha2]
  nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (sinSinhC a b L))]

/-- **Long-window bound**: `cosCoshC(a, b, L)² ≤ (4/a²) cosh²(bL/2)` for `a ≠ 0`. -/
theorem cosCoshC_sq_le_div_cosh {a : ℝ} (ha : a ≠ 0) (b L : ℝ) :
    cosCoshC a b L ^ 2 ≤ 4 / a ^ 2 * cosh (b * L / 2) ^ 2 := by
  have h := normSq_mul_cosCoshC_sq_le ha b L
  have ha2 : 0 < a ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ha2]
  nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (cosCoshC a b L))]

/-- `sinSinhC(a, b, L)² ≤ (4/a²) e^{|b|L}` for `a ≠ 0`, `L ≥ 0`. -/
theorem sinSinhC_sq_le_div {a : ℝ} (ha : a ≠ 0) (b : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    sinSinhC a b L ^ 2 ≤ 4 / a ^ 2 * exp (|b| * L) :=
  (sinSinhC_sq_le_div_cosh ha b L).trans
    (mul_le_mul_of_nonneg_left (cosh_half_sq_le_exp b hL) (by positivity))

/-- `cosCoshC(a, b, L)² ≤ (4/a²) e^{|b|L}` for `a ≠ 0`, `L ≥ 0`. -/
theorem cosCoshC_sq_le_div {a : ℝ} (ha : a ≠ 0) (b : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    cosCoshC a b L ^ 2 ≤ 4 / a ^ 2 * exp (|b| * L) :=
  (cosCoshC_sq_le_div_cosh ha b L).trans
    (mul_le_mul_of_nonneg_left (cosh_half_sq_le_exp b hL) (by positivity))

/-! ### The pairings through their four closed terms -/

/-- `((p + q + r + s)/4)² ≤ M` when each of `p², q², r², s²` is at most `M`. -/
theorem quarter_sum_sq_le {p q r s M : ℝ} (hp : p ^ 2 ≤ M) (hq : q ^ 2 ≤ M) (hr : r ^ 2 ≤ M)
    (hs : s ^ 2 ≤ M) : ((1 / 4) * (p + q + r + s)) ^ 2 ≤ M := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r),
    sq_nonneg (q - s), sq_nonneg (r - s)]

/-- `pairUe(L, z, z')² ≤ M` when `sinSinhC(γ ± γ', y ± y', L)² ≤ M` for all four sign choices. -/
theorem pairUe_sq_le {L M : ℝ} {z z' : ℂ}
    (h : ∀ a b : ℝ, (a = z.re + z'.re ∨ a = z.re - z'.re) → (b = z.im + z'.im ∨ b = z.im - z'.im) →
      sinSinhC a b L ^ 2 ≤ M) : pairUe L z z' ^ 2 ≤ M :=
  quarter_sum_sq_le (h _ _ (.inl rfl) (.inl rfl)) (h _ _ (.inl rfl) (.inr rfl))
    (h _ _ (.inr rfl) (.inl rfl)) (h _ _ (.inr rfl) (.inr rfl))

/-! ### One zero off the top set against `e^{2δL}` -/

/-- `L² e^{(D − ε)L} ≤ (4/ε²) e^{DL}` for `L ≥ 0`, `ε > 0`. -/
theorem sq_mul_exp_le {L ε D : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    L ^ 2 * exp ((D - ε) * L) ≤ 4 / ε ^ 2 * exp (D * L) := by
  have h1 : ε * L / 2 ≤ exp (ε * L / 2) := by linarith [Real.add_one_le_exp (ε * L / 2)]
  have h2 : (ε * L / 2) ^ 2 ≤ exp (ε * L) := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rwa [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (ε * L / 2) = ε * L by push_cast; ring] at this
  have e : exp (D * L) = exp ((D - ε) * L) * exp (ε * L) := by rw [← Real.exp_add]; ring_nf
  have hE := exp_pos ((D - ε) * L)
  rw [e, show L ^ 2 = 4 / ε ^ 2 * (ε * L / 2) ^ 2 by field_simp; ring]
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 / ε ^ 2)
  nlinarith

/-- Hypotheses on a family `f ρ L ≥ 0` off a finite set `S`: below `L²e^{(δ + |del ρ|)L}` for
`L ≥ 0`, and below `K/γ_ρ² · e^{(δ + |del ρ|)L}` for `L ≥ 0`, `|γ_ρ| ≥ R`. -/
structure OffTopBound (S : Finset nonTrivialZeroSet) (δ R K : ℝ) (f : nonTrivialZeroSet → ℝ → ℝ) : Prop where
  lt : ∀ ρ, ρ ∉ S → |Cvs.GaussKernel.del ρ| < δ
  K_nonneg : 0 ≤ K
  nonneg : ∀ (ρ : nonTrivialZeroSet) (L : ℝ), 0 ≤ f ρ L
  near : ∀ (ρ : nonTrivialZeroSet) (L : ℝ), 0 ≤ L → f ρ L ≤ L ^ 2 * exp ((δ + |Cvs.GaussKernel.del ρ|) * L)
  far : ∀ (ρ : nonTrivialZeroSet) (L : ℝ), 0 ≤ L → R ≤ |(ρ : ℂ).im| →
    f ρ L ≤ K * (1 / ((ρ : ℂ).im) ^ 2) * exp ((δ + |Cvs.GaussKernel.del ρ|) * L)

/-- The dominating weight `m_ρ(K/γ_ρ² + [|γ_ρ| < R]·4/(δ − |del ρ|)²)`. -/
def domW (δ R K : ℝ) (ρ : nonTrivialZeroSet) : ℝ :=
  mult ρ * (K * (1 / ((ρ : ℂ).im) ^ 2)
    + if |(ρ : ℂ).im| < R then 4 / (δ - |Cvs.GaussKernel.del ρ|) ^ 2 else 0)

/-- The dominating weight is summable over the nontrivial zeros. -/
theorem summable_domW (δ R K : ℝ) : Summable (domW δ R K) := by
  have h1 := Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq.mul_left K
  have h2 : Summable fun ρ : nonTrivialZeroSet => mult ρ
      * (if |(ρ : ℂ).im| < R then 4 / (δ - |Cvs.GaussKernel.del ρ|) ^ 2 else 0) := by
    refine summable_of_hasFiniteSupport ((Cvs.GaussKernel.finite_window R).subset fun ρ hρ => ?_)
    rw [Function.mem_support] at hρ
    simp only [Set.mem_ofPred_eq]
    by_contra h
    apply hρ
    have hg : Cvs.GaussKernel.gam ρ = (ρ : ℂ).im := rfl
    rw [hg] at h
    rw [if_neg fun h' => h h'.le, mul_zero]
  refine (h1.add h2).congr fun ρ => ?_
  simp only [domW, mult]
  ring

/-- **Pointwise domination**: under `OffTopBound`, `m_ρ f ρ L ≤ domW(ρ) e^{2δL}` for `ρ ∉ S`, `L ≥ 0`. -/
theorem mul_le_domW {S : Finset nonTrivialZeroSet} {δ R K : ℝ} {f : nonTrivialZeroSet → ℝ → ℝ}
    (hf : OffTopBound S δ R K f) {ρ : nonTrivialZeroSet} (hρ : ρ ∉ S) {L : ℝ} (hL : 0 ≤ L) :
    mult ρ * f ρ L ≤ domW δ R K ρ * exp (2 * δ * L) := by
  have hd := hf.lt ρ hρ
  have hε : 0 < δ - |Cvs.GaussKernel.del ρ| := sub_pos.2 hd
  have hm := mult_nonneg ρ
  have hK : 0 ≤ K * (1 / ((ρ : ℂ).im) ^ 2) := mul_nonneg hf.K_nonneg (by positivity)
  have hexp : exp ((δ + |Cvs.GaussKernel.del ρ|) * L) ≤ exp (2 * δ * L) :=
    exp_le_exp.2 (by nlinarith [abs_nonneg (Cvs.GaussKernel.del ρ)])
  have hsq := sq_mul_exp_le (D := 2 * δ) hL hε
  rw [show 2 * δ - (δ - |Cvs.GaussKernel.del ρ|) = δ + |Cvs.GaussKernel.del ρ| by ring] at hsq
  unfold domW
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hm
  have hE := exp_pos (2 * δ * L)
  split_ifs with hR
  · have := hf.near ρ L hL
    nlinarith [mul_nonneg hK hE.le]
  · have := hf.far ρ L hL (not_lt.1 hR)
    nlinarith [mul_le_mul_of_nonneg_left hexp hK]

/-- **Summability off `S`** under `OffTopBound`, at every `L ≥ 0`. -/
theorem summable_offTop {S : Finset nonTrivialZeroSet} {δ R K : ℝ} {f : nonTrivialZeroSet → ℝ → ℝ}
    (hf : OffTopBound S δ R K f) {L : ℝ} (hL : 0 ≤ L) :
    Summable fun ρ : {ρ // ρ ∉ S} => mult ρ * f ρ L :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (mult_nonneg _) (hf.nonneg _ _))
    (fun ρ => mul_le_domW hf ρ.2 hL)
    (((summable_domW δ R K).comp_injective Subtype.coe_injective).mul_right _)

/-- **Tannery off `S`**: under `OffTopBound`, `(Σ_{ρ ∉ S} m_ρ f ρ L)/e^{2δL} → 0` as `L → ∞`. -/
theorem tendsto_tsum_div_exp {S : Finset nonTrivialZeroSet} {δ R K : ℝ} {f : nonTrivialZeroSet → ℝ → ℝ}
    (hf : OffTopBound S δ R K f) :
    Tendsto (fun L => (∑' ρ : {ρ // ρ ∉ S}, mult ρ * f ρ L) / exp (2 * δ * L)) atTop (𝓝 0) := by
  have hpt : ∀ ρ : {ρ // ρ ∉ S}, Tendsto (fun L => mult ρ * f ρ L / exp (2 * δ * L)) atTop (𝓝 0) := by
    intro ρ
    have hε : 0 < δ - |Cvs.GaussKernel.del ρ| := sub_pos.2 (hf.lt ρ ρ.2)
    set ε := δ - |Cvs.GaussKernel.del ρ|
    have hlim : Tendsto (fun L => mult ρ * (1 / ε ^ 2) * ((ε * L) ^ 2 * exp (-(ε * L)))) atTop (𝓝 0) := by
      have := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp (tendsto_id.const_mul_atTop hε)
      have h2 := this.const_mul (mult ρ * (1 / ε ^ 2))
      rw [mul_zero] at h2
      exact h2
    refine squeeze_zero' (Eventually.of_forall fun L =>
      div_nonneg (mul_nonneg (mult_nonneg _) (hf.nonneg _ _)) (exp_pos _).le) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with L hL
    have h1 := hf.near ρ L hL
    have e : exp ((δ + |Cvs.GaussKernel.del ρ|) * L) = exp (2 * δ * L) * exp (-(ε * L)) := by
      rw [← Real.exp_add]; congr 1; simp only [ε]; ring
    have hE := exp_pos (2 * δ * L)
    rw [div_le_iff₀ hE]
    have hm := mult_nonneg ρ
    have : mult ρ * f ρ L ≤ mult ρ * (L ^ 2 * exp ((δ + |Cvs.GaussKernel.del ρ|) * L)) :=
      mul_le_mul_of_nonneg_left h1 hm
    rw [e] at this
    have e2 : mult ρ * (1 / ε ^ 2) * ((ε * L) ^ 2 * exp (-(ε * L))) * exp (2 * δ * L)
        = mult ρ * (L ^ 2 * (exp (2 * δ * L) * exp (-(ε * L)))) := by
      field_simp
    linarith
  have hdom : ∀ᶠ L in atTop, ∀ ρ : {ρ // ρ ∉ S},
      ‖mult ρ * f ρ L / exp (2 * δ * L)‖ ≤ domW δ R K ρ := by
    filter_upwards [eventually_ge_atTop 0] with L hL ρ
    have hE := exp_pos (2 * δ * L)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (mult_nonneg _) (hf.nonneg _ _)) hE.le),
      div_le_iff₀ hE]
    exact mul_le_domW hf ρ.2 hL
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_domW δ R K).comp_injective Subtype.coe_injective) hpt hdom
  rw [tsum_zero] at h
  exact h.congr fun L => tsum_div_const

/-! ### The pairings of a top zero satisfy the off-top bounds -/

/-- `|y ± y'| ≤ δ + |del ρ|` for `y = Im z_σ`, `y' = Im z_ρ`, `|del σ| = δ`. -/
theorem abs_im_pm_le {σ ρ : nonTrivialZeroSet} {δ : ℝ} (hσ : |Cvs.GaussKernel.del σ| = δ) {b : ℝ}
    (hb : b = (Cvs.ZeroCounting.zPoint σ).im + (Cvs.ZeroCounting.zPoint ρ).im
      ∨ b = (Cvs.ZeroCounting.zPoint σ).im - (Cvs.ZeroCounting.zPoint ρ).im) :
    |b| ≤ δ + |Cvs.GaussKernel.del ρ| := by
  have h1 : |(Cvs.ZeroCounting.zPoint σ).im| = δ := by
    rw [Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del, abs_neg, hσ]
  have h2 : |(Cvs.ZeroCounting.zPoint ρ).im| = |Cvs.GaussKernel.del ρ| := by
    rw [Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del, abs_neg]
  rcases hb with rfl | rfl
  · exact (abs_add_le _ _).trans (by rw [h1, h2])
  · exact (abs_sub _ _).trans (by rw [h1, h2])

/-- For `|γ'| ≥ 2|γ| + 1`, `a = γ ± γ'` has `a ≠ 0` and `4/a² ≤ 16/γ'²`. -/
theorem far_coef {γ γ' a : ℝ} (h : 2 * |γ| + 1 ≤ |γ'|) (ha : a = γ + γ' ∨ a = γ - γ') :
    a ≠ 0 ∧ 4 / a ^ 2 ≤ 16 * (1 / γ' ^ 2) := by
  have hla : |γ'| / 2 ≤ |a| := by
    rcases ha with rfl | rfl
    · have := abs_sub_abs_le_abs_sub γ' (-γ)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith [abs_nonneg γ]
    · have := abs_sub_abs_le_abs_sub γ' γ
      rw [abs_sub_comm] at this
      linarith [abs_nonneg γ]
  have hg : 0 < |γ'| := by linarith [abs_nonneg γ]
  have ha0 : 0 < |a| := by linarith
  refine ⟨abs_pos.1 ha0, ?_⟩
  have hsq : γ' ^ 2 / 4 ≤ a ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hla 2
    rw [div_pow, sq_abs, sq_abs] at this
    linarith
  have hg2 : 0 < γ' ^ 2 / 4 := by rw [← sq_abs]; positivity
  calc 4 / a ^ 2 ≤ 4 / (γ' ^ 2 / 4) := div_le_div_of_nonneg_left (by norm_num) hg2 hsq
    _ = 16 * (1 / γ' ^ 2) := by field_simp; ring

/-- **`U`-pairings of a top zero satisfy `OffTopBound`** with `R = 2|γ_σ| + 1`, `K = 16`. -/
theorem offTopBound_pairUe {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) :
    OffTopBound S δ (2 * |(σ : ℂ).im| + 1) 16
      (fun ρ L => pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2) where
  lt := hS.2.2.2
  K_nonneg := by norm_num
  nonneg := fun _ _ => sq_nonneg _
  near := fun ρ L hL => pairUe_sq_le fun a b _ hb =>
    (sinSinhC_sq_le_mul a b hL).trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (abs_im_pm_le (hS.2.2.1 σ hσ) hb) hL)) (sq_nonneg L))
  far := fun ρ L hL hR => pairUe_sq_le fun a b ha hb => by
    rw [Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_re] at ha
    obtain ⟨ha0, hc⟩ := far_coef hR ha
    exact (sinSinhC_sq_le_div ha0 b hL).trans (mul_le_mul hc
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (abs_im_pm_le (hS.2.2.1 σ hσ) hb) hL))
      (exp_pos _).le (by positivity))

/-! ### The norm of the pairing vector grows like `e^{δL}` -/

/-! ### The off-top sums divided by `‖b‖⁴` -/

/-! ### On the pairing vector at `x` -/

end Cvs.StepA.Edge.OffTopPairingBound

end
