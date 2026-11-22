import Mathlib
import Cvs.Finite.CentredCosineNyquist
import Cvs.Finite.EvenSectorZeroSide

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The slope of a moving pair of rank-one terms in the pair parameter `s = 4t²`

For `M(t) = B + 2a(ḡ + t)a(ḡ + t)ᵀ + 2a(ḡ − t)a(ḡ − t)ᵀ`, fixed `w` and `G = ⟪a, w⟫`, the form `⟪w, M(√s/2)w⟫` has
right derivative `G′(ḡ)² + G(ḡ)G″(ḡ)` at `s = 0`. Any `b ≤ ⟪w, M(√s/2)w⟫` with equality at `0`, such as the bottom of
the Rayleigh quotient in finite dimension, has `b(s) ≤ b(0) + (⟪w, Ṁw⟫ + ε)s` for small `s ≥ 0`. The rows
`(Φ_{f_m}(τ))_m` of `Cvs.Finite.CentredCosineNyquist`'s centred transform of continuous reflection-even profiles are smooth, so this applies.
-/

noncomputable section

open Real Filter Topology Asymptotics Set
open scoped ContDiff

namespace Cvs.Finite.MovingRankOnePairSlope
open Cvs.ZeroCounting

/-! ### The scalar law -/

section Scalar

variable {G G' : ℝ → ℝ} {g G2 : ℝ}

/-- The pair sum `H(t) = G(ḡ + t)² + G(ḡ − t)²`. -/
def H (G : ℝ → ℝ) (g t : ℝ) : ℝ := G (g + t) ^ 2 + G (g - t) ^ 2

/-- Its derivative `H′(t) = 2G(ḡ + t)G′(ḡ + t) − 2G(ḡ − t)G′(ḡ − t)`. -/
def H' (G G' : ℝ → ℝ) (g t : ℝ) : ℝ := 2 * G (g + t) * G' (g + t) - 2 * G (g - t) * G' (g - t)

/-- `H′` is the derivative of `H` at every `t` where `G` is differentiable at `ḡ ± t`. -/
theorem hasDerivAt_H {t : ℝ} (h1 : HasDerivAt G (G' (g + t)) (g + t))
    (h2 : HasDerivAt G (G' (g - t)) (g - t)) : HasDerivAt (H G g) (H' G G' g t) t := by
  have h1' : HasDerivAt (fun t => G (g + t)) (G' (g + t)) t := h1.comp_const_add g t
  have h2' : HasDerivAt (fun t => G (g - t)) (-G' (g - t)) t := h2.comp_const_sub g t
  have := (h1'.pow 2).add (h2'.pow 2)
  refine this.congr_deriv ?_
  unfold H'
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- If `G` is differentiable near `ḡ`, then `H′` is the derivative of `H` near `t = 0`. -/
theorem eventually_hasDerivAt_H (hG : ∀ᶠ τ in 𝓝 g, HasDerivAt G (G' τ) τ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (H G g) (H' G G' g t) t := by
  have hp : Tendsto (fun t : ℝ => g + t) (𝓝 0) (𝓝 g) :=
    (continuous_const.add continuous_id).tendsto' 0 g (by simp)
  have hm : Tendsto (fun t : ℝ => g - t) (𝓝 0) (𝓝 g) :=
    (continuous_const.sub continuous_id).tendsto' 0 g (by simp)
  filter_upwards [hp.eventually hG, hm.eventually hG] with t h1 h2
  exact hasDerivAt_H h1 h2

/-- **The second derivative of the pair sum at `0`**: `H″(0) = 4(G′(ḡ)² + G(ḡ)G″(ḡ))`. -/
theorem hasDerivAt_H' (hG : HasDerivAt G (G' g) g) (hG' : HasDerivAt G' G2 g) :
    HasDerivAt (H' G G' g) (4 * (G' g ^ 2 + G g * G2)) 0 := by
  have h1 : HasDerivAt (fun t => G (g + t)) (G' g) 0 := by
    have := (show HasDerivAt G (G' g) (g + 0) by simpa using hG).comp_const_add g 0; simpa using this
  have h2 : HasDerivAt (fun t => G (g - t)) (-G' g) 0 := by
    have := (show HasDerivAt G (G' g) (g - 0) by simpa using hG).comp_const_sub g 0; simpa using this
  have h1' : HasDerivAt (fun t => G' (g + t)) G2 0 := by
    have := (show HasDerivAt G' G2 (g + 0) by simpa using hG').comp_const_add g 0; simpa using this
  have h2' : HasDerivAt (fun t => G' (g - t)) (-G2) 0 := by
    have := (show HasDerivAt G' G2 (g - 0) by simpa using hG').comp_const_sub g 0; simpa using this
  have := (((h1.const_mul 2).mul h1').sub ((h2.const_mul 2).mul h2'))
  unfold H'
  refine this.congr_deriv ?_
  simp only [add_zero, sub_zero]
  ring

/-- `H′(0) = 0`. -/
theorem H'_zero (G G' : ℝ → ℝ) (g : ℝ) : H' G G' g 0 = 0 := by
  simp [H']

/-- **Second-order expansion of the pair sum**: `H(t) − H(0) − 2At² = o(t²)`, `A = G′(ḡ)² + G(ḡ)G″(ḡ)`. -/
theorem H_expansion (hG : ∀ᶠ τ in 𝓝 g, HasDerivAt G (G' τ) τ) (hG' : HasDerivAt G' G2 g) :
    (fun t => (H G g t - 2 * (G' g ^ 2 + G g * G2) * t ^ 2)
        - (H G g 0 - 2 * (G' g ^ 2 + G g * G2) * 0 ^ 2)) =o[𝓝 0] fun t => (t - 0) ^ (1 + 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_hasDerivAt_H hG)
  have hopen : 𝓝[Metric.ball (0 : ℝ) ε] 0 = 𝓝 0 :=
    Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hε)
  have hφ : ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivWithinAt
      (fun t => H G g t - 2 * (G' g ^ 2 + G g * G2) * t ^ 2)
      (H' G G' g t - 4 * (G' g ^ 2 + G g * G2) * t) (Metric.ball (0 : ℝ) ε) t := by
    intro t ht
    have := (hball (Metric.mem_ball.mp ht)).sub
      ((hasDerivAt_pow 2 t).const_mul (2 * (G' g ^ 2 + G g * G2)))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  have hφ' : (fun t => H' G G' g t - 4 * (G' g ^ 2 + G g * G2) * t) =o[𝓝[Metric.ball (0 : ℝ) ε] 0]
      fun t => (t - 0) ^ 1 := by
    rw [hopen]
    have := hasDerivAt_iff_isLittleO.mp (hasDerivAt_H' (G := G) hG.self_of_nhds hG')
    simp only [H'_zero, sub_zero, smul_eq_mul, pow_one] at this ⊢
    refine this.congr_left fun t => ?_
    ring
  have := Convex.isLittleO_pow_succ_real (convex_ball 0 ε) (Metric.mem_ball_self hε) hφ hφ'
  rwa [hopen] at this

/-- **The pair slope (scalar form)**: `s ↦ c₀ + 2G(ḡ + √s/2)² + 2G(ḡ − √s/2)²` has right derivative
`G′(ḡ)² + G(ḡ)G″(ḡ)` at `s = 0`. -/
theorem pair_slope (hG : ∀ᶠ τ in 𝓝 g, HasDerivAt G (G' τ) τ) (hG' : HasDerivAt G' G2 g) (c₀ : ℝ) :
    HasDerivWithinAt (fun s => c₀ + 2 * G (g + √s / 2) ^ 2 + 2 * G (g - √s / 2) ^ 2)
      (G' g ^ 2 + G g * G2) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_isLittleO]
  have hk : Tendsto (fun s : ℝ => √s / 2) (𝓝[Ici 0] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => √s / 2) (𝓝 0) (𝓝 (√0 / 2)) :=
      ((continuous_sqrt.div_const 2).tendsto 0)
    rw [sqrt_zero, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hφ := (H_expansion (G := G) hG hG').comp_tendsto hk
  have hsq : ∀ s ∈ Ici (0 : ℝ), (√s / 2 - 0) ^ (1 + 1) = s / 4 := by
    intro s hs
    rw [sub_zero, div_pow, sq_sqrt (mem_Ici.mp hs)]; norm_num
  have hbig : (fun s : ℝ => (√s / 2 - 0) ^ (1 + 1)) =O[𝓝[Ici 0] 0] fun s => s - 0 := by
    refine IsBigO.of_bound (1 / 4) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hsq s hs, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    norm_num
    ring_nf; rfl
  have h2 := (hφ.trans_isBigO hbig).const_mul_left 2
  refine h2.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (0 : ℝ) ≤ s := mem_Ici.mp hs
  simp only [Function.comp, H, sqrt_zero, zero_div, add_zero, sub_zero, smul_eq_mul]
  have : (√s / 2) ^ 2 = s / 4 := by rw [div_pow, sq_sqrt hs']; norm_num
  rw [this]
  ring

end Scalar

/-! ### The operator form -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The moving pair `M(t)w = Bw + 2⟪a(ḡ + t), w⟫a(ḡ + t) + 2⟪a(ḡ − t), w⟫a(ḡ − t)`. -/
def pairOp (B : E →ₗ[ℝ] E) (a : ℝ → E) (g t : ℝ) (w : E) : E :=
  B w + (2 * ⟪a (g + t), w⟫) • a (g + t) + (2 * ⟪a (g - t), w⟫) • a (g - t)

/-- The `s`-derivative of the pair, `Ṁw = ½(⟪a, w⟫a″ + 2⟪a′, w⟫a′ + ⟪a″, w⟫a)`. -/
def pairDot (a1 a2 a3 : E) (w : E) : E :=
  (1 / 2 : ℝ) • (⟪a1, w⟫ • a3 + (2 * ⟪a2, w⟫) • a2 + ⟪a3, w⟫ • a1)

/-- The quadratic form of the moving pair. -/
theorem inner_pairOp (B : E →ₗ[ℝ] E) (a : ℝ → E) (g t : ℝ) (w : E) :
    ⟪w, pairOp B a g t w⟫
      = ⟪w, B w⟫ + 2 * ⟪a (g + t), w⟫ ^ 2 + 2 * ⟪a (g - t), w⟫ ^ 2 := by
  unfold pairOp
  simp only [inner_add_right, inner_smul_right, real_inner_comm w]
  ring

/-- The quadratic form of `Ṁ` is `⟪a′, w⟫² + ⟪a, w⟫⟪a″, w⟫`. -/
theorem inner_pairDot (a1 a2 a3 w : E) :
    ⟪w, pairDot a1 a2 a3 w⟫ = ⟪a2, w⟫ ^ 2 + ⟪a1, w⟫ * ⟪a3, w⟫ := by
  unfold pairDot
  simp only [inner_add_right, inner_smul_right, real_inner_comm w]
  ring

/-- **The pair slope along a fixed vector**: for `a` differentiable near `ḡ` with derivative `a′`, and `a′`
differentiable at `ḡ` with derivative `a″`, `s ↦ ⟪w, M(√s/2)w⟫` has right derivative
`⟪w, Ṁw⟫ = G′(ḡ)² + G(ḡ)G″(ḡ)` at `0`. -/
theorem pair_slope_op (B : E →ₗ[ℝ] E) {a a' : ℝ → E} {g : ℝ} {a'' : E}
    (ha : ∀ᶠ τ in 𝓝 g, HasDerivAt a (a' τ) τ) (ha' : HasDerivAt a' a'' g) (w : E) :
    HasDerivWithinAt (fun s => ⟪w, pairOp B a g (√s / 2) w⟫)
      ⟪w, pairDot (a g) (a' g) a'' w⟫ (Ici 0) 0 := by
  have hG : ∀ᶠ τ in 𝓝 g, HasDerivAt (fun τ => ⟪a τ, w⟫) ⟪a' τ, w⟫ τ :=
    ha.mono fun τ h => by simpa using h.inner ℝ (hasDerivAt_const τ w)
  have hG' : HasDerivAt (fun τ => ⟪a' τ, w⟫) ⟪a'', w⟫ g := by
    simpa using ha'.inner ℝ (hasDerivAt_const g w)
  have := pair_slope hG hG' ⟪w, B w⟫
  rw [inner_pairDot]
  simp_rw [inner_pairOp]
  exact this

/-- **The second `t`-derivative**: near `t = 0`, `t ↦ ⟪w, M(t)w⟫` has derivative `2H′(t)`, which is `0` at
`t = 0` and has derivative `8(G′(ḡ)² + G(ḡ)G″(ḡ))` there. -/
theorem pair_second_deriv (B : E →ₗ[ℝ] E) {a a' : ℝ → E} {g : ℝ} {a'' : E}
    (ha : ∀ᶠ τ in 𝓝 g, HasDerivAt a (a' τ) τ) (ha' : HasDerivAt a' a'' g) (w : E) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => ⟪w, pairOp B a g t w⟫)
        (2 * H' (fun τ => ⟪a τ, w⟫) (fun τ => ⟪a' τ, w⟫) g t) t)
      ∧ H' (fun τ => ⟪a τ, w⟫) (fun τ => ⟪a' τ, w⟫) g 0 = 0
      ∧ HasDerivAt (fun t => 2 * H' (fun τ => ⟪a τ, w⟫) (fun τ => ⟪a' τ, w⟫) g t)
          (8 * (⟪a' g, w⟫ ^ 2 + ⟪a g, w⟫ * ⟪a'', w⟫)) 0 := by
  have hG : ∀ᶠ τ in 𝓝 g, HasDerivAt (fun τ => ⟪a τ, w⟫) ⟪a' τ, w⟫ τ :=
    ha.mono fun τ h => by simpa using h.inner ℝ (hasDerivAt_const τ w)
  have hG' : HasDerivAt (fun τ => ⟪a' τ, w⟫) ⟪a'', w⟫ g := by
    simpa using ha'.inner ℝ (hasDerivAt_const g w)
  have hfun : (fun t => ⟪w, pairOp B a g t w⟫) = fun t => ⟪w, B w⟫ + 2 * H (fun τ => ⟪a τ, w⟫) g t := by
    funext t; rw [inner_pairOp]; unfold H; ring
  refine ⟨?_, H'_zero _ _ _, ?_⟩
  · filter_upwards [eventually_hasDerivAt_H hG] with t ht
    rw [hfun]
    exact (ht.const_mul 2).const_add ⟪w, B w⟫
  · have := (hasDerivAt_H' (g := g) hG.self_of_nhds hG').const_mul 2
    refine this.congr_deriv ?_
    ring

/-- **The slope bounds any lower envelope touching at `s = 0`**: if `b(s) ≤ ⟪w, M(√s/2)w⟫` for `s ≥ 0` with
equality at `s = 0`, then for every `ε > 0`, eventually as `s → 0⁺`, `b(s) ≤ b(0) + (⟪w, Ṁw⟫ + ε)s`. -/
theorem envelope_slope_le (B : E →ₗ[ℝ] E) {a a' : ℝ → E} {g : ℝ} {a'' : E}
    (ha : ∀ᶠ τ in 𝓝 g, HasDerivAt a (a' τ) τ) (ha' : HasDerivAt a' a'' g) (w : E) {b : ℝ → ℝ}
    (hb : ∀ s, 0 ≤ s → b s ≤ ⟪w, pairOp B a g (√s / 2) w⟫) (hb0 : b 0 = ⟪w, pairOp B a g 0 w⟫)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[Ici 0] 0, b s ≤ b 0 + (⟪w, pairDot (a g) (a' g) a'' w⟫ + ε) * s := by
  have h := pair_slope_op B ha ha' w
  rw [hasDerivWithinAt_iff_isLittleO] at h
  filter_upwards [h.def hε, self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0 : ℝ) ≤ s := hs0
  simp only [sqrt_zero, zero_div, smul_eq_mul, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs0'] at hs
  have h1 := (abs_le.mp hs).2
  have h2 := hb s hs0'
  rw [hb0]
  nlinarith

/-- The bottom of the Rayleigh quotient of `M(t)`, `λ(t) = ⨅_{u ≠ 0} ⟪u, M(t)u⟫/⟪u, u⟫`. -/
def lamMin (B : E →ₗ[ℝ] E) (a : ℝ → E) (g t : ℝ) : ℝ :=
  ⨅ u : {u : E // u ≠ 0}, ⟪(u : E), pairOp B a g t u⟫ / ⟪(u : E), u⟫

/-- In finite dimension `λ(t)` lies below every Rayleigh quotient of `M(t)`. -/
theorem lamMin_le [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E) (a : ℝ → E) (g t : ℝ) {u : E} (hu : u ≠ 0) :
    lamMin B a g t ≤ ⟪u, pairOp B a g t u⟫ / ⟪u, u⟫ := by
  have hbdd : BddBelow (Set.range fun v : {v : E // v ≠ 0} =>
      ⟪(v : E), pairOp B a g t v⟫ / ⟪(v : E), v⟫) := by
    refine ⟨-‖LinearMap.toContinuousLinearMap B‖, ?_⟩
    rintro _ ⟨v, rfl⟩
    have hv : 0 < ⟪(v : E), v⟫ := real_inner_self_pos.mpr v.2
    dsimp only
    rw [le_div_iff₀ hv, inner_pairOp]
    have h1 : |⟪(v : E), B v⟫| ≤ ‖LinearMap.toContinuousLinearMap B‖ * ⟪(v : E), v⟫ := by
      calc |⟪(v : E), B v⟫| ≤ ‖(v : E)‖ * ‖B v‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖(v : E)‖ * (‖LinearMap.toContinuousLinearMap B‖ * ‖(v : E)‖) := by
            gcongr
            exact (LinearMap.toContinuousLinearMap B).le_opNorm (v : E)
        _ = ‖LinearMap.toContinuousLinearMap B‖ * ⟪(v : E), v⟫ := by
            rw [real_inner_self_eq_norm_sq]; ring
    nlinarith [abs_le.mp h1, sq_nonneg ⟪a (g + t), (v : E)⟫, sq_nonneg ⟪a (g - t), (v : E)⟫]
  exact ciInf_le hbdd ⟨u, hu⟩

/-- **The one-sided slope of the bottom of the spectrum**: in finite dimension, for a unit `w` attaining
`λ(0)`, `λ(√s/2) ≤ λ(0) + (⟪w, Ṁw⟫ + ε)s` eventually as `s → 0⁺`, for every `ε > 0`. -/
theorem lamMin_slope_le [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E) {a a' : ℝ → E} {g : ℝ} {a'' : E}
    (ha : ∀ᶠ τ in 𝓝 g, HasDerivAt a (a' τ) τ) (ha' : HasDerivAt a' a'' g) {w : E} (hw : ⟪w, w⟫ = 1)
    (hw0 : ⟪w, pairOp B a g 0 w⟫ = lamMin B a g 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[Ici 0] 0,
      lamMin B a g (√s / 2) ≤ lamMin B a g 0 + (⟪w, pairDot (a g) (a' g) a'' w⟫ + ε) * s := by
  have hw' : w ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hw; exact zero_ne_one hw
  have h := envelope_slope_le B ha ha' w (b := fun s => lamMin B a g (√s / 2))
    (fun s _ => by have := lamMin_le B a g (√s / 2) hw'; rwa [hw, div_one] at this)
    (by simp only [sqrt_zero, zero_div]; exact hw0.symm) hε
  simpa only [sqrt_zero, zero_div] using h

/-- The hypotheses are met by the quadratic path `a(τ) = τ²v`, whose slope is `⟪w, Ṁw⟫` at `a = ḡ²v`,
`a′ = 2ḡv`, `a″ = 2v`. -/
theorem witness (B : E →ₗ[ℝ] E) (v w : E) (g : ℝ) :
    HasDerivWithinAt (fun s => ⟪w, pairOp B (fun τ => τ ^ 2 • v) g (√s / 2) w⟫)
      ⟪w, pairDot (g ^ 2 • v) ((2 * g) • v) ((2 : ℝ) • v) w⟫ (Ici 0) 0 := by
  have ha : ∀ τ : ℝ, HasDerivAt (fun τ => τ ^ 2 • v) ((2 * τ) • v) τ := by
    intro τ
    refine ((hasDerivAt_pow 2 τ).smul_const v).congr_deriv ?_
    congr 1; simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have ha' : HasDerivAt (fun τ : ℝ => (2 * τ) • v) ((2 : ℝ) • v) g := by
    refine (((hasDerivAt_id g).const_mul 2).smul_const v).congr_deriv ?_
    simp
  exact pair_slope_op B (Eventually.of_forall ha) ha' w

end Operator

/-! ### The zero-side rows of the window modes -/

/-- The rows `a(τ) = (Φ_{f_m}(τ))_m` of `Cvs.Finite.CentredCosineNyquist`'s centred transform of a finite family of profiles. -/
def rows (L : ℝ) {n : ℕ} (f : Fin n → ℝ → ℝ) (τ : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun m => Cvs.Finite.CentredCosineNyquist.Phi L (f m) τ

/-- The rows of continuous reflection-even profiles are smooth. -/
theorem contDiff_rows {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ m s, f m (L - s) = f m s) (hc : ∀ m, Continuous (f m)) {k : WithTop ℕ∞} :
    ContDiff ℝ k (rows L f) :=
  contDiff_euclidean.mpr fun m => by
    simpa [rows] using Cvs.Finite.CentredCosineNyquist.contDiff_Phi hL (hf m) (hc m)

/-- **The pair slope on the zero-side rows**: for continuous reflection-even profiles `f_m`, any `B`, `ḡ` and `w`,
`s ↦ ⟪w, M(√s/2)w⟫` with `a = rows L f` has right derivative `⟪w, Ṁw⟫` at `0`, with `a′`, `a″` the first two
derivatives of the rows at `ḡ`. -/
theorem rows_pair_slope {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {f : Fin n → ℝ → ℝ}
    (hf : ∀ m s, f m (L - s) = f m s) (hc : ∀ m, Continuous (f m))
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (g : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    HasDerivWithinAt (fun s => @inner ℝ _ _ w (pairOp B (rows L f) g (√s / 2) w))
      (@inner ℝ _ _ w (pairDot (rows L f g) (deriv (rows L f) g) (deriv (deriv (rows L f)) g) w))
      (Ici 0) 0 := by
  have hcd : ContDiff ℝ ∞ (rows L f) := contDiff_rows hL hf hc
  have hd := contDiff_infty_iff_deriv.mp hcd
  have hd2 := contDiff_infty_iff_deriv.mp hd.2
  exact pair_slope_op B (Eventually.of_forall fun τ => (hd.1 τ).hasDerivAt) (hd2.1 g).hasDerivAt w

/-- The cosine window modes `cos(ω_m s)` are reflection-even on `[0, L]`. -/
theorem cosMode_reflect (L : ℝ) (m : ℤ) (s : ℝ) :
    Real.cos (Cvs.Finite.CentredCosineNyquist.om L m * (L - s)) = Real.cos (Cvs.Finite.CentredCosineNyquist.om L m * s) := by
  have h := Cvs.Finite.CentredCosineNyquist.cosPoly_reflect L (fun _ : Unit => m) (fun _ => 1) s
  simpa [Cvs.Finite.CentredCosineNyquist.cosPoly_eq] using h

/-- `rows_pair_slope` on the unit cosine modes `e_m = √(2/L)cos(ω_m s)`, `m < n`. -/
theorem cosRows_pair_slope {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (g : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    HasDerivWithinAt
      (fun s => @inner ℝ _ _ w (pairOp B (rows L fun m s =>
        √(2 / L) * Real.cos (Cvs.Finite.CentredCosineNyquist.om L (m : ℕ) * s)) g (√s / 2) w))
      (@inner ℝ _ _ w (pairDot (rows L (fun m s => √(2 / L) * Real.cos (Cvs.Finite.CentredCosineNyquist.om L (m : ℕ) * s)) g)
        (deriv (rows L fun m s => √(2 / L) * Real.cos (Cvs.Finite.CentredCosineNyquist.om L (m : ℕ) * s)) g)
        (deriv (deriv (rows L fun m s => √(2 / L) * Real.cos (Cvs.Finite.CentredCosineNyquist.om L (m : ℕ) * s))) g) w))
      (Ici 0) 0 :=
  rows_pair_slope hL (fun m s => by simp only [cosMode_reflect]) (fun m => by fun_prop) B g w

end Cvs.Finite.MovingRankOnePairSlope
