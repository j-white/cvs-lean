import Mathlib
import Cvs.StepA.Edge.PlanarBoxLemma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# First contact for a flow with `Φ 0 = id` on the compactum

The abstract first-contact theorem on a compact flow-invariant set `K` on which `Φ 0` is the
identity, from the planar box lemma `box_neg`.
-/

open Set Filter Topology

namespace Cvs.StepA.Edge.PlanarBoxLemma
variable {X : Type*} [TopologicalSpace X]

/-- **First contact**: if `Φ 0` fixes `K`, `s > 0` somewhere on `K` at all large levels, every zero
of `s` with locally nonpositive orbit row lies in `BS`, and each point of `BS` has a negative upper
half-disc and a positive point below, then `s > 0` somewhere on `K` at every level. -/
theorem exists_pos_of_firstContact (Φ : ℝ → X → X)
    (hΦ : Continuous fun p : ℝ × X => Φ p.1 p.2) (hadd : ∀ a b φ, Φ (a + b) φ = Φ a (Φ b φ))
    (s : X → ℝ → ℝ) (hs : Continuous fun p : X × ℝ => s p.1 p.2)
    {K : Set X} (hK : IsCompact K) (hKinv : ∀ x, ∀ φ ∈ K, Φ x φ ∈ K)
    (hΦ0 : ∀ φ ∈ K, Φ 0 φ = φ)
    (BS : X → ℝ → Prop)
    (hseed : ∃ Y₀, ∀ y ≥ Y₀, ∃ φ ∈ K, 0 < s φ y)
    (hC : ∀ φ y, s φ y = 0 → (∃ ε > 0, ∀ x, |x| < ε → s (Φ x φ) y ≤ 0) → BS φ y)
    (hWA : ∀ φ y, BS φ y → ∃ r > 0, ∀ x y', 0 ≤ y' → 0 < x ^ 2 + y' ^ 2 → x ^ 2 + y' ^ 2 < r ^ 2 →
      s (Φ x φ) (y + y') < 0)
    (hWB : ∀ φ y, BS φ y → ∃ lam > 0, ∃ η₀ > 0, ∀ η ∈ Ioo 0 η₀,
      0 < s (Φ (-(lam * η)) φ) (y - η))
    (y : ℝ) : ∃ φ ∈ K, 0 < s φ y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨Y₀, hY₀⟩ := hseed
  -- the levels at or above `y` where `s ≤ 0` on all of `K`
  set Bad : Set ℝ := {t | y ≤ t ∧ ∀ φ ∈ K, s φ t ≤ 0} with hBad
  have hBadcl : IsClosed Bad := by
    have : Bad = Ici y ∩ ⋂ φ ∈ K, {t | s φ t ≤ 0} := by
      ext t; simp [hBad]
    rw [this]
    exact isClosed_Ici.inter (isClosed_biInter fun φ _ =>
      isClosed_le (hs.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
  have hBadbdd : BddAbove Bad := by
    refine ⟨Y₀, fun t ht => le_of_not_gt fun hlt => ?_⟩
    obtain ⟨φ, hφ, hpos⟩ := hY₀ t hlt.le
    exact absurd (ht.2 φ hφ) (not_le.2 hpos)
  have hBadne : Bad.Nonempty := ⟨y, le_rfl, hcon⟩
  set ys := sSup Bad
  have hysBad : ys ∈ Bad := hBadcl.csSup_mem hBadne hBadbdd
  -- above the last bad level, `s` is positive somewhere on `K`
  have hgood : ∀ t, ys < t → ∃ φ ∈ K, 0 < s φ t := by
    intro t ht
    by_contra h
    push Not at h
    exact absurd (le_csSup hBadbdd ⟨hysBad.1.trans ht.le, h⟩) (not_le.2 ht)
  -- Lemma B: near each point of `K`, `s < 0` on `K` just above the level `ys`
  have hloc : ∀ φs ∈ K, ∀ᶠ q : ℝ × X in 𝓝 (ys, φs), ys < q.1 → q.2 ∈ K → s q.2 q.1 < 0 := by
    intro φs hφs
    rcases (hysBad.2 φs hφs).lt_or_eq with hneg | hzero
    · have hg : Continuous fun q : ℝ × X => s q.2 q.1 := hs.comp continuous_swap
      filter_upwards [(hg.tendsto (ys, φs)).eventually_lt_const hneg] with q hq _ _ using hq
    obtain ⟨r, hr, hdisc⟩ := hWA φs ys (hC φs ys hzero
      ⟨1, one_pos, fun x _ => hysBad.2 _ (hKinv x φs hφs)⟩)
    set ρ := r / 2 with hρ
    have hρpos : 0 < ρ := by positivity
    have hside0 : ∀ σ : ℝ, σ ^ 2 = ρ ^ 2 → s (Φ σ φs) ys < 0 := by
      intro σ hσ2
      have := hdisc σ 0 le_rfl (by rw [hσ2]; positivity) (by rw [hσ2, hρ]; nlinarith)
      simpa using this
    have hsc : ∀ σ : ℝ, Continuous fun q : ℝ × X => s (Φ σ q.2) q.1 := fun σ =>
      hs.comp (Continuous.prodMk (hΦ.comp (Continuous.prodMk continuous_const continuous_snd))
        continuous_fst)
    have hev : ∀ᶠ q : ℝ × X in 𝓝 ys ×ˢ 𝓝 φs, s (Φ ρ q.2) q.1 < 0 ∧ s (Φ (-ρ) q.2) q.1 < 0 := by
      rw [← nhds_prod_eq]
      exact (((hsc ρ).tendsto (ys, φs)).eventually_lt_const (hside0 ρ rfl)).and
        (((hsc (-ρ)).tendsto (ys, φs)).eventually_lt_const (hside0 (-ρ) (neg_sq ρ)))
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 hev
    obtain ⟨δ, hδ, hδpa⟩ := Metric.eventually_nhds_iff.1 hpa
    rw [nhds_prod_eq]
    filter_upwards [Filter.Eventually.prod_mk
      (show ∀ᶠ t in 𝓝 ys, t ∈ Metric.ball ys δ from Metric.ball_mem_nhds ys hδ) hpb]
      with ⟨t, φ⟩ ⟨ht, hφb⟩ hyt hφK
    simp only [Metric.mem_ball] at ht hyt hφK ⊢
    have hbox := box_neg (f := fun p : ℝ × ℝ => s (Φ p.1 φ) p.2) (ρ := ρ) (a := ys) (b := t)
      (hs.comp (Continuous.prodMk (hΦ.comp (Continuous.prodMk continuous_fst continuous_const))
        continuous_snd))
      (fun y' hy' => by
        have hy'δ : dist y' ys < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hy'.1)]
          rw [Real.dist_eq, abs_of_pos (sub_pos.2 hyt)] at ht
          linarith [hy'.2]
        have := hab (hδpa hy'δ) hφb
        exact ⟨this.2, this.1⟩)
      (fun x _ => hysBad.2 _ (hKinv x φ hφK))
      (fun z _ hz => by
        obtain ⟨r', hr', hdisc'⟩ := hWA (Φ z φ) ys (hC _ ys hz
          ⟨1, one_pos, fun x _ => hysBad.2 _ (hKinv x _ (hKinv z φ hφK))⟩)
        refine ⟨r', hr', fun x y'' hy'' h0 h1 => ?_⟩
        have := hdisc' (x - z) (y'' - ys) (sub_nonneg.2 hy'') h0 h1
        rwa [← hadd, sub_add_cancel, add_sub_cancel] at this)
      (fun x₀ _ y₀ _ hz ⟨ε, hε, hrow⟩ => by
        obtain ⟨lam, hlam, η₀, hη₀, hpos⟩ := hWB (Φ x₀ φ) y₀ (hC _ y₀ hz
          ⟨ε, hε, fun x hx => by
            rw [← hadd]
            exact hrow (x + x₀) (by rwa [add_sub_cancel_right])⟩)
        refine ⟨lam, hlam, η₀, hη₀, fun η hη => ?_⟩
        have := hpos η hη
        rwa [← hadd, neg_add_eq_sub] at this)
      0 ⟨by linarith, hρpos.le⟩ t ⟨hyt, le_rfl⟩
    simpa [hΦ0 φ hφK] using hbox
  have hall := hK.eventually_forall_of_forall_eventually
    (P := fun t φ => ys < t → φ ∈ K → s φ t < 0) hloc
  obtain ⟨t, ht, hyt⟩ :=
    ((hall.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists (f := 𝓝[>] ys)
  obtain ⟨φ, hφK, hpos⟩ := hgood t hyt
  exact absurd (ht φ hφK hyt hφK) (not_lt.2 hpos.le)

end Cvs.StepA.Edge.PlanarBoxLemma
