import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaZeroWindows

/-!
# The bucket as a difference of windows, and the main term's increment

Two pieces `Cvs.Zeta.ZeroCounting.BucketStepTightened`'s `hbucket` needs.  The bucket is exactly `W(n) \ W(n−1)`, so its
cardinality is a difference of counts with no zero-avoiding height involved; and the
Riemann–von Mangoldt main term increases by at most `(b−a)·log(b/2π)` across `[a,b]`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.ZeroBucketIncrement

/-- **The bucket is the top slice of a window.**  `⌈|γ|⌉ = n` says exactly `n−1 < |γ| ≤ n`,
so bucket `n` is what `W(n)` has and `W(n−1)` does not. -/
theorem card_bucketFinset_add {n : ℕ} (hn : 1 ≤ n) :
    nontrivialZetaZeroCount ((n - 1 : ℕ) : ℝ) + (completedZetaZeroBucketFinset n).card
      = nontrivialZetaZeroCount (n : ℝ) := by
  classical
  rw [← card_completedZetaZeroIndexWindowFinset, ← card_completedZetaZeroIndexWindowFinset]
  have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hlow : completedZetaZeroIndexWindowFinset ((n - 1 : ℕ) : ℝ)
      = (completedZetaZeroIndexWindowFinset (n : ℝ)).filter
          (fun rho => |(nontrivialZetaZeroValue rho.1).im| ≤ ((n - 1 : ℕ) : ℝ)) := by
    ext rho
    rw [Finset.mem_filter, mem_completedZetaZeroIndexWindowFinset,
      mem_completedZetaZeroIndexWindowFinset]
    exact ⟨fun h => ⟨h.trans hle, h⟩, fun h => h.2⟩
  have hbuck : completedZetaZeroBucketFinset n
      = (completedZetaZeroIndexWindowFinset (n : ℝ)).filter
          (fun rho => ¬ (|(nontrivialZetaZeroValue rho.1).im| ≤ ((n - 1 : ℕ) : ℝ))) := by
    ext rho
    rw [mem_completedZetaZeroBucketFinset, Finset.mem_filter,
      mem_completedZetaZeroIndexWindowFinset, completedZetaZeroBucket,
      Nat.ceil_eq_iff (by omega)]
    exact ⟨fun h => ⟨h.2, not_le.mpr h.1⟩, fun h => ⟨not_le.mp h.2, h.1⟩⟩
  rw [hlow, hbuck]
  exact Finset.card_filter_add_card_filter_not _

end Cvs.Zeta.ZeroBucketIncrement
