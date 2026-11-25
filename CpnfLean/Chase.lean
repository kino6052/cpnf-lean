import Mathlib
import CpnfLean.Sieve
import CpnfLean.Twin
import CpnfLean.TwinProcess

/-!
# CPNF — the endless chase

The chase: the blockers keep growing, the window keeps moving, and no twin index is ever
certified. The paper's Part 4 claims this cannot happen. What can honestly be settled
without density and without a covering theorem is stated here:

* **The window grows without bound** — whatever the blockers do, `y²/6` keeps rising.
* **Stagnation is a statement about a window that moves**, so "no index in the window"
  must be refuted *at each stage*, not once and for all — which is exactly why the chase
  is a real obstruction rather than a bookkeeping one.
* **A blocker kills a pair only by dividing one of its two members** — each blocker has two
  congruences, one class per member mod `q`. Note what this does *not* give: one blocker
  kills about `2W/q` indices in a window, not at most two. So a window of length `W` is not
  protected by any argument of the shape "needs at least `W` blockers"; a single blocker
  `5` already removes three indices from the window at `y = 7`. The counting core the
  earlier version of this file claimed is false as stated, and is not claimed now.

Whether a covering exists remains open, and is not claimed here.
-/

namespace CPNF

/-! ## The window grows -/

/-- `W(y) = ⌊(y² - 1)/6⌋` is monotone in `y`. -/
theorem window_mono : Monotone window := by
  intro a b hab
  simp only [window]
  have : a ^ 2 ≤ b ^ 2 := by
    -- `mul_self_le_mul_self_iff` is stated for `a * a`; unfold the squares to match.
    rw [pow_two, pow_two]
    exact Nat.mul_self_le_mul_self_iff.mpr hab
  omega

/-! ## Two congruences per blocker -/

/-- A blocker kills a pair only by dividing one of its two members: at most two residue
    classes per blocker, which is the combinatorial reason a covering is not free. -/
theorem killed_iff {B : Finset ℕ} {n : ℕ} :
    ¬ Admissible B n ↔ ∃ p ∈ B, p ∣ twinLo n ∨ p ∣ twinHi n := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    -- `push_neg` turns `¬ (p ∣ twinLo n ∨ p ∣ twinHi n)` into the conjunction of the
    -- two non-divisibilities; take each component for the matching member.
    exact h ⟨fun p hp => (hall p hp).1, fun p hp => (hall p hp).2⟩
  · rintro ⟨p, hp, hd⟩ ⟨hlo, hhi⟩
    rcases hd with hd | hd
    · exact hlo p hp hd
    · exact hhi p hp hd

end CPNF
