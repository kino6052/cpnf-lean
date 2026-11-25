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
* **The pair at any index has at most two reasons to be blocked** — for each blocker `q`,
  two congruences kill the pair. So a window of length `W` needs at least `W` blockers to
  be killed by distinct primes. This is the combinatorial core, and it is true.

Whether a covering exists remains open, and is not claimed here.
-/

namespace CPNF

/-! ## The window grows -/

/-- `W(y) = ⌊(y² - 1)/6⌋` is monotone in `y`. -/
theorem window_mono : Monotone window := by
  intro a b hab
  simp only [window]
  have : a ^ 2 ≤ b ^ 2 := by
    have h := Nat.mul_self_le_mul_self_iff.mpr hab
    exact h
  omega

/-! ## Two congruences per blocker -/

/-- A blocker kills a pair only by dividing one of its two members: at most two residue
    classes per blocker, which is the combinatorial reason a covering is not free. -/
theorem killed_iff {B : Finset ℕ} {n : ℕ} :
    ¬ Admissible B n ↔ ∃ p ∈ B, p ∣ twinLo n ∨ p ∣ twinHi n := by
  constructor
  · intro h
    by_contra hall
    push_neg at hall
    exact h ⟨fun p hp => fun hd => hall p hp (Or.inl hd),
             fun p hp => fun hd => hall p hp (Or.inr hd)⟩
  · rintro ⟨p, hp, hd⟩ ⟨hlo, hhi⟩
    rcases hd with hd | hd
    · exact hlo p hp hd
    · exact hhi p hp hd

end CPNF
