import Mathlib
import CpnfLean.Sieve
import CpnfLean.Twin

/-!
# CPNF — the twin process

The twin process grows a blocker set of numbers above `3` and certifies twin indices whose
pair is admissible inside the certification window. Nothing here presupposes that the pair
is prime; an index is certified because the blockers leave it alone, not because it is.

The certification window follows the paper's consistent form: an index `n` may be
certified when `6n + 1 ≤ y²`, i.e. `n ≤ ⌊(y² - 1)/6⌋`, where `y` is the largest blocker.
-/

namespace CPNF

/-! ## Extending twin blockers -/

/-- Adding a blocker above `3` keeps the twin-blocker property. -/
theorem twinBlockers_insert {B : Finset ℕ} (c : ℕ) (hc : 3 < c) (h : TwinBlockers B) :
    TwinBlockers (insert c B) := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact hc
  · exact h p hp

/-- Dropping a blocker can only enlarge the twin sieve. -/
theorem twinSieve_subset_of_subset {B B' : Finset ℕ} (h : B ⊆ B') (y : ℕ) :
    twinSieve B' y ⊆ twinSieve B y := by
  rintro n ⟨⟨hlo, hhi⟩, hwin⟩
  -- Each member survives more blockers, so it survives `B`.
  refine ⟨⟨fun p hp => hlo p (h hp), fun p hp => hhi p (h hp)⟩, hwin⟩

end CPNF
