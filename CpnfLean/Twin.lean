import Mathlib
import CpnfLean.Sieve

/-!
# CPNF — twin indices

A twin index `n` stands for the pair `(6n - 1, 6n + 1)`. An index is admissible for a
blocker set when both numbers survive every blocker. Nothing here assumes that either
number is "prime": admissibility is survival, exactly as in the ordinary process.

Two repairs to the paper's definitions, both forced by Lean:

* the certification window bounds the index against `y²`, not against `y`: the paper's
  `6n + 1 ≤ y` combined with `n ≤ ⌊(y² - 1)/6⌋` is a typo, and only the square form is
  consistent with the window it defines;
* the pair is not `6n ± 1` reduced, but `6n - 1` in `ℕ`, i.e. `0` at `n = 0`. Facts that
  are true only for `n ≥ 1` say so.
-/

namespace CPNF

/-- The left member of the pair at twin index `n`. -/
def twinLo (n : ℕ) : ℕ := 6 * n - 1

/-- The right member of the pair at twin index `n`. -/
def twinHi (n : ℕ) : ℕ := 6 * n + 1

/-- An index is admissible for `B` when both members survive every blocker in `B`. -/
def Admissible (B : Finset ℕ) (n : ℕ) : Prop := Survives B (twinLo n) ∧ Survives B (twinHi n)

instance (B : Finset ℕ) (n : ℕ) : Decidable (Admissible B n) :=
  inferInstanceAs (Decidable (Survives B (twinLo n) ∧ Survives B (twinHi n)))

/-- The certification window `W(y) = ⌊(y² - 1) / 6⌋` for the largest blocker `y`. -/
def window (y : ℕ) : ℕ := (y ^ 2 - 1) / 6

/-- The twin sieve: indices that survive the blockers and lie inside the window. -/
def twinSieve (B : Finset ℕ) (y : ℕ) : Set ℕ := { n | Admissible B n ∧ n ≤ window y }

/-! ## Facts about the pair -/

/-- The second member is never divisible by two. -/
theorem not_two_dvd_twinHi (n : ℕ) : ¬ (2 : ℕ) ∣ twinHi n := by
  simp only [twinHi]
  omega

/-- For `n ≥ 1` the first member is `6m + 5`, and never divisible by two. -/
theorem not_two_dvd_twinLo {n : ℕ} (hn : 1 ≤ n) : ¬ (2 : ℕ) ∣ twinLo n := by
  -- Write `n = m + 1`, so the member is `6m + 5`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h : twinLo (m + 1) = 6 * m + 5 := by simp only [twinLo]; omega
  rw [h]
  omega

/-! ## The window -/

/-- The window really bounds the pair: `6n + 1 ≤ y²` for every eligible index. -/
theorem window_bound {n y : ℕ} (h : n ≤ window y) (hy : 0 < y ^ 2) : 6 * n + 1 ≤ y ^ 2 := by
  -- The window times six is at most `y² - 1`.
  have hw : window y * 6 ≤ y ^ 2 - 1 := by
    simp only [window]
    omega
  -- Hence `6n + 1 ≤ 6W + 1 ≤ y²`.
  have : 6 * n ≤ 6 * window y := by omega
  omega

/-- For a largest blocker `y ≥ 7` the window holds at least `y` indices, so the window is
    never shorter than the largest blocker itself. This is the honest direction of growth:
    the window rises quadratically, an index bound rises linearly. -/
theorem window_ge (y : ℕ) (hy : 7 ≤ y) : y ≤ window y := by
  -- Turn the claim into a multiplication: `y ≤ (y² - 1)/6` iff `y * 6 ≤ y² - 1`.
  rw [window, Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 6)]
  -- Enough to show `6y + 1 ≤ y²`, i.e. `y * (y - 6) ≥ 1`.
  rw [pow_two]
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 7 := ⟨y - 7, by omega⟩
  ring_nf
  omega

/-! ## Blockers that kill every index -/

/-- A pair has no divisibility by two in either member. -/
theorem two_nor {n : ℕ} (hn : 1 ≤ n) :
    ¬ (2 : ℕ) ∣ twinLo n ∧ ¬ (2 : ℕ) ∣ twinHi n :=
  ⟨not_two_dvd_twinLo hn, not_two_dvd_twinHi n⟩

/-- The twin process starts after `2` and `3`: its blockers are only numbers above `3`.
    This is the paper's `B ← {2, 3}` read correctly — `2` and `3` never block a pair
    (`6n ± 1` is coprime to `6`), so they are dropped rather than carried as blockers. -/
def TwinBlockers (B : Finset ℕ) : Prop := ∀ p ∈ B, 3 < p

end CPNF
