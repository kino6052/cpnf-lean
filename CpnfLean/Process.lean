import Mathlib
import CpnfLean.Sieve

/-!
# CPNF — the certification process

At each stage the process certifies the least survivor and adds it to the blockers.
`stage k` is the blocker set after `k` stages; `certify k` is the number stage `k` certifies.
Nothing here assumes what a prime is: only survival and minimality.

The paper works with sets; we keep blockers in a `Finset`, because every stage only ever
*certifies one more number* and a finite blocker set is exactly what decides survival.
-/

namespace CPNF

/-! ## Existence of a survivor -/

/-- Every blocker set made of numbers `≥ 2` has a survivor: take `(max + 1)! + 1`.
    It is `≥ 2`, and no blocker divides it, since every blocker divides `(max + 1)!`. -/
theorem sieve_nonempty {B : Finset ℕ} (h2 : ∀ p ∈ B, 2 ≤ p) : (sieve B).Nonempty := by
  -- The candidate: one more than the factorial of the largest blocker plus one.
  refine ⟨(B.sup id + 1).factorial + 1, ?_, ?_⟩
  -- It is `≥ 2`, because the factorial is positive.
  · have hpos : 0 < (B.sup id + 1).factorial := Nat.factorial_pos _
    omega
  -- No blocker divides it: `p ∣ F` and `p ∣ F + 1` would force `p ∣ 1`, hence `p ≤ 1`.
  · intro p hp hdiv
    -- Every blocker divides the factorial: it is positive and at most `max + 1`.
    have hdvd : p ∣ (B.sup id + 1).factorial :=
      Nat.dvd_factorial (by have := h2 p hp; lia)
        (by have := Finset.le_sup (f := id) hp; exact Nat.le_succ_of_le this)
    -- Unfold both divisibilities into equations.
    obtain ⟨b, hb⟩ := hdiv
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hb
    -- `p * c + 1 = p * b`, so the difference `p * (b - c)` is `1`.
    have hp1 : p ∣ 1 := ⟨b - c, by rw [Nat.mul_sub]; omega⟩
    -- A divisor of `1` is at most `1`, contradicting `2 ≤ p`.
    have hp2 : p ≤ 1 := Nat.le_of_dvd (show 0 < 1 by norm_num) hp1
    have := h2 p hp
    omega

/-! ## One stage -/

/-- A number is certified at the next stage exactly when it is the least survivor. -/
def Step (B : Finset ℕ) (n : ℕ) : Prop := IsLeast (sieve B) n

/-- The number one stage certifies: the least survivor of `B`. -/
noncomputable def certifyOf (B : Finset ℕ) (h2 : ∀ p ∈ B, 2 ≤ p) : ℕ :=
  Nat.find (sieve_nonempty h2)

/-- One stage: certify the least survivor, and add it to the blockers. -/
noncomputable def advance (B : Finset ℕ) (c : ℕ) : Finset ℕ := insert c B

/-- The certified number at this stage is the least survivor. -/
theorem step_advance (B : Finset ℕ) (h2 : ∀ p ∈ B, 2 ≤ p) :
    Step B (certifyOf B h2) :=
  -- `Nat.find` gives a survivor, and it is minimal among survivors.
  ⟨Nat.find_spec (sieve_nonempty h2), fun _ hm => Nat.find_min' (sieve_nonempty h2) hm⟩

/-! ## The hypotheses carry to the next stage -/

/-- Every certified number is `≥ 2`, so the next stage's hypothesis holds by construction. -/
theorem above_one_advance {B : Finset ℕ} {c : ℕ} (h2 : ∀ p ∈ B, 2 ≤ p) (hc : 2 ≤ c) :
    ∀ p ∈ advance B c, 2 ≤ p := by
  intro p hp
  -- Either `p` is the new certified number, or it was already a blocker.
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact hc
  · exact h2 p hp

end CPNF
