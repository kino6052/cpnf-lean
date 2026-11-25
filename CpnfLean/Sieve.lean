import Mathlib

/-!
# CPNF — the sieve operator

The only primitive of the framework: a number survives a set of blockers when none of
them divides it. No primality is assumed here.

Blockers are kept as a `Finset`: the process only ever certifies into a finite set, and a
finite set is exactly what decides "survives" stage by stage.
-/

namespace CPNF

/-- `Survives B n`: `n` is not divisible by any blocker in `B`. -/
def Survives (B : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ B, ¬ p ∣ n

instance (B : Finset ℕ) (n : ℕ) : Decidable (Survives B n) :=
  inferInstanceAs (Decidable (∀ p ∈ B, ¬ p ∣ n))

/-- The sieve operator of the paper: survivors of `B` among the candidates `≥ 2`. -/
def sieve (B : Finset ℕ) : Set ℕ := { n | 2 ≤ n ∧ Survives B n }

instance (B : Finset ℕ) (n : ℕ) : Decidable (n ∈ sieve B) :=
  inferInstanceAs (Decidable (2 ≤ n ∧ Survives B n))

theorem survives_empty (_n : ℕ) : Survives ∅ _n := by
  intro p hp
  exact absurd hp (Finset.notMem_empty p)

/-- Membership in the sieve, spelled as a plain conjunction: this is the shape every
    later proof uses, so it never has to be rebuilt inline. -/
theorem mem_sieve_iff {B : Finset ℕ} {n : ℕ} : n ∈ sieve B ↔ 2 ≤ n ∧ Survives B n := Iff.rfl

/-- A divisor of a number is at most it, once the number is positive. Surviving a blocker
    therefore survives at least that blocker — not the other way round, which is false
    (`2 < 4` yet `2 ∣ 4`). -/
theorem le_of_dvd_pos {p n : ℕ} (hp : 0 < n) (h : p ∣ n) : p ≤ n := Nat.le_of_dvd hp h

/-- Adding blockers can only remove survivors. -/
theorem sieve_insert_subset (B : Finset ℕ) (c : ℕ) : sieve (insert c B) ⊆ sieve B := by
  rintro n ⟨h2, hs⟩
  exact ⟨h2, fun p hp => hs p (Finset.mem_insert_of_mem hp)⟩

theorem survives_insert_of_survives {B : Finset ℕ} {c n : ℕ} (hs : Survives B n)
    (hcn : ¬ c ∣ n) : Survives (insert c B) n := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact hcn
  · exact hs p hp

end CPNF
