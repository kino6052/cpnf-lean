import Mathlib
import CpnfLean.Head
import CpnfLean.Correspondence

/-!
# CPNF — the charge identity (rung 1 of the unconditional ladder)

On a set of rows whose upper member is a product of **two** primes and carries character
sign `-1`, every composite row is charged to exactly **one** prime of sign `+1` that divides
it. That is the whole content, and it is unconditional finite arithmetic: a sign table
`χ : ℕ → ℤ` satisfying `χ(ab) = χ(a)χ(b)` is the only structure used.

The point of the assignment is the bound `m/(z+1)`, **not** `√m`: the sign selects a
*unique* factor, not the *smaller* one. Charging by the smaller factor would lose
information; charging by the sign does not.

What this is *not*: a statement that the selected set is large. The frontier's ledger is
explicit — this rung removes double counting on a chosen family but guarantees no rows.
-/

namespace CPNF


theorem prime_dvd_of_dvd_mul {q a b : ℕ} (hq : Nat.Prime q) (ha : Nat.Prime a) (hb : Nat.Prime b)
    (h : q ∣ a * b) : q = a ∨ q = b := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases ha.eq_one_or_self_of_dvd q h with h' | h'
    · exact absurd h' (Nat.Prime.ne_one hq)
    · exact Or.inl h'
  · rcases hb.eq_one_or_self_of_dvd q h with h' | h'
    · exact absurd h' (Nat.Prime.ne_one hq)
    · exact Or.inr h'

theorem semiprime_sign {s : ℕ → ℤ} (hmul : ∀ a b, s (a * b) = s a * s b)
    (hneg : s (a * b) = -1) (h1 : s a = 1 ∨ s a = -1) (h2 : s b = 1 ∨ s b = -1) :
    (s a = 1 ∧ s b = -1) ∨ (s a = -1 ∧ s b = 1) := by
  have hm := hmul a b
  rcases h1 with h | h
  · rcases h2 with h' | h'
    · rw [h, h'] at hm; omega
    · exact Or.inl ⟨h, h'⟩
  · rcases h2 with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · rw [h, h'] at hm; omega


/-- **Exactly one `+1`-sign factor above the cutoff divides a negative semiprime.** This is
    the mathematical heart of the charge: both factors exceed `z`, exactly one of them
    carries sign `+1`, and any other divisor is one of the two. -/
theorem exists_unique_plus_factor {s : ℕ → ℤ} (hmul : ∀ a b, s (a * b) = s a * s b)
    {m z : ℕ} (hneg : s m = -1)
    (hsemi : ∃ a b, z < a ∧ z < b ∧ Nat.Prime a ∧ Nat.Prime b ∧ m = a * b)
    (hsign : ∀ q, Nat.Prime q → s q = 1 ∨ s q = -1) :
    ∃! q, z < q ∧ q < m ∧ Nat.Prime q ∧ s q = 1 ∧ q ∣ m := by
  obtain ⟨a, b, hza, hzb, hpa, hpb, rfl⟩ := hsemi
  have hsig := semiprime_sign hmul hneg (hsign a hpa) (hsign b hpb)
  rcases hsig with ⟨hsa, hsb⟩ | ⟨hsa, hsb⟩
  · have hb2 : 2 ≤ b := hpb.two_le
    refine ⟨a, ⟨hza, by nlinarith, hpa, hsa, dvd_mul_right a b⟩, ?_⟩
    rintro q ⟨hzq, hqm, hpq, hsq, hdq⟩
    rcases prime_dvd_of_dvd_mul hpq hpa hpb hdq with rfl | rfl
    · rfl
    · rw [hsb] at hsq; omega
  · have ha2 : 2 ≤ a := hpa.two_le
    refine ⟨b, ⟨hzb, by nlinarith, hpb, hsb, dvd_mul_left b a⟩, ?_⟩
    rintro q ⟨hzq, hqm, hpq, hsq, hdq⟩
    rcases prime_dvd_of_dvd_mul hpq hpa hpb hdq with rfl | rfl
    · rw [hsa] at hsq; omega
    · rfl

end CPNF
