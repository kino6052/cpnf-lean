import Mathlib
import CpnfLean.Obstruction
import CpnfLean.Progression

/-!
# CPNF — the scale obstruction, structural half

Three pieces of the frontier's obstruction, compiled.

**Marks avoid the nine primes.** A mark `N < (6n±1).minFac` with `N ≥ 31` has no divisor
among `{5,7,11,13,17,19,23,29,31}`: any such divisor would force `minFac ≤ 31 ≤ N`. This is
what makes inclusion–exclusion over the nine primes legitimate.

**Kill implies residue.** The converse direction the frontier flagged as missing: a wheel-killed
row really is `n ≡ 1` or `n ≡ 34 (mod 35)`. Without it one cannot bound *how many* classes are
killed, only that two *are*.

**Capacity lower bound.** In `L` consecutive integers at most `2⌈L/35⌉` rows are killed, so the
wheel capacity is at least `L − 2(L/35 + 1) ≥ (33/35)L − 2`.

Still open: the inclusion–exclusion count `a ≤ ρL + 512` for one column (not in Mathlib; must
be built), and of course the last-16-levels search itself.

No `sorry`, no `axiom`.
-/

namespace CPNF


/-- The nine primes of the obstruction. -/
def ninePrimes : Finset ℕ := {5, 7, 11, 13, 17, 19, 23, 29, 31}

/-- Every member of `ninePrimes` is at most 31 and at least 2. -/
theorem ninePrimes_le {p : ℕ} (hp : p ∈ ninePrimes) : 2 ≤ p ∧ p ≤ 31 := by
  simp only [ninePrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- A low mark has no divisor from the nine primes, once `N ≥ 31`. -/
theorem loMark_no_nine_dvd {N n p : ℕ} (h31 : 31 ≤ N)
    (hn : n ∈ loMarks N) (hp : p ∈ ninePrimes) : ¬ p ∣ twinLo n := by
  intro hd
  have h2 := (ninePrimes_le hp).1
  have hle : (twinLo n).minFac ≤ p := Nat.minFac_le_of_dvd h2 hd
  unfold loMarks at hn
  obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hn
  have hp31 := (ninePrimes_le hp).2
  omega

/-- A high mark has no divisor from the nine primes, once `N ≥ 31`. -/
theorem hiMark_no_nine_dvd {N n p : ℕ} (h31 : 31 ≤ N)
    (hn : n ∈ hiMarks N) (hp : p ∈ ninePrimes) : ¬ p ∣ twinHi n := by
  intro hd
  have h2 := (ninePrimes_le hp).1
  have hle : (twinHi n).minFac ≤ p := Nat.minFac_le_of_dvd h2 hd
  unfold hiMarks at hn
  obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hn
  have hp31 := (ninePrimes_le hp).2
  omega

/-- The converse direction: a killed row really is in class 1 or 34 mod 35. -/
theorem mod_of_wheelKilled {n : ℕ} (hn : 1 ≤ n) (hk : wheelKilled n) :
    n % 35 = 1 ∨ n % 35 = 34 := by
  unfold wheelKilled twinLo twinHi at hk
  rcases hk with ⟨h5, h7⟩ | ⟨h7, h5⟩
  · -- 5 | 6n-1 and 7 | 6n+1  =>  n ≡ 1 mod 5 and n ≡ 1 mod 7
    obtain ⟨a, ha⟩ := h5
    obtain ⟨b, hb⟩ := h7
    omega
  · obtain ⟨a, ha⟩ := h7
    obtain ⟨b, hb⟩ := h5
    omega



/-- In `L` consecutive integers, the rows killed by the wheel number at most `2⌈L/35⌉`. -/
theorem killed_range_le (L : ℕ) :
    ((Finset.range L).filter (fun j => j % 35 = 1 ∨ j % 35 = 34)).card ≤
      2 * ((L + 34) / 35) := by
  have h35 : 0 < 35 := by norm_num
  have hsub : (Finset.range L).filter (fun j => j % 35 = 1 ∨ j % 35 = 34) ⊆
      (Finset.range L).filter (fun j => j % 35 = 1) ∪
      (Finset.range L).filter (fun j => j % 35 = 34) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hj.2 with h | h
    · exact Or.inl ⟨hj.1, h⟩
    · exact Or.inr ⟨hj.1, h⟩
  have h1 := card_mod_eq_le 35 L 1 h35
  have h34 := card_mod_eq_le 35 L 34 h35
  have heq : L + 35 - 1 = L + 34 := by omega
  rw [heq] at h1 h34
  have hunion : ((Finset.range L).filter (fun j => j % 35 = 1) ∪
      (Finset.range L).filter (fun j => j % 35 = 34)).card ≤
      ((Finset.range L).filter (fun j => j % 35 = 1)).card +
      ((Finset.range L).filter (fun j => j % 35 = 34)).card :=
    Finset.card_union_le _ _
  have hfe : ((Finset.range L).filter (fun j => j % 35 = 1 ∨ j % 35 = 34)).card ≤
      ((Finset.range L).filter (fun j => j % 35 = 1) ∪
       (Finset.range L).filter (fun j => j % 35 = 34)).card :=
    Finset.card_le_card hsub
  have := Nat.le_trans hfe hunion
  omega

end CPNF
