import Mathlib

/-!
# CPNF — progression counting (the finite core of the top-band bound)

The single fact that turns the wheel count into a bound on rows hit by a band prime:
**among `L` consecutive integers, a fixed residue class modulo `q` contains at most
`⌈L/q⌉ = (L+q-1)/q` of them.** The proof injects `j ↦ j/q` into `[0, ⌈L/q⌉)`; the two
lemmas `ceil_div_le` and `card_mod_eq_le` capture the ceiling identity and the injection.

No primes, no estimates — pure finite arithmetic. This is the honest core behind the
frontier's corrected "≤ 2 hits" statement (two signs, each at most one residue class mod `q`).
-/

namespace CPNF


theorem ceil_div_le (q L : ℕ) (hq : 0 < q) (hL : 1 ≤ L) :
    (L - 1)/q + 1 ≤ (L + q - 1)/q := by
  rw [Nat.le_div_iff_mul_le hq]
  have hdiv : ((L - 1) / q) * q ≤ L - 1 := Nat.div_mul_le_self (L - 1) q
  have hmul : ((L - 1) / q + 1) * q = ((L - 1) / q) * q + q := by ring
  rw [hmul]
  omega
/-- Consecutive integers hit a residue class at most `⌈L/q⌉` times. -/
theorem card_mod_eq_le (q L r : ℕ) (hq : 0 < q) :
    ((Finset.range L).filter (fun j => j % q = r)).card ≤ (L + q - 1)/q := by
  by_cases hrq : r < q
  · by_cases hL : 1 ≤ L
    · have hle : ((Finset.range L).filter (fun j => j % q = r)).card ≤
          (Finset.range ((L - 1) / q + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun j => j / q)
        · intro j hj
          rw [Finset.mem_coe] at hj
          rw [Finset.mem_filter] at hj
          have hjL : j < L := Finset.mem_range.mp hj.1
          have hjle : j ≤ L - 1 := by omega
          have hdiv : j / q ≤ (L - 1) / q := Nat.div_le_div_right hjle
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hdiv)
        · intro j₁ hj₁ j₂ hj₂ he
          have hm₁ : j₁ % q = r := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
          have hm₂ : j₂ % q = r := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
          have h₁ : q * (j₁ / q) + r = j₁ := by rw [← hm₁]; exact Nat.div_add_mod j₁ q
          have h₂ : q * (j₂ / q) + r = j₂ := by rw [← hm₂]; exact Nat.div_add_mod j₂ q
          change j₁ / q = j₂ / q at he
          rw [he] at h₁
          omega
      have hcard : (Finset.range ((L - 1) / q + 1)).card = (L - 1) / q + 1 := Finset.card_range _
      rw [hcard] at hle
      exact le_trans hle (ceil_div_le q L hq hL)
    · have hL0 : L = 0 := by omega
      subst L
      simp
  · have hempty : ((Finset.range L).filter (fun j => j % q = r)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have hnot : ¬ j % q = r := by
        have := Nat.mod_lt j hq
        omega
      simp [hnot]
    rw [hempty]
    exact Nat.zero_le _

end CPNF
