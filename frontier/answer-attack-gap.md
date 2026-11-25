```lean
/-!
Append after `end CPNF` in `Correspondence.lean`. No new imports.

Choice: a conditional on the first moment of the score. The input statistic
sums all scores in a block: it tests neither primality nor record status.
The finite theorem gives a lower bound on the number of passing rows, not
just a test for existence.
-/

namespace CPNF

/-- First lemma: a failing row at index at most `2*t²` contributes at most
`4*t` to the score sum. Square the proposed bound and use the composite cap. -/
theorem failing_score_le_four_mul {t n : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hN : n ≤ 2 * t ^ 2) (hf : score n ≠ twinLo n) :
    score n ≤ 4 * t := by
  have hlt : score n < twinLo n := lt_of_le_of_ne (score_le_lo n hn) hf
  have hs := score_sq_le_hi_of_gt hn hlt
  have ht2 : 1 ≤ t ^ 2 := by positivity
  apply Nat.mul_self_le_mul_self_iff.mp
  unfold twinHi at hs
  nlinarith only [hs, hN, ht2]

def momentBlock (t : ℕ) : Finset ℕ := Finset.Icc (t ^ 2) (2 * t ^ 2)

def scoreMass (t : ℕ) : ℕ := ∑ n ∈ momentBlock t, score n

def passingRows (t : ℕ) : Finset ℕ :=
  (momentBlock t).filter (fun n => score n = twinLo n)

/-- A budget for `r` passing rows: allow `4*t` per row and an extra
`12*t²` for each pass. Exceeding that budget certifies more than `r` passes. -/
theorem passingRows_gt_of_mass {t r : ℕ} (ht : 1 ≤ t)
    (hm : (momentBlock t).card * (4 * t) + r * (12 * t ^ 2) < scoreMass t) :
    r < (passingRows t).card := by
  have hrow (n : ℕ) (hn : n ∈ momentBlock t) :
      score n ≤ 4 * t + (if score n = twinLo n then 12 * t ^ 2 else 0) := by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp (show n ∈ Finset.Icc (t^2) (2*t^2) from hn)
    have ht2 : 1 ≤ t ^ 2 := by positivity
    have hn1 : 1 ≤ n := ht2.trans hl
    by_cases hp : score n = twinLo n
    · rw [if_pos hp, hp]
      unfold twinLo
      omega
    · rw [if_neg hp, Nat.add_zero]
      exact failing_score_le_four_mul ht hn1 hu hp
  have hbudget : scoreMass t ≤
      (momentBlock t).card * (4 * t) + (passingRows t).card * (12 * t ^ 2) := by
    calc
      scoreMass t ≤ ∑ n ∈ momentBlock t,
          (4 * t + (if score n = twinLo n then 12 * t ^ 2 else 0)) :=
        Finset.sum_le_sum hrow
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [passingRows, Nat.nsmul_eq_mul]
  by_contra! h
  exact (not_lt_of_ge (hbudget.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right (12 * t ^ 2) h) _))) hm

/-- The single new ingredient requested of an outside estimate: on cofinally
many square-scale blocks, the mean score exceeds `4*t`. This is a finite
integer comparison for each proposed `t`; its cofinality is NOT certified
by any finite scan. No asymptotic formula or error term is required. -/
def CofinalScoreMass : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧ (momentBlock t).card * (4 * t) < scoreMass t

/-- The moment estimate suffices for the exact record target. -/
theorem passing_beyond_of_scoreMass (H : CofinalScoreMass) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ score n = twinLo n := by
  intro K
  obtain ⟨t, ht, hm⟩ := H (K + 1)
  have ht1 : 1 ≤ t := by omega
  have hc : 0 < (passingRows t).card :=
    passingRows_gt_of_mass (r := 0) ht1 (by simpa using hm)
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hc
  obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hn
  have hl : t ^ 2 ≤ n := (Finset.mem_Icc.mp hb).1
  have htsq : t ≤ t ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left t ht1
  exact ⟨n, by omega, hp⟩

end CPNF
```
