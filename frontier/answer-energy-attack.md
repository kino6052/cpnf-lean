```lean
import CpnfLean.Correspondence

namespace CPNF

/-- Idea: for p ≤ 7 use the values (11,13); for p > 7 use (5,7). -/
lemma dickson_twin_admissible (p : ℕ) (hp : Nat.Prime p) :
    ∃ m : ℕ, ¬ p ∣ 6*m + 5 ∧ ¬ p ∣ 6*m + 7 := by
  by_cases h : p ≤ 7
  · refine ⟨1, ?_⟩
    have h2 := hp.two_le
    interval_cases p <;> norm_num
  · refine ⟨0, ?_⟩
    change (¬ p ∣ 5) ∧ (¬ p ∣ 7)
    constructor <;> intro hd
    · have := Nat.le_of_dvd (by decide : 0 < 5) hd
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 7) hd
      omega
```

**Conditional reduction: Dickson’s conjecture for two linear forms implies `CofinalScoreEnergy`.** The hypothesis below is the positive-coefficient case: if for each prime there is an input at which it divides neither value, then there are arbitrarily large inputs at which both values are prime. The first lemma verifies the local hypothesis unconditionally; Dickson’s conjecture supplies the simultaneous primality.

```lean
def DicksonTwoPositive : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
    (∀ p : ℕ, Nat.Prime p →
      ∃ m : ℕ, ¬ p ∣ a*m + b ∧ ¬ p ∣ c*m + d) →
    ∀ K : ℕ, ∃ m : ℕ, K ≤ m ∧
      Nat.Prime (a*m + b) ∧ Nat.Prime (c*m + d)

theorem energy_of_dickson_two (H : DicksonTwoPositive) :
    CofinalScoreEnergy := by
  apply energy_iff_cofinal_pass.mpr
  intro K
  obtain ⟨m, hm, h5, h7⟩ :=
    H 6 5 6 7 (by decide) (by decide) (by decide) (by decide)
      dickson_twin_admissible K
  refine ⟨m + 1, by omega, (twin_iff_score_eq_lo (by omega : 1 ≤ m + 1)).mp ?_⟩
  have hlo : twinLo (m + 1) = 6*m + 5 := by unfold twinLo; omega
  have hhi : twinHi (m + 1) = 6*m + 7 := by unfold twinHi; omega
  rw [hlo, hhi]
  exact ⟨h5, h7⟩

end CPNF
```

This is a conditional, not an unconditional proof: the two-form Dickson hypothesis is unproved. On the refutation side, failure **cofinally often** would not suffice. The negation requires a cutoff beyond which **every** eligible block fails; by `energy_iff_cofinal_pass`, that would bound all passing rows and hence all twin indices.
