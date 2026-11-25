# Prove or disprove CofinalScoreEnergy

All Lean sources are attached and compile (`lake build`, no `sorry`, no axioms). Do not
ask whether it is provable. **Prove it or disprove it.** Work as a mathematician, not a
scribe. We only accept a Lean-checkable proof or a Lean-checkable refutation (or a clean
reduction to a named theorem, stated as an implication we can formalize).

## The statement

```lean
def score (n : ℕ) : ℕ := min (twinLo n).minFac (twinHi n).minFac   -- twinLo n = 6n-1, twinHi n = 6n+1

def CofinalScoreEnergy : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ 2 ≤ N ∧
    (∑ n ∈ Finset.Icc N (2*N), twinHi n) <
      (∑ n ∈ Finset.Icc N (2*N), score n * score n)
```

Everything around it is proved, including `energy_iff_cofinal_pass`:

```lean
theorem energy_iff_cofinal_pass :
    CofinalScoreEnergy ↔ ∀ K : ℕ, ∃ n, K ≤ n ∧ score n = twinLo n   -- proved

theorem twins_of_scoreEnergy (H : CofinalScoreEnergy) :
    ∀ K, ∃ n, K ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)    -- proved
```

So `CofinalScoreEnergy` is exactly twin primes in this language. **Prove it, or disprove
it** (a refutation would be a counterexample block for every large `N`, i.e. a proof that
twin primes are finite — which would itself be a result we would formalize).

## The facts at your disposal

- `score n = 6n-1` iff both `6n-1`, `6n+1` are prime; otherwise `score n ≤ √(6n+1)`
  (composite members have a factor at most their root).
- One twin row at `n ≥ N` has `score² = (6n-1)² ≥ (6N-1)²`, exceeding the whole budget
  `Σ_{N}^{2N}(6n+1) ≤ (N+1)(12N+1)`.
- So the inequality is a block detector for "contains a twin pair".

## What to deliver

1. A proof or a disproof of `CofinalScoreEnergy`, as a sequence of Lean-checkable lemmas —
   the first one stated with signature and one-line idea.
2. If you prove it via a named theorem (sieve lower bound, Bombieri–Vinogradov,
   Elliott–Halberstam, Hardy–Littlewood, prime-gap bound), name the theorem and give the
   exact implication with that theorem as the hypothesis, so we can formalize the
   conditional even if the named theorem is not yet in Mathlib.
3. If you find a counterexample (a proof that the inequality fails cofinally often), state
   the first lemma and the idea.

Be concrete. First lemma in Lean shape now.
