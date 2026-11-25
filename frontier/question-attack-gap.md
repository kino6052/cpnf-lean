# Attack the gap: passing records beyond every bound

All Lean sources are attached and compile (`lake build`, no `sorry`, no axioms). The goal is
a **Lean running proof, and nothing else** — we do not claim a proof outside Lean, and we
are fine with a sharp conditional or a sharp no-go. What we want from you is the attack
that a modern frontier model plus Lean can actually close.

## The exact gap, in our language

We have proved the twin conjecture is equivalent to each of:

```lean
-- `score n = min(minFac(6n-1), minFac(6n+1))`
∀ K, ∃ n, K ≤ n ∧ score n = twinLo n        -- passing records beyond every bound
∀ K, ∃ n, K ≤ n ∧ twinHi n < score n * score n
∀ K, ∃ k, K ≤ head k ∧ Direct k
```

All three are `OftenDirect` / unbounded twins in different notation. The first is the one
to attack: `score n = twinLo n` is a single equality, and `twin_iff_score_eq_lo` shows it
means exactly "both members prime".

## What is already proved, so you do not redo it

- `certify_prime`, `stage_eq_primes_lt` — the process enumerates the primes in order.
- `minFac_sq_le` — a composite `m` has `minFac(m)² ≤ m`.
- `prime_of_minFac_gt` — `m ≤ B²` and no prime factor ≤ `B` forces `m` prime.
- `twin_iff_sq_test`, `twin_iff_score_eq_lo` — the twin test is one equality per `n`.
- `isRecord_of_twin`, `passing_record_iff_twin`, `no_passing_record_iff_no_twin` — a
  records-only scan is exact; a null scan is a theorem.
- `head_eq_iff_first_crossing` — records partition the heads; the death is at the endpoint.

## The obstacle, restated (from your earlier verdicts)

At a non-direct death the struck member is `c·q` with `q > 1` also surviving, so `q ≥ c`;
the gates force a *divisor event* but give no reason arbitrarily late deaths cannot all
carry such a cofactor. Squaring the members keeps the same head sequence and kills every
direct stage, so no argument uniform over member readouts can derive cofinal directness
from the shared gates alone. That is the parity shape, but not a literal factor-parity
identification, and not an impossibility theorem for CPNF.

## What I am asking you to decide

1. **What is the strongest statement a frontier + Lean can actually close?** Twin primes is
   open; do not pretend otherwise. Pick one of:
   - a clean *conditional* — e.g. "twins follow from hypothesis H", where H is simple,
     checkable, and ideally itself a statement about the score/record sequence, not a
     restatement of twin primes;
   - a *concrete reduction* — prove the gap is equivalent to a statement that a finite or
     decidable computation could in principle certify (a π-function bound, a prime-gap
     statement, a sieve-density identity) that is **not** just twins again;
   - a *sharp no-go* — prove that no argument of a certain shape (e.g. using only
     `Survives`, `certify`, monotonicity) can close the gap, which would tell us exactly
     what new ingredient is needed.
2. **For the choice you make, give the first Lean lemma** — signature plus the one-line
   idea, so we can start checking it immediately. Prefer statements expressible with the
   `score`/`minFac`/`certify` primitives we already have.
3. **Name the new ingredient.** If the answer is "nothing in this framework suffices",
   say which single outside fact (an analytic prime-counting estimate, a sieve upper
   bound, a modular structure theorem) is the cheapest one to import, and why that one.

Constraints: only `import Mathlib`; the aim is a proof that runs in Lean. A conditional or
a no-go is a success; a hand-waving density heuristic is not.
