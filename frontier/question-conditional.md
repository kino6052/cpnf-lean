# Attack the conditional: prove it, refute it, or find the right statistic

All Lean sources are attached and compile (`lake build`, no `sorry`, no axioms). Be bold.
A creative reframing that turns `CofinalScoreMass` into something genuinely weaker, yet
still sufficient, is worth more to us than a careful restatement of the difficulty.

## The state of the project

Everything except one hypothesis is now a Lean theorem:

```lean
def score (n : ℕ) : ℕ := min (twinLo n).minFac (twinHi n).minFac   -- twinLo n = 6n-1, twinHi n = 6n+1

theorem twin_iff_score_eq_lo {n : ℕ} (hn : 1 ≤ n) :
    (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) ↔ score n = twinLo n

theorem isRecord_of_twin {n : ℕ} (hn : 1 ≤ n) (hp : _) (hq : _) : IsRecord n

theorem passing_record_iff_twin {n : ℕ} (hn : 1 ≤ n) :
    (IsRecord n ∧ twinHi n < score n * score n) ↔ (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n))

theorem head_eq_iff_first_crossing {k n : ℕ} (hn : 1 ≤ n) : head k = n ↔ ...

theorem failing_score_le_four_mul {t n : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hN : n ≤ 2 * t ^ 2) (hf : score n ≠ twinLo n) : score n ≤ 4 * t

def momentBlock (t : ℕ) : Finset ℕ := Finset.Icc (t ^ 2) (2 * t ^ 2)
def scoreMass (t : ℕ) : ℕ := ∑ n ∈ momentBlock t, score n
def passingRows (t : ℕ) : Finset ℕ := (momentBlock t).filter (fun n => score n = twinLo n)

theorem passingRows_gt_of_mass {t r : ℕ} (ht : 1 ≤ t)
    (hm : (momentBlock t).card * (4 * t) + r * (12 * t ^ 2) < scoreMass t) :
    r < (passingRows t).card

def CofinalScoreMass : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧ (momentBlock t).card * (4 * t) < scoreMass t

theorem twins_of_scoreMass (H : CofinalScoreMass) :
    ∀ K, ∃ n, K ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)
```

So `CofinalScoreMass` is the whole remaining gap. It is a **mean score > 4t on cofinally
many square-scale blocks**, with `score n = min(minFac(6n-1), minFac(6n+1))`.

## Three things I suspect, and want you to settle

1. **`CofinalScoreMass` may be equivalent to twin primes in disguise.** A passing row has
   score `6n-1 ≈ 6t²`, enormously above the threshold `4t`. A block with a single passing
   row gets a huge contribution. Is `CofinalScoreMass` therefore just "cofinally many
   passing rows" restated, or can the mass be met *without* any passing row? Compute the
   honest answer: what is the actual size of `scoreMass` for a block with no passing rows?

2. **What is the weakest sufficient statistic?** We want something strictly weaker than
   twins but still sufficient. Candidates I can see, please judge and improve:
   - a **maximum** statement rather than a mean: `sup_{n ≤ N} score n` grows faster than
     the trivial `≤ 6N-1` in a way that forces a passing row;
   - a **variance / second-moment** statement, since failing rows are capped at `4t` while
     passing rows are `Θ(t²)` — the gap is enormous, so maybe one outlier suffices and a
     mean is the wrong instrument;
   - a **counting** statement: the number of `n` with `score n ≥ y` for a variable cut `y`,
     which would connect to sieve upper bounds;
   - a **record-based** statement: cofinally many strict records (not necessarily passing),
     which we already know how to prove things about via `head_eq_iff_first_crossing`.

3. **If it cannot be weakened, prove it equivalent** — a Lean-checkable equivalence
   `CofinalScoreMass ↔ ∀ K, ∃ n ≥ K, score n = twinLo n` would at least tell us we have not
   moved the goalposts, and would let us stop trying to weaken it.

## What to give us

- The verdict on (1), honestly, with the computation.
- The best candidate from (2), or a better one you invent, stated as a `def ... : Prop`
  with the sufficiency theorem `... → twin primes` and the first Lean lemma in shape.
- If (3), the two directions as Lean statements.

Constraints: `import Mathlib` only, everything must end up as a running Lean proof. A
bold reframing is welcome; an uncheckable heuristic is not. We do not claim a proof of twin
primes outside Lean, and we are happy with a sharper conditional or a clean equivalence.
