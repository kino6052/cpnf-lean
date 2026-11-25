# Finalise the record-scan layer

All Lean sources are attached and compile (`lake build`, no `sorry`, no axioms). I want you
to finalise — that means: confirm what is correct, correct what is subtly wrong, and tell
me whether there is a *stronger* or *cleaner* statement I should aim for next.

## The new layer (`CpnfLean/Correspondence.lean`, section "Records")

```lean
def IsRecord (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → score m < score n

theorem score_le_lo (m : ℕ) (hm : 1 ≤ m) : score m ≤ twinLo m := ...

theorem isRecord_of_twin {n : ℕ} (hn : 1 ≤ n)
    (hp : Nat.Prime (twinLo n)) (hq : Nat.Prime (twinHi n)) : IsRecord n := ...

theorem no_passing_record_iff_no_twin (N : ℕ) :
    (∀ n, 1 ≤ n → n ≤ N → IsRecord n → ¬ twinHi n < score n * score n) ↔
    (∀ n, 1 ≤ n → n ≤ N → ¬ (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n))) := ...
```

`score`, `twin_iff_sq_test` (`both prime ↔ 6n+1 < score n²`), `minFac_eq_self_of_prime`,
`minFac_sq_le`, `head_le_iff` all compile earlier in the file.

## What I think is true, and want checked

1. **`IsRecord` as stated is the right notion.** Strict, not weak. A weak record (score
   `≥` max of earlier) would allow ties and break the run-length claim. Confirm the strict
   form is the one that gives a *partition* of stages, or correct it.

2. **`isRecord_of_twin` is the completeness direction.** It is what makes a records-only
   scan exact — no twin pair hides behind a non-record. Is the bound `score m ≤ 6m - 1 <
   6n - 1` the cleanest route, or is there a one-line `minFac`-free argument?

3. **`no_passing_record_iff_no_twin` is stated with two `∀`s and a `¬`.** I believe this is
   exactly the finite-scan theorem: a finished scan proves "no twin in `[1, N]`" when it
   finds no passing record, and proves "a twin in `[1, N]`" when it finds one (via
   `twin_iff_sq_test`). But this form is asymmetric — the positive side ("a passing record
   *is* a twin at that `n`") is hidden inside `twin_iff_sq_test`. Is there a cleaner
   symmetric statement, e.g. an equality of two `Finset`s of indices

   `(Finset.filter (fun n => IsRecord n ∧ 6n+1 < score n²) (Finset.Icc 1 N))
     = (Finset.filter (fun n => both prime) (Finset.Icc 1 N))`

   and is that actually more useful, or just prettier?

4. **The plateau/head link is still missing.** The frontier earlier said one record covers
   a whole run of heads, with the death only at the endpoint. I have `head_le_iff` and
   `IsRecord` but have *not* proved a lemma tying a record to the heads it certifies. What
   is the exact statement, and is it worth adding now or is it dead weight for the twin
   target?

5. **Honest bottom line:** nothing here forces a passing record to occur beyond every
   bound — that remains the conjecture. State in one line whether this layer changes the
   *shape* of the obstacle (records vs stages vs primes) or merely renames it.

Please give: corrections to the four lemmas where wrong, the cleanest statement of each,
and a yes/no on whether to add the plateau lemma now.
