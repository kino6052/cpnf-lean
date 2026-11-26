# Rung 3 (`middle_or_pass`): give a Lean-compilable statement + proof, using what is already compiled

We are building the unconditional ladder to the boxed condition, and three of four rungs are
already compiled in Lean (all `import Mathlib`, v4.36.0, no `sorry`, build green). Rung 3 is
the last heavy one. Give us a **complete, finite, Lean-compilable** statement and a proof plan
that uses exactly the lemmas we already have (listed below). Flag any step that secretly
needs an analytic estimate.

## Vocabulary (already in our files, compiled)

- `twinLo n = 6*n - 1`, `twinHi n = 6*n + 1`, `score n = min ((twinLo n).minFac) ((twinHi n).minFac)`.
- `window h = (h^2 - 1)/6` (natural division), `le_window_iff`.
- `midP / midB / midT / rough` partition (in `Ladder.lean`):
  - `rough X z = {n ∈ (X,2X] : z < score n}`
  - `midB = {n : score² ≤ X}`, `midT = {n : X < score² ≤ twinHi}`, `midP = {n : score = twinLo}`
  - `local_slack_iff (X z) (hz : z < 6*X - 1) : |midB| + |midT| < |rough| ↔ ∃ n ∈ (X,2X], score n = twinLo n`
- `wheel_block (a : ℕ) : #{b ∈ [a+1, a+210] : Coprime b 210} = 48` (in `Wheel.lean`),
  and `gcd_mod_self`.
- Factorial avoidance (in `Coverage.lean`): `not_dvd_succ_of_dvd`, `not_dvd_pred_of_dvd`,
  `minFac_gt_of_no_small_dvd`, `score_unbounded` — the machinery that at `n = (h+1)!` gives
  `score n > h`.

## The rung (your own earlier description, restated)

> A residue-class version of the top-band exclusion: pre-sieve by any fixed set of small
> primes and *still* exclude the top band on a positive fraction of the pre-sieved rows.
> Thus, under no witness, you can force many **middle-band** deaths.

Concretely, we want a theorem of this shape, with **explicit constants and no "sufficiently
large" quantifier**:

```lean
theorem middle_or_pass (X z M r : ℕ) (hX : z ≤ Nat.sqrt X) ... :
    -- S = classBlock X M r (rows of (X,2X] with n % M = r),
    -- and every top-band prime is coprime to M,
    -- then: |S| ≤ 20 * |D| + (something explicitly bounded by the wheel count),
    -- where D = rows of S hit by a top-band prime
```

The point: `D` is *forced* — its complement in `S` either passes (`score = twinLo`) or has a
killer above `z`. We want the count of non-passing rows to be quantitatively bounded by
`20 |D|` on the rows that survive the pre-sieve.

## What we need from you

1. **The exact theorem statement** in Lean, using the above names, with concrete constants.
   Give the full signature (hypotheses and conclusion), so we can transcribe it directly.
2. **The proof plan**, step by step, naming which compiled lemma covers each step:
   - how the top band is split into `k` blocks of length 210 (where `k = ⌊√X⌋ / 210` or
     your choice),
   - how `wheel_block` bounds the number of coprime candidates per block,
   - how the "≤ 2 hits per prime" fact is stated and used (a prime `q > √X` divides
     `twinLo n` or `twinHi n` for at most 2 values of `n` in a residue class — is this true,
     and what is the exact Lean statement?),
   - how `local_slack_iff` turns "no witness" into "every non-passing row is in `D`".
3. **The exact arithmetic** that yields `20 |D| ≥ ...` — spell out `96k`, `192k`, `288k`,
   `8064k`, `20U ≤ 19L` as you did before, and say which is a theorem and which is just
   rewriting.
4. **Honest wall check**: is any step actually a prime-counting estimate in disguise? If the
   "≤ 2 hits" step is wrong for a prime `q` that can divide both `6n-1` and `6n+1`, say so
   and give the corrected finite statement.

Keep it Lean-first: every quantifier over `ℕ`, every set a `Finset`, no `ℝ`, no asymptotics.
Paper and all Lean sources (including `Wheel.lean`, `Charge.lean`, `Ladder.lean`) attached.
