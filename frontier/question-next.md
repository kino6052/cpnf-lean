# Frontier call: give us the next formalization steps, in order

You already gave us the bridge theorem, the exact count, and the crossing step.
We formalized the crossing step (`twinSieve_of_lt_two_mul`) and it compiles. Now
we need a concrete, ordered build plan — not a review, a sequence of precise
statements we can prove one at a time.

## Current repo state (all compiles, no `sorry`, no `Nat.Prime` in the gates)

- `Process.lean`: `sieve_nonempty` (`∀ p ∈ B, 2 ≤ p → (sieve B).Nonempty`),
  `Step`, `advance`, `step_advance`, `above_one_advance`.
- `Stage.lean`: `stage k`, `certify k`, `stage_succ` (`stage (k+1) = insert
  (certify k) (stage k)`), `step_stage`, `stage_subset_of_le`,
  `always_a_next_step`, `certify_survives`, `above_one_stage`.
- `TwinStage.lean`: `maxBlocker k = (stage k).sup id`,
  `stageWindow k = window (maxBlocker k)`,
  `searchSet k = twinSieve (stage k) (maxBlocker k)`,
  `TwinCertifiedAt k n = IsLeast (searchSet k) n`,
  `certifiedAt_admissible / _in_window / _least`,
  `admissible_of_stage_le`, `stageWindow_ge (7 ≤ y → y ≤ window y)`,
  and the new `twinSieve_of_lt_two_mul`: for `y ≥ 3`, if `twinLo n < 2y` and
  `Admissible (stage k) n`, then `n ∈ twinSieve (stage k) y`.

We hold these facts already (definitions in `Twin.lean`): `twinLo n = 6n-1`,
`twinHi n = 6n+1`, `Admissible B n = Survives B (twinLo n) ∧ Survives B (twinHi n)`,
`window y = (y^2-1)/6`, `twinSieve B y = {n | Admissible B n ∧ n ≤ window y}`.

## What we want from this call — a numbered build order

Give us the statements, fully quantified, in the order they should be proved.
For each one: its exact Lean-level statement (hypotheses and conclusion), why it
comes now, and what it depends on. We will prove them in this order.

Specifically we need precise statements for:

1. **Canonical-prefix invariant.** What exactly is `stage k` after the first
   `k` steps, when the run starts from the empty blocker set? Is it "the first
   `k` primes" (for `k ≥ 1`)? Give the inductive statement and what the base case
   needs. This is where `Nat.Prime` first appears — mark it as correspondence
   layer, not a gate.

2. **Window exactness.** For `1 ≤ n ≤ window y`, `n ∈ twinSieve B y` iff
   `twinLo n` and `twinHi n` are both prime and `> y`, on the canonical run.
   Give the exact statement and the two directions' dependencies (which need the
   canonical-prefix invariant, which need only arithmetic).

3. **Bridge theorem.** `(∃ K, ∀ k ≥ K, searchSet k = ∅)` ⇔ `¬ UnboundedTwins`,
   or the contrapositive: non-stagnation ⇔ unbounded twins. Give the cleanest
   formulation with the least `Nat.Prime` leakage, and which direction uses
   Bertrand (`p < 2y`) vs which is arithmetic.

4. **Exact count.** The `|G| + Σ_odd C_S = Σ_even C_S` identity with
   `d_S = Π S`, `T_S = {r ∈ [1,d_S] | ∀ b ∈ S, (6r mod b) = 1 ∨ = b-1}`,
   `C_S = Σ_{r∈T_S} ((W+d_S-r)/d_S)`, and `|T_S| = 2^{|S|}`. Give the exact
   `ℕ` statement we should prove, and the smallest intermediate lemmas (CRT
   invertibility of 6, the single-progression count, then the alternating sum).

5. **Anything we should prove between these.** Flag if the order above is wrong
   and what should come first/last, and any lemma that is false as stated.

## Constraints

- Constructive, finite, `ℕ`-first. Mertens and covering systems stay out.
- `Nat.Prime` only inside the correspondence/bridge layer, clearly separated
  from the CPNF process gates.
- Prefer short true statements over ambitious ones. We will prove them in Lean,
  so exact quantification matters more than intuition.
