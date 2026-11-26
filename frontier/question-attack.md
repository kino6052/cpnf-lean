# Attack it: close the boxed gap by a route that avoids the known walls

We have reduced the twin conjecture, inside CPNF, to one exact statement. It is machine
checked (`Coverage.lean`, attached, builds with no `sorry`). **Attack this, creatively, and
avoid the walls that are already mapped.**

## The exact target (proved equivalent to the twin conjecture)

```lean
WindowWitness K := ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n
windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect
```

where `score n = min((6n−1).minFac, (6n+1).minFac)` and `window h = (h²−1)/6`.
In words:

> For every `K` there is an index `n ≥ K` and a threshold `h` with `6n+1 ≤ h²` and
> `score n > h`.

Equivalently: **some index in `[K, (h²−1)/6]` has no prime factor `≤ h` in either member.**
That is all that is needed. No uniform gaps, no bounded ratios, no twins in every block.

## The gap, measured

- **We can prove** (`score_unbounded`): unbounded `score` at factorial location `n = (h+1)!`.
- **A sieve gives**: every interval of `h⁵` consecutive indices contains such an `n`
  (dimension-2 beta sieve, level `D = H/(log H)^10`, uniform in the start point).
- **Needed**: the witness must satisfy `n ≤ (h²−1)/6`, and the interval must reach beyond `K`.

So the requirement is roughly `h²` instead of `h⁵`: a factor `h³` too strong. Note the
subtlety: the sieve gives room `h⁵` **but the witness it produces is just above `h` in
score**, whereas the boxed condition allows an enormous `h` for a given `n`. The boxed
condition is *not* obviously weaker — it lets `h` be as large as `√(6n)`, i.e. up to the
twin cutoff.

## The walls already mapped — do not walk into these

1. **Parity.** Any argument that counts prime factors of `6n±1` evenly dies.
2. **The `≈2` sifting ratio.** At cutoff `√(12X+1)`, survival *is* twindom, so the ratio
   hits `≈2`, outside every positive lower-bound sieve range.
3. **Fixed-modulus projection.** Already refuted by us: a fresh prime `q ∤ 6M` hits exactly
   2 of the `q` lifts of every old residue, so the hit bit is not a function of the old
   label. Appendix D's finite-subcover step is invalid; do not reuse it.
4. **The prime order.** Already refuted: the cubic-domain comparison chase has the same
   primes and residues and produces proper deaths forever. Any argument must use the *full*
   index set, not the sieve's order.

## What we want — one creative strategy, specified to the lemma

Give **one** attack (or at most two, if genuinely different), chosen for creativity and for
avoiding all four walls. For the attack, be concrete:

- **The idea in one paragraph**, in the process vocabulary if it helps, but the mathematics
  must be standard and checkable.
- **The first lemma**, stated in Lean-ready form using `score`, `window`, `minFac`,
  `twinLo`, `twinHi` — something finite and provable, that is a genuine step toward the
  boxed condition. Not a restatement of it.
- **Why it dodges the four walls**, wall by wall.
- **The most likely failure point**, named honestly.
- **What the attack would prove if it worked**: the boxed condition, or a weaker but still
  new statement?

Be bold. A clever reformulation that turns the boxed condition into something with a
*known* technique is worth more than a restatement of the barrier. If you believe the boxed
condition is genuinely out of reach of current mathematics, say so and give the sharpest
provable statement that *would* have been a step — we will formalize that instead.

Paper and all Lean sources (now including `Coverage.lean`) attached.
