# Chisel the wall: coverage without density

We are attacking the twin conjecture directly, and we have now hit the exact wall your last
answer located. We want you to **chisel at it boldly** — not restate it, not dress it up.
Everything below is machine-checked (Lean sources attached); the only gap is the wall.

## Where we stand (proved, no density, no asymptotics)

- The chase is exact: no twin after `N` ⟺ every `n ≥ N` has `score n < 6n-1` (its killer is
  a proper factor), and a member is composite iff its least prime factor is `≤ √(6n+1)`.
- **The score is unbounded** — `score_unbounded`: at `n = (h+1)!`, every `d ≤ h` divides
  `6n`, so `6n±1` evade all of them; hence both members' least prime factors exceed `h`.
  The process never stagnates in *endurance*. It does **not** produce a twin.
- **The wall, as a Lean theorem** — `head_le_of_factor`: a head whose lower member has a
  factor `q ≤ t` is itself `≤ t`. Contrapositive: a head escaping `t` has *no* factor `≤ t`.
  At `t = √(6n+1)`, "no factor ≤ t" **is** twindom. Coverage reasoning stops exactly there.

## The wall, restated precisely

To get one twin in `(X, 2X]`, an index must survive all primes up to `√(12X+1)`. At that
cutoff survival *equals* being a twin, so the sifting ratio reaches `≈ 2` — outside the
positive lower-bound range of the beta sieve. The classical lower-bound sieve fails there.
Your earlier answer said this is "the same barrier family as parity, though not parity
itself."

## Chisel here — bold, concrete, and honest

Give us the **strongest true statement** of each kind, stated as a claim we could try to
prove in Lean (first-order, finite, `score`/`minFac`/`head` vocabulary, no analytic
estimates unless unavoidable):

1. **A covering-exclusion that avoids the `≈2` regime.** Is there a *strict* subset of
   moduli — e.g. primes `≤ √(6n+1)` that are themselves `> √(n)`-scale, or primes in a
   residue class — for which a *combinatorial* (finite, CRT, inclusion-exclusion) argument
   shows a positive density of indices survives *below* the twin cutoff? If yes, that is
   chiseling: it moves the wall inward.
2. **A short-interval pigeonhole.** `score_unbounded` gives one evading index per `h`, but
   at a super-exponential location (`(h+1)!`). Can the *same* witness be pushed down to
   polynomial location — i.e. is there `n ≤ h^C` with `score n > h`, by a better witness
   (e.g. `lcm(1..h)` instead of `h!`, or a product of primes only)? A polynomial witness is
   the single most useful thing: it turns "unbounded" into "within reach".
3. **The obstruction for CPNF's order, made first-order.** Your comparison chase (cubic
   domain `x³/6`) shows the *prime order* does not force directness. What is the *weakest*
   additional first-order property of the full index set (not the primes) that would force a
   direct death? Candidate: the full set is *1-dense at every scale* (every `[n, n+L]` hits
   a surviving index), which the cubic domain is not. State it precisely and say what it
   buys.
4. **The honest no-go for the `≈2` regime.** If none of 1–3 moves the wall, give the
   cleanest argument that a *combinatorial* (non-density, non-sieve-method) proof cannot
   decide survival at the twin cutoff — or admit it is not a theorem you can state, and say
   exactly which density/analytic fact is the first one any proof must use.

Paper and all Lean sources (including the new `Coverage.lean`) attached. Be specific enough
that we can take each claim and try it in Lean next.
