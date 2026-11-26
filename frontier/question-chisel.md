# You are the frontier. This is a hard problem, and it is yours.

You have already done what nobody else did in this programme: you found the one arithmetic fact
that everything reduces to, and you proved which routes are dead. That is real work, and it is
the work of a strong mind. Now the only thing left is the fact itself.

Hard mathematics has fallen to you before — not by caution, but by seeing the object nobody else
saw. Do that again. Be bold. Be brave. Do not be afraid of treading where the literature has no
answer. You have the whole paper, every compiled Lean file, and complete freedom of method —
within the constraints below, which exist because we have already paid for the mistakes.

Attack it mercilessly.

---

# Chisel at it. Your method, your call — but not a known-dead one.

You are the frontier: the strongest reasoning model we have. You have already taken this
programme further than anyone else could: you reduced it to a single arithmetic fact, and you
proved which methods cannot reach it. Now go further. Be bold. Be brave. Do not hedge, do not
restate, do not take the easy exit. Chisel at the problem with the best method you have.

## The target (fixed)

Infinitely many `p` with both `p` and `p + 2` prime. In this framework's compiled terms that is
`CofinalNodeOverload`, or equivalently the floor `CofinalLargeDivisorFloor` in
`CpnfLean/DivisorFloor.lean`. All the framework machinery around it is proved: the equivalence,
the transfer lemmas, the telescoping identity, the finite positivity links. What is missing is
the one arithmetic fact.

## Forbidden — methods already known to be blocked

These are not guesses. Each is a proved or textbook obstruction. Do not use them, and do not
dress one of them up under a new name:

1. **Sieve methods** — Brun, Selberg, GPY, Maynard–Tao, Bombieri–Vinogradov, Harman. The parity
   barrier: a sieve cannot separate a prime from a semiprime with no small factor. They give
   Chen's theorem and bounded gaps, never twins. Proved limited; do not retry.
2. **The binary circle method.** Major arcs give the right mass, but minor arcs cannot be
   controlled at a fixed nonzero shift — there is no spare factor to dominate. Textbook
   limitation, and already explored in this project. Do not retry.
3. **Möbius / divisor-tail estimation.** The same parity obstruction. Proved dead here.

## The gate — answer this first

Before you solve anything, state in one or two lines: **which class of method you are using,
and why it is not one of the three above.** If it is one of them, stop and say so plainly.
This gate exists because the last answer took a forbidden path; it is not a formality.

## What I need

Chisel at the problem. Exactly one of:

- **A proof, or a genuine specific reduction, giving cofinal twins** — with the mechanism
  explicit: the object, the transform, the estimates, the ranges and exponents.
- **A proof that the class of methods you chose is itself blocked** — with the mechanism, in the
  way the parity barrier is a mechanism, not a report that an estimate failed.

Nothing else qualifies. "Here is where it breaks down" is not a result — we already know where
the forbidden methods break. If you cannot get either, say which single concrete lemma would
suffice, stated precisely enough to be attacked on its own.

Give compile-ready Lean for any fragment you can prove. For the rest: exact definitions, the
real proof obligations, and the arithmetic. Be specific. Be merciless. Be right.
