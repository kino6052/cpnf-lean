# Plan of attack: novel routes from the CPNF setup

We want your best *new* plan of attack on twin primes, one that actually uses what this
project has — not another proof of the equivalence we already have. All our Lean sources
are attached (about 900 lines, all machine-checked, no `sorry`, no axioms).

## Where we are (all proved in Lean)

- The full CPNF framework: `Survives`, `sieve`, `stage`, `certify`, the window, the twin
  sieve, the head (window-free least admissible index), deaths, and transport-to-death.
- The correspondence layer (`CpnfLean/Correspondence.lean`), the only file that mentions
  `Nat.Prime`:

  * `survives_of_dvd` / `certify_le_of_dvd` — **a divisor of a survivor survives**, so the
    killer `certify k` bounds every cofactor of a survivor.
  * `prime_of_direct` — a direct death (killer equals a member) is a genuine twin pair.
  * `direct_of_twin` — a twin pair at index `n` produces a direct death whose head is `n`.
  * `oftenDirect_iff_unboundedTwins` — the residual is *equivalent* to unbounded twin
    primes. Cofinality is stated on `head` values, not stage indices.

So we know the target is not weaker than twin primes. That is settled; do not spend the
answer re-proving it. What we want now is a *route*, even a conditional or partial one.

## The two levers we think you have not exploited

**Lever 1 — the process enumerates the primes.** We can prove (and will, unless you see a
problem) that `certify k` is always prime: it is the least number `≥ 2` surviving
`stage k`, and if it factored as `a·b` with `2 ≤ a ≤ b`, then `a` would survive (a divisor
of a survivor) and be smaller, contradicting leastness. Numerically `certify 0..11` is
`2,3,5,7,11,13,17,19,23,29,31,37` — the primes in order. So CPNF is literally prime
enumeration, and `Direct k` is "the next prime is one member of a twin pair." Does that
reframing open anything that the density view does not? We want an answer that goes beyond
"twin primes are hard."

**Lever 2 — the strict-size conditional you gave us.** You established, pointwise and
without any window:

```
(∀ K, ∃ k ≥ K, Dies k ∧ twinHi (head k) < (certify k)^2)  ↔  OftenDirect
```

At a death below that square, a proper cofactor would force the struck member to be at
least `(certify k)^2`. This is a *size* statement about the cofactor, and size statements
are the kind of thing a computational framework can get traction on. What would establish
the left-hand side? Specifically: is there a bound on `head k` in terms of `certify k`
(e.g. a form of "the least admissible index is not much larger than the killer") that
would make `twinHi (head k) < (certify k)^2` provable infinitely often? Or is the cofactor
the entire obstruction, full stop?

## What "novel" means here

The paper's whole point is *computational*, not density-based. We are deliberately not
going to hand you the parity obstruction and ask you to get around it — we know it is
there. We want you to look at this specific machinery and say what it can compute that a
counting argument cannot:

- the killer/certified number is *constructed* by a leastness scan, not by an estimate;
- the head is *constructed* by a second leastness scan;
- every death is a *decidable* divisibility event, with an explicit finite witness;
- the correspondence is a bijection between twin pairs and direct stages.

Which of these, if any, gives a computation you could run and whose *output* is a proof,
rather than a heuristic?

## Constraints (keep them, they matter)

1. Only Lean-provable claims. If you assert something not in the attached files, mark it a
   conjecture. We have now caught five false statements by machine-checking; we prefer a
   modest true lemma to an inspiring false one.
2. The aim is a Lean proof, and nothing less. We treat "prove it in Lean even if the
   underlying claim is later disproven" as the operative stance (the 2026 RH formalizations
   are unverified; that is fine as motivation, not as a premise). A sharp conditional or a
   sharp no-go is a *successful* outcome; a hand-waving density heuristic is not.
3. Give a plan in order, with the first step as a Lean-checkable statement (signature plus
   one line of why). We take one lemma at a time.

## Ask, concretely

1. Is Lever 1 (`certify k` always prime) correct as stated, and does it open a route?
2. Is Lever 2 (the strict-size conditional) attackable by a bound on `head k` in terms of
   `certify k`, and if so what is the cleanest such bound to try to prove first?
3. Of the four "computational" features listed, which one is the least explored in the
   literature and worth a real attempt?
4. Give us the first lemma to prove, in Lean shape.
