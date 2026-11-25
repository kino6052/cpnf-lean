# Design a non-classical mathematics in which the twin statement is DECIDED

The paper (full text attached, `paper.txt`, Yong Xue) argues that reification — treating
processes as completed objects — creates artificial obstacles, and that a process ontology
dissolves them. **Take that seriously as a mathematical programme, not a metaphor.**

## The task, stated exactly

Design a mathematical framework — a logic, its primitives, and its semantics — with these
properties:

1. **It is NOT a conservative extension of classical mathematics.** It need not translate
   to classical statements, and you are not required (or expected) to imply classical twin
   primes. We are not proving the conjecture inside the ordinary frame; that is the point.
2. **In this framework, the twin statement is DECIDED** — either proved or disproved.
   State it precisely in the framework's own vocabulary, then decide it.
3. **Sound**, and **non-trivial**: the theorem must not be true by definition, and the
   framework must not be able to prove everything. Say explicitly which of your definitions
   does work and which could be accused of assuming the conclusion — and why it does not.
4. **Honest about the relationship.** State what the decided theorem does imply, if
   anything, about classical twin primes, and state plainly if the answer is "nothing".

## The three primitives the paper asks for

- **Numbers and primes are outputs of a process.** There is no completed `ℕ`; there is a
  generator, and a number *is* a certified stage. Primes are survivors, not objects.
- **Infinity is a recognizable recursive loop, by identity of a step.** Not `∀K ∃n`; the
  loop is infinite because the step function, applied to any state, returns a state of the
  same recognizable kind. Say exactly what "identity of a step" is — a bisimulation, a
  guarded type, a fixed point, a coalgebra — and why it licenses "forever".
- **Twin non-stagnation** is the statement to decide.

## What we already know (do not re-derive; use or discard)

Lean sources are attached and compile. We proved, in classical Lean:
`certify k` is prime and stage `k` is exactly the primes below it; `score n =
min(minFac(6n-1), minFac(6n+1))`; twin ⟺ `score n = 6n-1`; the CPNF residual is
*equivalent* to unbounded twins; and `score` is unbounded via the elementary witness
`6D = x³` with `x = 6(a+1)(h+1)!`, so `x³±1` factor but evade every divisor `≤ h`.

That last fact is the *classical* reach of the framework. Your job is to design the
non-classical mathematics that goes further, and to be explicit about where it departs.

## Deliverables

- **(a) The logic** — judgment forms, and the rule that licenses "runs forever".
- **(b) The primitives** — survivor, step-identity, loop, stagnation, defined precisely.
- **(c) The theorem** — the twin statement in the framework, with its proof or disproof.
- **(d) The model** — a semantics in which the framework is sound. If the model is
  non-standard (a Kripke model, a topos, a coalgebra, a realizability model), say which
  and why it is the right one for a process ontology.
- **(e) The checker** — what software runs it (existing or to be built, with the minimum
  kernel), so we can actually check the proof.
- **(f) The honest ledger** — one short table: what the framework proves, what it does not,
  and what in it would be *false* or *meaningless* classically.

Be bold. We would rather have a sharply-specified non-classical framework with one decided
theorem and an honest ledger, than a safe restatement. If the framework you design decides
the statement by making the negation unstatable, say so and defend it.
