# Design new mathematics from the paper's ontology, so that non-stagnation is provable

The paper (full text attached below as `paper.txt`, by Yong Xue) proposes the Computational
Prime Number Framework (CPNF): primes are not pre-existing objects but *survivors of a
certification process*; infinity is treated as a *process*, not a completed set. Its central
claim is that the twin-certification process **cannot enter permanent stagnation**. We have
machine-checked the framework in Lean (sources attached). Here is what we now need from
you, asked with full creative license.

## What we have established in Lean (do not re-derive this)

- CPNF is exactly prime enumeration: `certify k` is always prime, and stage `k` is the
  primes below it.
- `score n = min(minFac(6n-1), minFac(6n+1))`; a twin index is `score n = 6n-1`.
- **Non-stagnation is equivalent to twin primes.** We proved
  `OftenDirect ↔ unbounded twins`, and
  `CofinalScoreEnergy ↔ cofinal passing rows ↔ twins`.
  So the paper's "cannot stagnate", read as "a twin certification recurs beyond every
  bound", *is* the twin prime conjecture. This is settled; do not relitigate it.

## The honest trap we keep hitting, stated once

Every target we form that is strong enough to imply twins turns out to be *equivalent* to
twins. Every reduction lands on Dickson/Hardy–Littlewood or the covering problem. The
paper's §4.4 ("no finite set of subsequent primes covers all admissible residues") is
exactly the unproven step: it asserts, by "construction excludes adversarial coverings",
precisely what needs proving. We are not asking you to repeat this.

## The actual task: design the mathematics the paper gestures at, but never builds

Take the paper's epistemology seriously as a *foundation to be built*, not a slogan:

1. **Numbers and primes are outputs of a computational process.** There is no completed
   `ℕ`; there is a generator, and a number *is* a stage at which it is certified.
2. **Infinity is a recognizable recursive loop, by identity of a step.** "The process runs
   forever" is not a `∀K ∃n` statement; it is the claim that the step function, applied to
   any state, returns a state of the *same recognizable kind* — so the loop is infinite
   because it is self-referential, not because it is counted.
3. **Twin conjecture = the twin process never stagnates.** "Never stagnates" must mean
   something *provable in the loop vocabulary* — not `cofinally many direct deaths`, but a
   step-level property the loop demonstrably has.

Design, concretely:

- **(a) The logic.** What is the proof notion in which "infinity = recursive loop by step
  identity" is primitive? Name it or construct it: is it guarded corecursion / coinduction,
  a modal or fixed-point logic, a type theory where "productivity" is the only notion of
  infinity, or something genuinely new? Give the judgment forms and the rule that
  certifies "this loop never gets stuck".
- **(b) The conceptual tools.** Define, precisely, in this logic: *survivor*, *loop
  identity*, *non-stagnation*, and the exact step function of the twin process. Show what
  "adversarial covering" becomes — and whether it is excluded *by the logic* or only by an
  assumption (if the latter, say so plainly).
- **(c) The checker.** Which software actually checks this logic — existing (Agda, Cedille,
  cubical type theory, a coinductive fragment of Lean, Coq's `coinductive`), or a new
  kernel you specify? We need something we can run. If none exists, say the minimum we
  would have to build.
- **(d) The first theorem.** State the *first* non-trivial thing this framework proves, in
  its own notation, with the one-line proof idea — and show how it is *not* just "assume
  twins".

## Non-negotiable constraints

- The proof obligation must be real: the framework cannot make twins true by *defining*
  them true. If your design's "non-stagnation" is provable trivially, say what *else* it
  proves that classical math could not, or admit the design is only a relabeling.
- Soundness: no contradiction. If the logic makes "the loop never gets stuck" provable and
  also makes classical twin primes false, that is a feature to *name*, not hide.
- Concrete and runnable: we want a path to a checked proof, not a manifesto.

Be bold and precise. Give us (a)-(d), with the first theorem written out.
