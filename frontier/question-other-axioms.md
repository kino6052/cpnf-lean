# Other non-classical axioms: natural to the process ontology, not a shifted copy

The `X`/shift answer was sound and honest, but it cheats in a specific way: it *changes
what a number is* (adds a second constructor, so the "twins" live in new columns and are
not the twins the process was ever chasing). We want alternatives. Give several, ranked by
how *natural* they are to the ontology the paper actually describes — and be ruthless about
whether each one decides the real statement or merely relabels it.

## The ontology the axiom must fit (verbatim, from the paper's program)

- **Numbers are outputs of a computational process.** A number *is* a certified stage of a
  generator. There is no completed `ℕ`; there is the generator and its trace.
- **Primes are survivors of the sieve.** A newborn is prime iff no earlier survivor divides
  it. This is the *actual* sieve, on the *actual* generated numbers — not a copy.
- **Infinity is a recognizable recursive loop, by identity of a step.** "Forever" means the
  step function returns a state of the same recognizable kind; forever is licensed by
  step-repetition, not by counting.
- **The twin statement to decide** is: the actual sieve, on the actual generated numbers,
  never reaches a stage after which no twin pair `6n−1, 6n+1` is ever certified.

## What we are rejecting (state if you disagree)

- Adding a second constructor / a second number system (the `X` move): the twins must be
  twins of the *numbers the process actually generates*, not of a shifted copy.
- Redefining "twin" or "infinite" so the statement becomes trivially true.
- Any axiom that is simply "there are infinitely many twin pairs" in disguise.

## What to deliver

1. **Three to five candidate axioms or principles**, each one line of "what it says", ranked
   by common-sense fit to the ontology. Prefer principles that a process thinker already
   believes: fairness, bar induction, constructive choice, a productivity/coinduction
   principle, a "recognition closes the loop" pigeonhole principle, a monotone-fixpoint
   principle, a potential-infinity reflection principle, a "no dead ends" progress
   principle — anything in that family.
2. For **each** candidate: does it (a) decide the *actual* survivor-twin statement, (b)
   change the generator, or (c) change the meaning of "twin"/"infinite"? Be honest; mark
   (a)/(b)/(c) explicitly. If it is (b) or (c), it is a cheat in our sense — say so.
3. If **no** sound, natural axiom can be of type (a), give the argument for *that* — a
   meta-mathematical statement that the process ontology, short of changing the generator
   or the meaning, does not decide the twin statement. A clean negative result is a real
   deliverable, not a failure.
4. The one candidate you would actually build, with its first theorem in its own notation.

Constraints: sound (no contradiction), non-trivial (not true by definition), and the honest
ledger for whatever you recommend. Paper and all Lean sources attached.
