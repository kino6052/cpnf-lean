# Frontier call: attack cofinal nonemptiness — a Lean-formalizable proof

This is an attack, not a review. The owner's posture, which we adopt: treat this
as solvable, prove it in Lean 4, and if the proof later turns out to have a flaw,
that is acceptable — the gate is Lean, not human consensus. We want you to
actually attempt the proof, or hand us the strongest sub-result plus the exact
one-line residual that closes it.

## The target

Prove, density-free and constructively:

    OftenSearch := ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ (searchSet k).Nonempty

where (see sources) `searchSet k = twinSieve (stage k) (maxBlocker k)`,
`twinSieve B y = { n | Admissible B n ∧ n ≤ window y }`, `window y = (y² - 1) / 6`,
`Admissible B n` = neither `6n-1` nor `6n+1` divisible by any blocker in `B`.

## What is already settled (in the repo, and agreed with you in earlier calls)

- The ordinary process never terminates: `always_a_next_step`.
- **Cofinal nonemptiness is equivalent to unbounded twin primes.** So this target
  *is* the twin prime conjecture in CPNF form. We are not pretending otherwise.
- Window exactness: for `1 ≤ n ≤ window y` on the canonical run, `Admissible`
  means `6n-1` and `6n+1` are both prime and `> y`.

## The known obstruction (we are aware — do not re-explain it to us)

The parity problem: a pure sieve cannot certify "both are prime", only "few prime
factors". We are looking for a route that does not need a density/parity-splitting
argument — or that turns the obstruction into a *separately stated lemma* we can
then try to prove or refute in Lean.

## What we want

1. A concrete proof strategy for `OftenSearch`, as a sequence of Lean lemmas
   (names, hypotheses, conclusions) we can attempt one at a time.
2. If a full route is not available: the strongest **unconditional** statement you
   believe is provable, plus the exact residual claim that would close it. Make
   the residual as weak and precisely stated as possible.
3. Explicitly flag every step that would need analytic / sieve-method input. Do
   not hide it; state it as a separate conditional lemma.
4. Flag immediately if the target, or any step you propose, is actually **false**.
   We have already caught four false lemmas this way; a clean false result is
   valuable and we want it fast.

## Constraints

- Constructive-first, finite, `ℕ`-first. No Mertens, no covering systems, no
  analytic densities unless you flag them explicitly as a separate conditional.
- We will formalize whatever you give, so exact quantification matters more than
  intuition.
- Short and correct over ambitious and vague.
