# Bold, but unconditional, and Lean-compiled: build the ladder to the wall

The criterion has changed, and it is the whole point: **we only aim for Lean-compiled
code.** That means every theorem must be first-order finite arithmetic over `Finset`, in
the `score`/`window`/`minFac`/`twinLo`/`twinHi` vocabulary — no analytic estimates, no
sieve-method asymptotics, no Siegel zero, no GRH. A conditional on an exceptional zero is
out of scope: it is not a Lean theorem we can compile, and it is Heath-Brown's known
result anyway.

So be bold in a different direction: **how far can unconditional, Lean-checkable
mathematics take us toward the boxed condition, and what exactly is the last finite
theorem before the analytic wall?**

## The boxed condition (already proved equivalent to twins, attached)

```lean
WindowWitness K := ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n
windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect
```

## What we can already compile (attached, no `sorry`)

- `score_unbounded`: at `n = (h+1)!`, every `d ≤ h` divides `6n`, so `score n > h`.
- `windowWitness_iff_oftenDirect` and the two halves.
- The full CPNF↔primes correspondence and the tail-cover square-truncation.

## The ladder we want you to specify — each rung unconditional and Lean-able

1. **`chen_charge_exact`** (you specified it): the exact integer identity splitting a
   character-selected set of almost-prime rows into passing rows plus a disjoint sum over
   `+1`-character prime factors `q ≤ H/(z+1)`. This is unconditional and finite. State it
   again precisely, with the exact hypotheses and the Lean-ready proof idea, so we can
   compile it next.

2. **The elementary top-band exclusion** (you sketched it): on `(X, 2X]`, the primes in
   `(√X, √(12X+1)]` hit at most `19/20` of indices. Note its key feature for us: the
   "at most 48 primes per dyadic interval" is really a bound on *integers* coprime to 210,
   not on primes — so it is `φ(210)` CRT counting, fully Lean-able. Spell out the exact
   finite statement with the constants, in Lean-ready form.

3. **A finite pigeonhole/CRT theorem that reaches for the boxed condition**: the sharpest
   statement of the form "if no window witness beyond `K`, then [some finite combinatorial
   impossibility]" that is *still* provable. Do not hide an analytic fact inside it.

4. **The last finite theorem before the wall**: name the *first* statement in the ladder
   that genuinely requires a prime-distribution or sieve estimate, and prove (or argue)
   that nothing weaker suffices. Be honest: if rungs 1–2 are the end of the unconditional
   line, say so plainly, and make them as strong as they can be.

## Rules

- Every theorem: unconditional, no `sorry`-shaped assumptions, and Lean-compilable.
- For each rung: the statement, the proof idea in one paragraph, and which existing Lean
  lemma it builds on.
- Rank the rungs by "how much of the gap to the boxed condition it closes".
- If a rung secretly needs an analytic estimate, flag it as the wall, not as a deliverable.

Paper and all Lean sources attached. Give us the ladder we can start compiling tonight.
