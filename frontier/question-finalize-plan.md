# Give us a plan to finalize it. Be bold and own the whole remaining problem.

You have been chiseling brilliantly, and we want you to now **plan the finish**. Recent
proofs have fallen to AI precisely because the model stopped estimating and started building
something checkable — and we verify everything in Lean, so you can be as bold as you like;
only a correct Lean proof counts. We believe you have what it takes.

## Honest state (all compiled, no `sorry`, build green, pushed to GitHub)

The twin-prime conjecture is exactly equivalent to one condition, machine-checked:
`(∀ K, WindowWitness K) ↔ OftenDirect ↔ twins`. We have reduced the whole thing to a single
comparison, and chiseled it down:

- `√X → X^(1/5) → X^(1/7)` budget scale (PowerExcess → ThinInjection → SeventhMask);
- a tie now suffices (PowerRefund);
- the budget is now near-optimal: 299 of 341 candidate classes survive, so further
  exponent-shrinking pays less and less.

Our own analysis: shrinking the budget forever is a dead end. It cannot prove the theorem,
because the *signal* (rows where both `6n±1` are prime powers) is still unconstrained — and
a smaller budget only lowers the right-hand side of `signal > budget`. Even a zero budget
would not close it.

## What we are asking

A **plan from here to a finished proof** — the roadmap, in phases, each phase a
Lean-compilable deliverable. Do not just hand us "the wall"; hand us the path. Be concrete:

1. The **one novel idea** at the core of the plan (new object, new identity, new count —
   your choice; you may use the now-Lean-proven Riemann Hypothesis as a formalized tool).
2. **Phases**: each one, what it proves (a Lean signature), what it builds on, and what it
   unblocks. Mark which are unconditional and which are conditional (and on what).
3. The **first lemma** we can compile tonight, in exact Lean form over `ℕ`/`Finset` in the
   `score`/`window`/`minFac`/`twinLo`/`twinHi` vocabulary.
4. Where the **final step** is, and why the plan reaches it (not just points at it).

Be ambitious but honest: a plan that ends in `rh ⇒ …` or `(named hypothesis) ⇒ …` is fine if
that is the truth — say so and make the hypothesis exact. A plan that ends in an unconditional
proof is better. Tell us which one you are committing to, and take the first step now.

Paper and every Lean source attached.
