# Question for frontier review (one call)

## What we are formalizing

CPNF ("Computational Prime Number Framework") is presented in:

Yong Xue, "A Computational Framework for Prime Numbers: A Case Study on How Reification and
Ontology Affect Prime Infinitude Arguments", 26 Dec 2025.

Core semantics. A finite blocker set B. A number n "survives" B when no p in B divides n.
The sieve is {n >= 2 : survives}. At each stage the process certifies the LEAST survivor and
adds it to B. That is the whole primitive. There is no predicate "is prime" inside the
framework; primes are whatever the process certifies. Non-termination ("no stage is the last")
is CPNF's honest replacement for "infinitely many primes" - proved elementarily: (max B + 1)! + 1
always survives.

We have this fully formalized in Lean 4 / Mathlib, including:

- sieve, step, advance; stage sequence by guarded recursion
- determinism, monotonicity, non-termination
- twin indices: index n <-> pair (6n-1, 6n+1); "admissible for B" = both members survive B
- certification window W(y) = floor((y^2 - 1)/6) for y = max B; window_bound: 6n+1 <= y^2
- window_mono; window_ge (y <= W(y) for y >= 7)
- killed_iff: a blocker kills a pair only by dividing one of the two members
- the twin process as a READOUT of the ordinary stages (blockers at stage k are stage k;
  search at stage k = admissible indices inside that stage's window; certified = least such)
- honest correction: admissibility flows BACKWARDS over stages (more blockers => fewer
  admissible indices). The paper's Lemma 9 "certified stays certified" only holds for the
  record of certification, not for admissibility itself.

## Three things Lean has already refuted in our own work

1. "a survivor stays a survivor after one stage" - false (9 survives {2}, not {2,3}).
2. "admissible implies 2 not in B" - false (survival is a negative condition).
3. "y^2 - 1 <= 6y" (window shorter than y) - false at y = 7 (48 > 42). We had assumed it while
   building a window-versus-blocker counting comparison. The true statement is the reverse.
4. Consequently, the claim "a window of length W needs at least W blockers, because each
   blocker has only two congruences" is FALSE: one blocker q kills about 2W/q indices, and
   {5} alone kills 3 of the 8 indices in the window at y = 7. This was in our Chase.lean header
   and is now removed.

## The open part we are asking about

The paper's Section 4 and Appendix D argue that "permanent stagnation" (a stage after which no
twin index is ever certified) cannot occur. The argument as written uses:

- R_0 = admissible residue set modulo M_0 = prod of B_{k0}
- Lemma 11: a new prime q eliminates at most 2*M_0/q classes mod M_0 (CRT lifting)
- Lemma 12: |R^k_M| >= C * M_k / (log y_k)^2, via Mertens' third theorem
- Theorem 13: stagnation implies a finite covering of R_0 by finitely many primes' classes
- Lemma D.2 (Appendix D.2, "Necessary Condition for Covering"): a bound ruling out such coverings

So the paper explicitly does NOT rely on uniform distribution or density heuristics; it says it
uses "only growth rates and periodicity". But in practice it leans on Mertens' theorem, which is
an analytic input, and on a finite covering/covering-system argument.

## What we actually want to know

We are deliberately avoiding the density-based / parity-obstructed route. The parity problem is
exactly why we are interested in this framing: in a stage-relative process semantics there is no
"number of prime factors" to be even or odd, so the standard obstruction should not apply in the
same form. Our question is whether that intuition can be made into an actual proof, and what it
would cost.

Please answer these, concretely and with proof sketches where you can:

1. Is there a density-free, Mertens-free argument that excludes permanent stagnation in CPNF,
   using only: the deterministic least-survivor rule, monotonicity, and finiteness of the window
   at each stage? If yes, sketch it and name the key lemma. If no, say precisely what extra
   input is unavoidable and why.

2. The paper's determinism claim ("blockers are generated without foresight, excluding
   adversarial alignments") is a PRINCIPLE, not a theorem. Is there any precise statement of it
   that is both true and strong enough to rule out a covering? For instance: could a
   least-survivor process in fact be forced into a covering configuration, or can we prove it
   cannot because of how the least survivor relates to the largest blocker?

3. Is there a correct density-free replacement for the false "W blockers for a window of length
   W" counting? Specifically, is there an exact statement about how many indices in the window
   survive a given finite blocker set, one that is true and provable in Lean without analysis?

4. If the parity problem is genuinely bypassed by this framing, where exactly does the bypass
   happen - at which lemma does the classical obstruction fail to apply, and what replaces it?

5. What parts of the paper's Section 4 argument should be reframed, and in what order, to make
   an honest formalization possible? Be blunt about which pieces should simply be dropped.

## Constraints on the answer

- We will formalize whatever you propose, in Lean, so prefer statements that are elementary and
  combinatorial over ones that need analysis (logs, Mertens, asymptotics).
- No appeals to unproved conjectures. If a step would need one, say so explicitly.
- If the honest conclusion is "this framing does not prove twin-primality, it only reframes it",
  say that plainly. That is a useful result for us, not a failure.
