# Frontier call: attacking cofinal window nonemptiness

You reviewed this project once before and left us with a clean picture. We
accepted all of it. Now we want to *work*, not review: your previous answer
isolated the open proposition. Help us attack it.

## What is already formalized and building (Lean 4 + Mathlib, no `sorry`)

- `stage k` — the CPNF process: blocker set `B`, `sieve B n` (survivors),
  `Step B n` = least survivor, `advance B c = insert c B`. Nonempty sieve always
  (`factorial + 1` is coprime to every blocker), so no stage is terminal
  (proved: `always_a_next_step`).
- Twin readout, a *readout* of those stages, not a second recursion:
  `twinLo n = 6n-1`, `twinHi n = 6n+1`, `Admissible B n` (neither `twinLo n` nor
  `twinHi n` is divisible by any blocker), `window y = (y^2-1)/6`,
  `twinSieve B y = {n | Admissible B n ∧ n ≤ window y}`,
  `TwinCertifiedAtt k n = IsLeast (twinSieve (stage k) (maxBlocker k)) n`.
- Proved: `certifiedAt_admissible`, `certifiedAt_in_window`,
  `certifiedAt_least`, `window_ge (7 ≤ y → y ≤ window y)`.
- Three lemmas we formerly had were **false** and are now deleted and documented
  in `README.md` with counterexamples. Lean refused them and was right:
  `survives_advance`, `admissible_not_two`, and the bound `y^2-1 ≤ 6y`.
- We also refuted our own earlier claim "a window of length W needs ≥ W
  blockers": `{5}` alone kills 3 of the 8 indices at `y = 7`.

Our gates deliberately contain **no `Nat.Prime`**. Non-termination in CPNF means
"no stage is the last", not "there are infinitely many primes". Any `Nat.Prime`
appears only in a separately-labelled correspondence/bridge layer.

## Where your last answer left us

You proposed a bridge theorem (canonical-prefix invariant + window exactness +
Bertrand for the converse), and identified **cofinal window nonemptiness**

    ∀ K ∃ k ≥ K,  A_k ≠ ∅      (A_k = admissible n in [1, W(y_k)])

as the missing statement, plus the deflation that inside the window the negative
divisibility test *is* an exact primality test. We agree with all of it.

## What we want from this call

We are not looking for a review. We want the strongest honest progress.

1. **Sharpen the gap.** Is cofinal window nonemptiness (a) strictly weaker than
   unbounded twin primes, (b) equivalent to it, or (c) *a priori* stronger?
   Settle this if it can be settled. If it is equivalent, say so plainly and we
   will stop pretending the framing is a bypass.

2. **The exact count you gave us.** `Σ_{S⊆P} (−1)^|S| Σ_{r∈T_S} ⌊(W+d_S−r)/d_S⌋`
   with `|T_S| = 2^|S|`. Give the precise definition of `T_S` and `d_S`, and the
   smallest fully-written statement that we can formalize in `ℕ` today without
   any analytic input. We want the *statement* to be exactly right, not
   approximately right, since Lean will not forgive a sloppy one.

3. **A constructive attack on cofinal nonemptiness.** Is there any honest route
   that does not smuggle in analytic input? Specifically:
   - Can the canonical trajectory's *own* history be used — e.g. persistent
     records of prior certificates — to force a fresh witness cofinally often,
     rather than proving directly that windows stay nonempty?
   - Or does every such attempt collapse into a restatement of twin primes?
   If so, give the cleanest formal implication and we will formalize it as the
   honest headline: "no known route, and here is the exact oracle strength".

4. **One concrete next Lean lemma.** The single smallest true statement that
   moves us closest to (1). Fully quantified, with hypotheses. We will prove it.

## Constraints

- Constructive and finite. No Mertens, no covering systems, no density
  arguments, no `Nat.Prime` in the gates.
- We would rather have a short true answer than an ambitious unclear one.
- Be explicit about which steps are unconditional and which are conditional.

## What we will do with the answer

Formalize (2) and (4) in Lean in the existing repo, and record (1) and (3) in
`PLAN.md` as the frontier's standing verdict on where the framing stops.
