# RH is now proven in Lean. Be bold: use it (or something novel) to attack the boxed condition — and say the hard truth.

## What just happened (verified news, Nov 2026)

The Riemann Hypothesis has been proven and machine-checked. Levent Alpöge released a 17M-line
Lean proof on Nov 20, 2026; the Lean FRO and Mathlib Initiative certified statement + proof,
and independent mathematicians (Sutherland, Buzzard's comparator run) confirmed it. Mathlib's
`RiemannHypothesis` proposition is now backed by a compiling proof.

Sources:
- https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- https://www.scientificamerican.com/article/the-ai-riemann-hypothesis-proof-is-almost-certainly-true-independent-mathematicians-attest/

## The honest constraint you must respect

RH does **not** imply twin primes, and GRH does not either. RH controls first-order error in
prime counting; the twin conjecture needs second-moment / simultaneous-primality control, which
is Elliott–Halberstam territory, not RH. Do not fake a deduction RH ⇒ twins — it is not there.
Also, in *our* Lean project we cannot literally import the 17M-line library; relying on RH is
an `axiom rh : RiemannHypothesis` (a hypothesis, an externally-proven one, not a `sorry`).

## Our target (unchanged, already compiled — all attached)

```lean
WindowWitness K := ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n
windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect
```

`score n = min((6n−1).minFac, (6n+1).minFac)`, `window h = (h²−1)/6`. The boxed condition is
equivalent to twin primes. We have four compiled rungs (`Charge`, `Wheel`, `Progression`,
`PerPrime`, `TopBand`, `Ladder`): the whole unconditional finite ladder is machine-checked, and
the one remaining step is feeding `210U ≤ 192L + 60480k` a real distribution input.

## Bite the bullet — be bold, and pick ONE of these (or a better one you invent)

1. **Use RH (or GRH) as a tool.** Give the sharpest conditional theorem of the form
   `RH ⇒ (something new toward the boxed condition)` that is (a) true or plausibly true, and
   (b) Lean-checkable in *finite* form. Be explicit about what RH actually supplies — an
   explicit error term, a level of distribution, a bound on a character sum — and where it
   enters the sieve. If RH is genuinely too weak, say so in one line and move on.

2. **The minimal added hypothesis.** If RH/GRH is insufficient, name the exact extra
   hypothesis (Elliott–Halberstam? a specific level of distribution `ϑ`? a `k`-tuple
   density?) that, *together with RH*, would prove the boxed condition, and state that
   conditional theorem in Lean-ready form.

3. **A novel non-density route.** Our whole program is that the boxed condition is *not* a
   density statement — it is a "for every `K`, there is a witness" statement. Given RH is now
   available as a formalized fact, is there a route to cofinal witnesses that uses RH's
   *equidistribution* directly (zeros, characters, `ψ` estimates) without going through
   density? Be creative and concrete.

4. **The wall, named.** If none of 1–3 yields a Lean-checkable step, say so, and give the
   sharpest *true* statement that RH provably gives toward the boxed condition — something we
   can compile as `rh ⇒ φ` with `φ` a finite arithmetic claim, even if weak.

## Requirements

- Every theorem: `ℕ`, `Finset`, the `score`/`window`/`minFac` vocabulary, or a clean `rh ⇒`
  conditional. No asymptotics, no `sorry`-shaped content.
- For the chosen route: the exact Lean signature, the proof idea in one paragraph, and which
  compiled lemma it builds on.
- Name the model of the wall: is the residual step *still* Elliott–Halberstam, or does your
  route genuinely avoid it?

Paper and all Lean sources attached. Be bold, but tell us the hard truth.
