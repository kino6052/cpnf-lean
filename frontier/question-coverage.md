# Attack the real conjecture through a coverage argument, not parity

We are attacking the twin prime conjecture itself. Not a relabeling, not a non-classical
framework. The one route we have not tried: **prove that no covering system can sustain the
endless chase**, or prove that one can. Parity is not the tool. Coverage is.

## The precise statement, in CPNF terms (this is what must be decided)

The paper's twin process is: the ordinary sieve enumerates primes; at stage `k` a twin index
`n` is *admissible* if neither `6n−1` nor `6n+1` is divisible by any certified prime; the
*head* `h_k` is the least admissible index; `Dies k` means `h_k < h_{k+1}`; `Direct k` means
the killing divisor `certify k` **is itself** a member (`= 6h_k ∓ 1`), not a proper factor.
Twins ⟺ `Direct` occurs unboundedly.

**The endless chase** = `Dies` occurs forever but `Direct` only finitely often. So the twin
conjecture is exactly: *the endless chase is impossible*.

## What "coverage" means here — and why it might beat parity

`Dies` is provably productive (we have `next_death`: every stage eventually dies, with a
bounded receipt). The open fact is that the killer is a **factor**, never a **member**.

A "chase" would be an infinite supply of deaths whose killers are all proper factors. Such
a set of killers `q₁, q₂, …` must, for each head, hit `6h±1` with `q < 6h−1`. That is a
**covering of the admissible residues by proper-factor primes** — a covering-system problem,
not a parity problem. We want either:

- **(A) a proof that no such covering can arise from the sieve's own order** (killers are
  forced to be members infinitely often), or
- **(B) a construction of a covering** (which would show the chase is possible in *some*
  process — and would tell us exactly which property of the CPNF order rules it out).

**Guardrail:** the paper's §4.4 asserts (A) by "construction excludes adversarial coverings".
That is unproven. Distinguish two targets: (A) for **CPNF's deterministic order**, and (A′)
for **any covering system whatsoever** (which is false — coverings exist: `{2,3,5,…}` cover
integers; the question is whether one covers `{6n±1}` with all moduli *proper* relative to
the heads). Say which one you are doing.

## What we already have (attached, compiles)

Exact CPNF: `certify k` prime, stage `k` = primes below; `score n = min(minFac(6n−1),
minFac(6n+1))`; twin ⟺ `score n = 6n−1`; residual ⟺ unbounded twins; `Dies` productive with
bounded receipt; `dies_iff` (death ⟺ the new prime divides a head member). Also:
`score` unbounded via `6D = x³`. And a proved failure of the paper's fixed-modulus reduction
(the new hit bit is not a function of the old residue label).

## Deliver

1. **The coverage statement made exact** — the precise combinatorial object a chase is
   equivalent to. Ideally: chase ⟺ existence of a sequence of primes covering every head
   with moduli smaller than the head, subject to the sieve's order constraints.
2. **The strongest obstruction you can actually prove** — any theorem that narrows the
   space of chases, even if it does not close it. A partial covering bound is a real result.
3. **The point where the standard tools fail** — and whether it is the same wall as parity,
   or a genuinely different wall.
4. **If you believe (A) is provable by this route, sketch the proof**; if you believe it is
   not, say what the obstruction is.

Honest ledger required: what would still be open after your best argument. Do not sell a
covering bound as a proof of the conjecture.
