# Be bold and brave: chisel the last part, for Lean verification only. No assumed walls.

The Riemann Hypothesis has been **proven in Lean** (Nov 2026, certified by the Lean FRO +
Mathlib Initiative). That fact alone says we should not assume anything is impossible. We do
not want you to name a wall, classify a moment, or argue that a barrier exists. We want you
to **produce Lean-checkable lemmas** that make genuine progress on the one remaining gap,
however small, and to be bold about it.

## What is already compiled (all attached, `import Mathlib`, no `sorry`, build green)

The twin-prime conjecture is *exactly equivalent* to a single condition, already proved in
Lean (`windowWitness_iff_oftenDirect`):

```lean
WindowWitness K := ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n
-- (∀ K, WindowWitness K) ↔ OftenDirect ↔ unbounded twin primes
```

`score n = min((6n−1).minFac, (6n+1).minFac)`, `window h = (h²−1)/6`.

We have four unconditional finite rungs compiled (`Charge`, `Wheel`, `Progression`,
`PerPrime`, `TopBand`, `Ladder`), and one clean conditional compiled (`PowerExcess.lean`):

```lean
windowWitness_of_power_excess :
  (powerErrorRows X).card < (powerPairRows X).card → WindowWitness K
```

where `powerPairRows` = rows whose two members are both prime powers, and
`powerErrorRows` = rows where either member is a *proper* prime power.

## What is left

Exactly one input is missing to finish: we need a way to know, on blocks arbitrarily far
out, that the *signal* rows outnumber the *budget* rows (or anything that implies
`WindowWitness K`). We are **not** assuming this is hard, and we are **not** assuming RH is
or is not enough. RH being done in Lean means a previously-impossible-looking tool is now on
the table.

## What we want from you

Be brave. Give us **concrete, Lean-compilable** theorems that chip at that single remaining
input. For each:

- the **exact Lean signature** (over `ℕ` and `Finset`, in the `score`/`window`/`minFac`/
  `twinLo`/`twinHi` vocabulary, or a clean `rh ⇒ φ` conditional if that is the honest route);
- the **proof idea** in one paragraph;
- **which compiled lemma it builds on**;
- whether it is unconditional or conditional (and on what).

Do not stop to tell us what is impossible. If you can hand us a true, finite, Lean-provable
lemma that makes the signal strictly bigger or the budget strictly smaller on some explicit
infinite sequence of blocks, give it. If RH or GRH can be leveraged *as a formalized fact*,
say exactly how, in Lean terms. Aim for at least one lemma we can compile tonight, and one
more we can attempt after it.

Paper and all Lean sources attached.
