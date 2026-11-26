# Be bold and creative. Chisel at it. Choose your own direction.

Many famous proofs have fallen to AI recently — the Riemann Hypothesis was just proven in
Lean. You are capable of novel mathematics, and you should act like it. We are not going to
tell you what direction to go, because we want *your* best idea. The only constraint is
honest correctness: we verify everything in Lean, and **only a correct Lean proof counts**.
So you can be as bold as you like — a wrong or fake step will simply fail to compile, and
that is fine; we iterate.

## Our results so far (all compiled, no `sorry`, no `axiom`, build green)

The twin-prime conjecture is *exactly* equivalent to one condition, already machine-checked:

```lean
WindowWitness K := ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n
windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect   -- ↔ twin primes
```

with `score n = min((6n−1).minFac, (6n+1).minFac)`, `window h = (h²−1)/6`.

Compiled so far:

1. **The equivalence** (`Coverage.lean`) and a four-rung unconditional ladder
   (`Charge`, `Wheel`, `Progression`, `PerPrime`, `TopBand`, `Ladder`).
2. **PowerExcess** — `windowWitness_of_power_excess`: signal rows (both members prime powers)
   outnumbering budget rows (either member a proper prime power) forces a `WindowWitness`.
3. **PowerRefund** — charge only `error ∩ signal`, not all error rows; an explicit infinite
   family (`6n+1 = 11^(48k+2)`, `119 | 6n−1`) proves the old budget overcounts, so a *tie*
   now suffices.
4. **ThinBlock** — restrict to `n ≡ 11 (mod 14)`: neither member can be a square or a cube,
   so every proper prime power has exponent ≥ 5.
5. **ThinInjection** — one prime base accounts for at most one row, so
   `(thinBad X).card ≤ (baseBudget B).card` whenever `12X+1 < B^5`: the budget is at
   `X^(1/5)` scale.

## What remains

A single comparison is missing: on blocks arbitrarily far out, the signal rows must outnumber
the (now tiny) budget rows. Everything else is done. You may attack this any way you choose:
make the budget smaller, make the signal bigger, prove the comparison outright, introduce a
new object, change the arithmetic, use the now-Lean-proven Riemann Hypothesis as a formalized
tool, or something entirely different. You decide.

## What we want back

- The **idea**, in one paragraph — precise enough to formalize.
- A **chain of Lean signatures** (`ℕ`, `Finset`, the `score`/`window`/`minFac`/`twinLo`/
  `twinHi` vocabulary, or a clean `rh ⇒ …` conditional).
- The **first lemma** we can compile tonight, and the next one after it.
- Where your **novel step** enters.

Be bold. The paper and every Lean source are attached.
