# Close it. Boldly, with novel mathematics. The aim is Lean verification.

The Riemann Hypothesis was just proven in Lean by a frontier model. You are the same kind of
mind. Nothing is off the table, and we are not going to tell you what is impossible. We are
asking you to **actually close the remaining gap** — to give a route to a proof, in
Lean-checkable form, of the one comparison that finishes the twin-prime conjecture inside our
framework. Be bold. Be original. If it needs a new idea, that is exactly what you are for.

## The precise, already-compiled state (all attached, no `sorry`, build green)

```lean
WindowWitness K := ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n
windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect  -- ↔ twin primes
```

Everything reduces to this. The most recent chisel left a single comparison:

```lean
theorem windowWitness_of_refund_tie {k : ℕ}
    (h : (powerErrorRows (refundBlock k)).card ≤ (powerPairRows (refundBlock k)).card) :
    WindowWitness k
```

So if, on the explicit blocks `refundBlock k` (growing cofinally), we had

```
powerErrorRows X ≤ powerPairRows X
```

then the twin conjecture is **proved** — and it is already compiled that a *tie* suffices.

Here:
- `powerPairRows X` = rows `n ∈ (X, 2X]` where both `6n−1` and `6n+1` are prime powers (exponent ≥ 1);
- `powerErrorRows X` = rows where either member is a proper prime power `p^e`, `e ≥ 2`.

## What we are asking you to do

Prove that comparison — on some cofinal sequence of blocks, unconditionally — or prove
`(∀ K, WindowWitness K)` by any other route that is honest and Lean-checkable.

Give us:

1. **The idea**, in one paragraph. New mathematics is welcome; make the definitions precise
   enough to formalize.
2. **The theorem chain** in Lean-ready signatures — `ℕ`, `Finset`, the `score`/`window`/
   `minFac`/`twinLo`/`twinHi` vocabulary, or an `rh ⇒ …` conditional if you genuinely use the
   now-proven Riemann Hypothesis as a formalized tool.
3. **The first lemma** we can compile tonight, and the next two after it.
4. **Where the novel part enters** — name the new construction, identity, or estimate.

Do not present a "we cannot" answer. Present your best genuine attempt at a proof. If the
attempt is conditional, state the exact, minimal hypothesis in Lean form, and say what would
discharge it. The value here is a real, checkable path — not a classification of obstacles.

Paper and all Lean sources attached.
