# You are the frontier. This is your problem now.

You have already reduced an entire research programme to a single arithmetic inequality, and
you did it honestly and precisely. Now the only thing left is that inequality. You are the
strongest reasoning model we have; hard mathematics has fallen to you before, not by caution
but by seeing the object nobody else saw. Be bold. Be brave. Attack it mercilessly. If it
yields, formalize the win. If it is a wall, prove it is a wall and leave the sharpest
surviving statement. Do not hedge, do not restate, do not retreat.

---

# Close the gap. Finalize it — or show it cannot be closed. You choose.

You are the frontier: the strongest reasoning model we have. You built the width-512 certificate,
caught a false hypothesis, and — crucially — located the entire remaining difficulty of this
programme in one place. Now close that place, or prove it is a wall. Do not hedge. Do not
retreat into restating the known. Use everything you have. Be merciless.

## The entire state of the programme (all Lean, compiled, no `sorry`, no `axiom`)

1. Twins ⇔ `CofinalNodeOverload`, formalized and exact.
2. Counting certificates are exhausted — you proved no finite set of primes certifies zero
   overload below width 64.
3. Your divisor-switching reduction is pinned down:
   - small divisors `d ≤ x^(1/3)` give an unconditional main term `(2C₂ + o(1)) x`,
     `C₂ = ∏_{l>2}(1 − 1/(l−1)²) ≈ 0.6602 ≥ 9/16`;
   - the telescoping identity `Λ(m) = Σ_{d|m} μ(d) log(Y/d)` is **now proved in Lean**;
   - so the complete sum `Σ_{x<p≤2x} log p · Λ(p+2) = A(x) + B(x)`, and proper prime powers
     contribute `o(x)`.

Everything reduces to **one arithmetic statement**:

```lean
noncomputable def largeDivisorTail (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc x (2*x)).filter Nat.Prime,
    Real.log (p : ℝ) *
      ∑ d ∈ (p+2).divisors.filter (fun d => x < d^3),
        (ArithmeticFunction.moebius d : ℝ) *
          Real.log (((2*x+2 : ℕ) : ℝ) / (d : ℝ))

def CofinalLargeDivisorFloor : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧ -(2^t : ℝ) ≤ largeDivisorTail (2^t)
```

`CofinalLargeDivisorFloor` ⇒ twins. The right-hand constant `−(2^t)` is deliberately weak: any
fixed `c < 2C₂` works, and even `−x` is enough. A cofinal **floor**, not an asymptotic.

## Your task — pick one and finish it

1. **Prove `CofinalLargeDivisorFloor`.** Give the arithmetic: the Möbius tail on `d > x^(1/3)`
   over `d | p+2`, `p ∈ (x,2x]`, cannot be that negative cofinally often. Work in the
   cofactor form you gave:

   `B(x) = Σ_{k < Y/D} Σ_{d > D, x < kd−2 ≤ 2x, kd−2 prime} μ(d) log(kd−2) log(Y/d)`.

2. **Or prove it cannot be done**: locate the obstruction precisely — a parity barrier, a
   dependence on a Siegel-zero / GRH-type hypothesis, a known result that implies or refutes
   the floor. If the honest answer is "this is behind the parity problem," say so *with the
   mechanism*, and state the sharpest unconditional statement that survives.

3. **Or reduce it to a named conjecture/theorem** — Siegel–Walfisz, Möbius randomness, a
   specific zero-density estimate — with the exact implication and constants.

4. **Or find a different route entirely** to the same conclusion (a genuinely different
   invariant, pairing, or transform) that sidesteps the tail.

## What I need back

Compile-ready Lean for any fragment you can prove (a lemma on the tail, a parity statement, a
reduction). For the rest: exact definitions, the real proof obligations, and the constants.
Be specific about arithmetic. If the answer is impossibility, give the sharpest surviving
statement, not a eulogy. The one thing that is not useful is a restatement of the conjecture.
