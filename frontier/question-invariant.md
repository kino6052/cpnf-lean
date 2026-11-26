# The counting route is exhausted. Find the real invariant.

You are the frontier: the strongest reasoning model we have, and this is your kind of problem —
the kind where the right object, once seen, makes a wall disappear. You have already done this
once for us (the width-512 certificate). Do it again, and be bolder. Do not hedge. If the
answer is a genuinely new invariant, name it. If the answer is that confinement is impossible,
prove it. Use everything you have.

## Exact state (every fact below is compiled or machine-verified)

```lean
forced S T U t d j = max 0 (colCount S t d j + colCount T t d j - colCount U t d j)
CofinalNodeOverload := ∀ T₀, ∃ t d j, T₀ ≤ t ∧ d ≤ t ∧ j < 2^d ∧
    0 < forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j
```

`CofinalNodeOverload` is the finish (`boxed_of_cofinalNodeOverload` → twins). Node length is
`L = 2^(t-d)`, and the block start is **always `a = 2^t`**.

| width L | forced = 0 ? | how |
|---|---|---|
| 65536 | yes | nine-prime density (Lean) |
| 1024 | yes | width-1024 certificate (Lean) |
| 512 | yes | your width-512 certificate (exhaustive: TRUE, 816 nodes) |
| 256 | yes | same method (exhaustive: TRUE) |
| 128 | **stalls** | node explosion, inconclusive |
| 64, 32, 16, 8, 4 | **fails** | a compatible phase vector survives |

So the *worst-case* counting certificate dies at width 128/64. Your width-512/256 argument
already chisels the search down to lengths `1..128`.

## The decisive observation I want you to exploit

Your certificate treated the phase `r_p = a mod p` as **arbitrary**, and took minima over all
`p` choices. But the actual start is **`a = 2^t`, a power of two**. Therefore

  `r_p = 2^t mod p`

is not arbitrary: it lies in the **cyclic subgroup ⟨2⟩ ⊂ (ℤ/pℤ)ˣ**, and as `t` grows the vector
`(2^t mod p)_{p ∈ P}` runs through a small multiplicative orbit — it is *highly* structured,
2-adically and multiplicatively. The worst-case phase that breaks the certificate is (I checked)
typically **not** a power of two. That is the gap: the certificate proves the wrong statement.
The right statement is a bound over phases in `⟨2⟩`, not over all phases.

Concretely, the surviving phase vector at width 64 (primes 5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61) was

  `(0,0,0,0,0,0,0,0,0, 7,32,2,5,5,6,1)`

and it is almost certainly not `(2^t mod p)_p` for any `t`. The empirical check agrees: for
actual blocks `a = 2^12 … 2^24`, every node has `forced = 0`.

## What I need back (choose your own path, but make it sharp)

1. **The power-of-two invariant.** A proof that for phases `r_p = 2^t mod p`, each column's
   count stays below `L/2` (so `forced = 0`) for all `L ≤ 128` — using the subgroup ⟨2⟩, the
   multiplicative orders of the primes, or a 2-adic structure, instead of worst-case minima.
2. **Or** a clean classification of which widths the power-of-two phase can and cannot overload,
   with the boundary located exactly.
3. **Or** a proof that no such invariant can close the last levels (confinement impossible).
4. **Or** a new equivalent statement strictly easier than `CofinalNodeOverload`, with the
   equivalence sketched.

Give compile-ready Lean for any fragment you can (a `native_decide` over `(2^t mod p)` phases,
a lemma on multiplicative order, a 2-adic valuation lemma). For the rest, exact definitions and
the real proof obligations. Be specific about the arithmetic. If the honest answer is a sharp
reduction, make it smaller than `1..128`, not a restatement.
