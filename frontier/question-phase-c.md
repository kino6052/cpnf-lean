# Phase C — the one estimate left. Be bold and creative; this is exactly the kind of thing that needs you.

You have been right so far, and every phase you designed has compiled in Lean. Phases A and B
are now **done and proved** (see below). Only Phase C remains: the debt bound. This is the
creative heart of the problem, and we want your boldest, most original idea — not a recital of
why it is hard. Many hard things have fallen recently precisely because a model committed to
one new construction and carried it through. We verify everything in Lean, so you can be as
bold as you like; a wrong step simply fails to compile and we iterate.

## Where we are (all compiled, no `sorry`, no `axiom`, pushed)

On the block `(N, 2N]` with `N = 2^t`, two single-member columns
`loMarks N = {n | N < (6n−1).minFac}`, `hiMarks N = {n | N < (6n+1).minFac}`. Each mark is a
genuine prime (Phase B), and a common mark is already a twin (inside `window N`).

Phase A is proved — the exact telescope, for two **arbitrary** subsets `S T`:

```lean
column_telescope (S T : Finset ℕ) (t) :
  levelSum S T t 0 = 2^t * levelSum S T t t − ∑ d ∈ Finset.range t, (2:ℤ)^d * levelTermG S T t d
```

with `levelSum d = Σ_j colCount(S,node) * colCount(T,node)` over the `2^d` nodes of the binary
block decomposition, and `levelTermG d = Σ_j (colCount_S_left − colCount_S_right) *
(colCount_T_left − colCount_T_right)`. At depth `t` the nodes are singletons, so
`levelSum t t = #(S ∩ T)` (the common-mark count).

Specialized to `S = loMarks (2^t)`, `T = hiMarks (2^t)`, the root term
`rootProduct t = (loMarks.card) * (hiMarks.card)` is the signal, and the sum of the
`levelTermG d` is exactly how that signal is lost as the two columns are resolved to the same
row.

## What Phase C needs

A condition that forces `#(loMarks ∩ hiMarks) > 0` cofinally. Your own earlier proposal was

```lean
def CofinalHalfDebt : Prop := ∀ T, ∃ t, T ≤ t ∧ 2 * levelDebt t ≤ rootProduct t
```

where `levelDebt t = Σ_d max 0 (−levelTerm t d)`. But we are **not** wedded to this. We want
your judgment on the sharpest, most provable version:

1. **Is half-debt true, or is something weaker enough?** The finish only needs the common-mark
   count to be positive on one block past each `K`. State the exact minimal hypothesis.
2. **Can the debt be bounded by something you can actually prove** — e.g. by pairing nodes,
   by a Cauchy–Schwarz or second-moment identity, by an expansion of `(A_L − A_R)(B_L − B_R)`
   into shifted counts of one column, or by a sign argument? Give the identity.
3. **Can the now-Lean-proven Riemann Hypothesis be used as a formalized tool** to bound the
   `levelTerm` fluctuations, and how exactly does a zero-free-region / explicit error bound
   enter one `levelTerm`?
4. **Or change the object.** If the two-column telescope fights you, propose a different
   decomposition whose correction term is provably nonnegative or provably small. Be original.

## What we want back

- The **idea** in one paragraph, precise enough to formalize.
- The **exact Lean signature** of the Phase C hypothesis you commit to, and the lemma chain
  from it to `boxed_of_…` (the finish).
- The **first lemma** we can compile tonight, over `ℕ`/`Finset`/`ℤ` in the existing
  `node`/`colCount`/`levelSum`/`levelTermG` vocabulary.
- Where the **novel step** enters, and whether the result is unconditional or conditional (on
  what, exactly).

Be bold. The paper and every Lean source are attached.
