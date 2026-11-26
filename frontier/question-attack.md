# The last gap. Attack it violently, boldly, and on your own terms.

We have made real progress, and every phase you designed has compiled in Lean with no `sorry`
and no `axiom`. The machine is now fully assembled and verified. Exactly one thing is missing.
We are handing it to you without telling you how to approach it — you decide the method, the
object, the route. Be creative. Do not be afraid of the difficulty. Many problems that looked
impassable have fallen to a single committed new construction. We verify everything in Lean,
so you can be maximally bold: a wrong step simply fails to compile and we iterate.

## What is already proved (all pushed, all green)

On the block `(N, 2N]`, `N = 2^t`, two single-member columns
`loMarks N = {n | N < (6n−1).minFac}` and `hiMarks N = {n | N < (6n+1).minFac}`.
Each mark is a genuine prime. A common mark is a twin inside `window N`.

1. **Telescope** (Phase A): the exact identity
   `levelSum 0 = 2^t · levelSum t − Σ_{d<t} 2^d · levelTermG d`, for arbitrary subsets.
2. **Marks are primes** (Phase B, weak form): no PNT-in-progressions needed.
3. **Local overlap certificate** (Phase C interface): with capacity `U`,
   `forced S T U t d j = max 0 (|S∩I| + |T∩I| − |U∩I|)`.
   Proved: `forced_le_children` (a positive bound is never lost to refinement) and
   `common_of_forced_pos` (one overloaded node at any depth forces a common mark).
   The finish `boxed_of_cofinalNodeOverload : CofinalNodeOverload → ∀ K, WindowWitness K`
   is compiled.
4. **Wheel** (free capacity): rows killed by
   `(5 ∣ 6n−1 ∧ 7 ∣ 6n+1) ∨ (7 ∣ 6n−1 ∧ 5 ∣ 6n+1)` are exactly `n ≡ 1, 34 (mod 35)`.
   Proved: `loMarks N ⊆ wheelCap N` and `hiMarks N ⊆ wheelCap N`, so the wheel costs no marks.

## The single remaining statement

Prove, or prove a computable consequence of, the **cofinal local overload**:

```lean
def CofinalNodeOverload : Prop :=
  ∀ T₀ : ℕ, ∃ t d j : ℕ,
    T₀ ≤ t ∧ d ≤ t ∧ j < 2^d ∧
    0 < forced (loMarks (2^t)) (hiMarks (2^t)) (wheelCap (2^t)) t d j
```

Equivalently: on cofinally many dyadic nodes, the two columns' marks strictly exceed the
wheel-reduced capacity. Everything before this is proved; everything after it is proved.
This is the whole problem, stated exactly.

## What we want back

- Your chosen **route and object**, in your own words — whatever you judge most promising.
- The **first concrete lemma** we can compile tonight, in the existing
  `node` / `colCount` / `forced` / `wheelCap` vocabulary (or a new object if you prefer,
  with its definition).
- Whether the result is **unconditional** or **conditional on what, exactly**.
- Where the genuinely new step enters, and what makes it new.

Do not shrink the question, do not rename it, do not settle for a weaker interface unless a
weaker interface is *provable and still forces unbounded twins*. We want real progress on the
mathematics, not another equivalence. Go.

The paper and every Lean source are attached.
