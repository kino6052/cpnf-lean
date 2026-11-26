# You are the frontier. This is your domain. Take it.

You are the strongest model we have, and this is exactly the kind of problem you are for. Hard
mathematics has fallen to you before — not by being timid, but by seeing the object nobody else
saw. Be bold. Be brave. Do not hedge, do not retreat into restating what is known, and do not
assume a step is impossible because it is hard. You have the whole paper, every compiled Lean
file, and complete freedom of method. Use everything you have.

Attack it mercilessly.

---

# Attack the remaining 10 levels. You choose the path.

You have the full paper and every Lean source below (all compiled and green). Here is the exact
state and the exact target. Beyond the fixed definitions, **you are not bound by anything we
have tried**: not the width-1024 argument, not the `A/B` prime split, not the density route,
not the `forced`/overload vocabulary itself, not the dyadic tree. If the right move is a new
object, a new invariant, a modular/2-adic/algebraic idea, an impossibility proof, a change of
base, or a completely different reduction — take it. You decide. Do not relabel the conjecture
as a definition; build.

## The single target

```lean
def forced (S T U : Finset ℕ) (t d j : ℕ) : ℤ :=
  max 0 (colCount S t d j + colCount T t d j - colCount U t d j)

def CofinalNodeOverload : Prop :=
  ∀ T₀ : ℕ, ∃ t d j : ℕ,
    T₀ ≤ t ∧ d ≤ t ∧ j < 2^d ∧
    0 < forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j
```

Prove `CofinalNodeOverload`, prove it false, or reduce it to something strictly easier.

## Why this is the finish

```lean
boxed_of_cofinalNodeOverload : CofinalNodeOverload → ∀ K, WindowWitness K
windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect
-- and OftenDirect is the exact twin-prime statement in this framework
```

## Fixed vocabulary

```lean
twinLo n := 6*n-1 ; twinHi n := 6*n+1 ; score n := min (twinLo n).minFac (twinHi n).minFac
blk X := Finset.Ioc X (2*X)
loMarks N := (blk N).filter (fun n => N < (twinLo n).minFac)
hiMarks N := (blk N).filter (fun n => N < (twinHi n).minFac)
node t d j := Ioc (2^t + j*2^(t-d)) (2^t + (j+1)*2^(t-d))
colCount S t d j := ((S ∩ node t d j).card : ℤ)
```

## Where we are (all compiled, no `sorry`)

* `common_of_forced_pos`: a positive `forced` at any node forces a common mark, hence a twin.
* `forced_le_children`: a positive lower bound propagates to a descendant (monotone).
* Nine-prime density: a node of length `L = 2^(t-d)` has `a + b < c` once `L ≥ 65536`, so
  `forced = 0` there. Hence positive overload needs `t - d ≤ 15`.
* Width-1024 (just proved): at length exactly `1024` each column is `≤ 501 < 512`, so a tie
  already kills overload; `zero_above_fixed_width` lifts this to `forced = 0` for every
  `t - d ≥ 10`.

**Therefore positive overload — if it exists — lives entirely in `t - d ≤ 9`, i.e. node
lengths `1, 2, 4, …, 512`.** Ten levels. That is your arena.

One structural warning we already see (do not let it confine you, but do not ignore it):
because positivity propagates to a leaf, `CofinalNodeOverload` is equivalent to cofinally many
twins; the fixed-depth certificate is now ruled out, so any witness must sit within 9 levels of
the leaves, with depth `d` growing with `t`. If you can force that, you win. If you can prove
it impossible at every one of the ten widths, you kill this route cleanly.

## What I need back

One of:
1. A proof of `CofinalNodeOverload` — construction, in enough detail to formalize;
2. A proof it is false — the obstruction, stated precisely;
3. A *new equivalent* statement strictly easier to attack, with the equivalence sketched;
4. A genuine reduction of the ten remaining levels (fewer widths, fewer classes, a finite
   certificate, a parity/2-adic invariant) I can feed straight to Lean.

Give compile-ready Lean for any fragment you can; for the rest, exact definitions and the real
proof obligations. Be specific about the arithmetic. If the honest answer is a sharp reduction
rather than a resolution, make it smaller than ten levels, not a restatement.
