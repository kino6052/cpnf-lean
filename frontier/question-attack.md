# Finalize it. Construct the cofinal overload.

You have the full paper and every Lean source below. The whole framework is compiled and
green. One statement stands between us and the finish. Attack that statement with everything
you have. Do not be bound by the density route, by the existing vocabulary, or by anything in
this file except the definitions — they are fixed. If the right move is a new object, a new
certificate, a different induction, a modular/2-adic/algebraic obstruction, a change of base,
an impossibility proof, or a genuine reduction of the search space, take it. You choose the
path. You are not here to relabel the conjecture as a definition; you are here to build.

## The single target

```lean
def forced (S T U : Finset ℕ) (t d j : ℕ) : ℤ :=
  max 0 (colCount S t d j + colCount T t d j - colCount U t d j)

def CofinalNodeOverload : Prop :=
  ∀ T₀ : ℕ, ∃ t d j : ℕ,
    T₀ ≤ t ∧ d ≤ t ∧ j < 2^d ∧
    0 < forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j
```

Prove `CofinalNodeOverload` — or prove it impossible, or reduce it to something strictly
smaller that we can then grind in Lean.

## Why this is the finish

```lean
theorem boxed_of_cofinalNodeOverload (H : CofinalNodeOverload) :
    ∀ K, WindowWitness K
-- and  windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect
-- and  OftenDirect  is the exact twin-prime statement in this framework
```

So this is equivalent to unbounded twins. That is not a reason to flinch; it is the point.
Attack it directly.

## The vocabulary (all compiled)

```lean
def twinLo n := 6*n - 1 ; def twinHi n := 6*n + 1
def score n := min (twinLo n).minFac (twinHi n).minFac
def blk X := Finset.Ioc X (2*X)
def loMarks N := (blk N).filter (fun n => N < (twinLo n).minFac)
def hiMarks N := (blk N).filter (fun n => N < (twinHi n).minFac)
def node t d j := Ioc (2^t + j*2^(t-d)) (2^t + (j+1)*2^(t-d))
def colCount S t d j := ((S ∩ node t d j).card : ℤ)
def contrast S t d j := colCount S t (d+1) (2*j) - colCount S t (d+1) (2*j+1)
```

`forced` is monotone down the dyadic tree: `forced_le_children` proves a positive overload
is never lost to a finer scale. A positive overload at any node forces a common mark
(`common_of_forced_pos`), hence a twin.

## The known wall (your own earlier result, now compiled)

For a node of length `L = 2^(t-d)`, the nine primes `{5,7,11,13,17,19,23,29,31}` force

  `colCount(loMarks) ≤ ρL + 512`, `colCount(hiMarks) ≤ ρL + 512`, `colCount(blk) ≥ (33/35)L − 2`,

with `ρ = ∏(1−1/p) < 0.46`. So for `L ≥ 65536` (i.e. `t − d ≥ 16`) the node has
`a + b < c` and `forced = 0`. **Positive overload lives entirely in `t − d ≤ 15` — the last
16 dyadic levels of every block.** The problem is cornered there. That is your arena.

There is also the exact dyadic identity `column_telescope`:

  `levelSum S T t 0 = 2^t · levelSum S T t t − Σ_{d<t} 2^d · levelTermG S T t d`

with `levelSum S T t d = Σ_j colCount S t d j · colCount T t d j` and
`levelTermG S T t d = Σ_j contrast S t d j · contrast T t d j`. Use it, break it, or ignore it.

## What I need back

One of:
1. A proof of `CofinalNodeOverload` — the construction, in enough detail to formalize;
2. A proof it is false, with the obstruction;
3. A *new equivalent* statement strictly easier to attack, with a sketch of the equivalence;
4. A genuine reduction of the last-16-levels search (fewer levels, fewer classes, a finite
   list of candidate certificates) that I can feed to Lean.

Give compile-ready Lean for any fragment you can, and for the rest give exact definitions and
the real proof obligations. Be specific about the arithmetic. If the honest answer is a
reduction rather than a resolution, make it a sharp one — a smaller problem, not a restatement.
