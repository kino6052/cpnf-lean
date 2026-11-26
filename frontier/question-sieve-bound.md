# A narrow technical block. Not the mathematics — that part you already gave us.

Your obstruction is nearly fully compiled. One step is left, and it is stalling us. We need
your help on this specific piece only, not on the problem again.

## What is compiled (pushed, green, no `sorry`)

- `forced_le_children`, `common_of_forced_pos`, `boxed_of_cofinalNodeOverload` — the
  overlap certificate and the finish.
- `wheelKilled_of_mod_one`, `wheelKilled_of_mod_thirtyfour`, `mod_of_wheelKilled` (the
  kill→residue direction you flagged), `loMarks_subset_wheelCap`, `hiMarks_subset_wheelCap`.
- `loMark_no_nine_dvd`, `hiMark_no_nine_dvd` — marks avoid `{5,7,11,13,17,19,23,29,31}`.
- `killed_range_le` — at most `2⌈L/35⌉` killed rows per `L`.
- `nine_prime_density`, `forced_zero_of_nine_prime_bounds` — your numerical certificate,
  compiled exactly as you wrote it.

## The block

I need the column count `a ≤ ρL + 512` for a set `A ⊆ Finset.range L` whose elements avoid
all nine primes. Two things are going wrong.

**1. The inclusion–exclusion direction.** I first tried bounding `|A|` by `L − |union of
multiples|` and then bounding the union by the *sum* of the individual counts. That is the
wrong direction for inclusion–exclusion: it gives `|A| ≥ (1−Σ1/p)L`, not an upper bound. The
correct statement needs the exact alternating sum
`Σ_{t ⊆ P} (−1)^{|t|} ⌊·/∏t⌋`, and `Mathlib` has no ready-made bound for it. `Finset.prod_sub`
gives `∏_{p∈P}(1 − 1/p) = Σ_{t ⊆ P} (−1)^{|t|} ∏_{p∈t} 1/p`, which is the right algebraic
shape, but turning it into a count over `Finset.range L` needs a per-subset progression count
`⌊L/m_t⌋` and an error term summed over `2^9` subsets.

**2. A tactic failure that may indicate my statement is wrong.** In this `Mathlib`
(`v4.36.0`), `linarith` fails on goals that look plainly linear. Minimal reproducer:

```lean
import Mathlib
example (a L U : ℚ) (h1 : a ≤ L - U) (h2 : U ≤ 9) : a ≤ L - 9 + 9 := by
  linarith  -- fails
```

`linarith` succeeds on `a ≤ b`, `b ≤ c` ⊢ `a ≤ c`, so it is not a broken import. It fails
whenever subtraction and a numeral mix. `nlinarith` fails on the same shapes.

## What we need from you

- **The exact lemma statement** for the column count that is actually true and actually
  provable, with the hypothesis shape you want (`A ⊆ Finset.range L`, avoidance hypothesis,
  and the conclusion in whichever form you think survives `linarith` in this `Mathlib`).
- **The proof sketch in steps small enough to compile**, especially the inclusion–exclusion
  accounting. If you know a slicker route than full inclusion–exclusion (a sieve weight, a
  device that only needs `2^k` errors, an appeal to `Nat.card` of a product), give that
  instead — that is the kind of thing we want.
- **A note on the `linarith` behaviour**: whether the shapes I am writing are subtly
  ill-formed, or whether this is a known tactic limitation we should just route around with
  `omega`/`nlinarith`/`positivity`.

Compile-ready Lean is ideal. We will verify it immediately.
