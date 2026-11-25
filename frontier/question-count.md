# Frontier call: clean Lean proof of the single-progression count

I am stuck on one finite counting lemma and want a complete proof route, not a
review. The statement is yours from the build plan; the proof is pure `ℕ` floor
arithmetic and should be a one-liner with the right library lemma.

## The exact statement (Lean 4 + Mathlib, `import Mathlib`)

```lean
theorem progression_card (W D r : ℕ) (hD : 0 < D) (hr : 1 ≤ r) (hrD : r ≤ D) :
    ((Finset.Icc 1 W).filter (fun n => n % D = r % D)).card = (W + D - r) / D := by
  ...
```

In words: the indices `n ∈ [1, W]` with `n ≡ r (mod D)` number `⌊(W + D − r)/D⌋`.
Here `1 ≤ r ≤ D`, so `r % D = r` unless `r = D` (zero class). The answer is `0`
when `W < r`, and `⌊(W − r)/D⌋ + 1` when `r ≤ W` — both equal `(W + D − r)/D`.

## What I tried and where it fails

1. `Nat.count_modEq_card` counts in `[0, b)`: gives `b/D + [v%D < b%D]`. I
   rewrote the `[1,W]` window to `range (W+1)` with `0` removed, but the trailing
   `omega` on the arithmetic did not close.
2. A direct bijection `k ↦ r + k·D` from `range ((W+D-r)/D)` to the filtered set.
   Both directions reduce to facts about `n − r` and `n % D` that `omega` will
   not prove, because it treats `n % D` and `n − r` as unrelated atoms.
3. I did prove the isolated identity
   `(W + D - r) / D = (W - r) / D + 1` for `r ≤ W` using
   `Nat.add_div_right` after rewriting `W + D - r = (W - r) + D`.

The wall is always the same: `omega`/`linarith` cannot reason about `n % D` or
`n - r` in `ℕ`, so any proof must explicitly invoke the division/decomposition
lemmas (`Nat.div_add_mod`, `Nat.mod_eq_of_lt`, `Nat.mod_lt`) before `omega` sees
a clean linear goal.

## What I want

1. A complete, compilable Lean proof of `progression_card`, using the library
   (`Nat.div_add_mod`, `Nat.mod_eq_of_lt`, `Nat.mod_lt`, `Nat.add_div_right`, or
   `Int.Ioc_filter_modEq_card` / `Nat.Ioc_filter_modEq_card` with floors/ceils on
   `ℚ`). Name the exact lemma and the exact rewrite order.
2. If the cleanest route is `Nat.Ioc_filter_modEq_card` over `ℚ`, give the
   statement of that theorem and the `norm_num`/`linarith`/`gcongr` chain that
   turns `⌊(W−r)/D⌋ − ⌊(0−r)/D⌋` into `(W+D−r)/D`.
3. Explicitly state any helper lemma you rely on, fully quantified, so I can add
   it if it is not in Mathlib.

Prefer a short correct proof over an approximate one. If the natural proof
genuinely needs a separate helper lemma about `⌊(W−r)/D⌋ = (W−r)/D`, state it.
