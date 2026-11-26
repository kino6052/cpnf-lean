# Give a compiling Lean script for the per-prime top-band bound

We have compiled the finite core already (`Progression.lean`, attached). Now we need the two
steps that bridge from a residue-class `Finset` to that core. Give the **full compiling
tactic scripts** for both, Mathlib v4.36.0, `import Mathlib`, no `sorry`, no `axiom`.

## Already compiled (in `CpnfLean.Progression`, namespace `CPNF`)

```lean
theorem ceil_div_le (q L : ℕ) (hq : 0 < q) (hL : 1 ≤ L) :
    (L - 1)/q + 1 ≤ (L + q - 1)/q

theorem card_mod_eq_le (q L r : ℕ) (hq : 0 < q) :
    ((Finset.range L).filter (fun j => j % q = r)).card ≤ (L + q - 1)/q
```

Also compiled (in `CpnfLean.TopBand`, namespace `CPNF`):

```lean
def blk (X : ℕ) : Finset ℕ := Finset.Ioc X (2 * X)
def classBlock (X M r : ℕ) : Finset ℕ := (blk X).filter (fun n => n % M = r)
```

And in the base files: `twinLo n = 6 * n - 1`, `twinHi n = 6 * n + 1` (defs, with
`twinLo` using truncated subtraction).

## Theorem to prove (the corrected per-prime bound)

```lean
theorem per_prime_bound (X M r q : ℕ) (hM : 0 < M) (hr : r < M) (hq : Nat.Prime q)
    (hq3 : 3 < q) (hcop : Nat.Coprime q M) :
    ((classBlock X M r).filter (fun n => q ∣ twinLo n ∨ q ∣ twinHi n)).card ≤
      2 * (((classBlock X M r).card + q - 1) / q) := by
  sorry
```

**Why `2 *`:** each of the two signs `6n-1`, `6n+1` contributes at most one residue class
modulo `q`, because `6 * M` is invertible mod `q` (`q > 3` so `Coprime q 6`, and `Coprime q M`).

## The two steps we could not get clean

### Step 1 — classBlock is a consecutive progression

Prove (or give a statement you can actually prove) that `classBlock X M r`, when nonempty,
equals `{a + M * j : j < L}` for `a = classBlock X M r .min' h` and `L = (classBlock X M r).card`.
We tried `Finset.card_le_card_of_injOn`/`card_bij` and got stuck on the `a + M*j` ordering
and the membership of the image. Give the exact statement you would use and its proof.

### Step 2 — each sign is one residue class modulo q

For a fixed sign, show the set `{j < L : q ∣ twinLo (a + M*j)}` is contained in (or equal to)
`{j < L : j % q = r₀}` for a single `r₀`, using `Coprime q (6*M)` so that
`6*(a+M*j) ≡ 1 [MOD q]` pins `j` to one residue. Give the exact `Nat.ModEq`/`ZMod` lemmas and
the script.

## What to return

Full `namespace CPNF ... end CPNF` with:
1. the `classBlock` parametrization lemma (whatever exact form you choose, stated and proved),
2. the `per_prime_bound` theorem proved using (1) and `card_mod_eq_le`, applied twice with a
   union bound. If `Finset.card_union_le` is cleaner than a disjointness argument, use it and
   say so.

Keep everything over `ℕ` and `Finset`; no `ℚ`, no asymptotics. If Step 1 has an edge case
(empty class), handle it with a `by_cases` on nonempty.
