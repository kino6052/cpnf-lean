# One Lean bijection. Third retry on the same step — please give us the literal proof.

You were right on both diagnoses from last round, and both of your fragments compiled
unmodified: `div_width_err` and `err_step` are green. The `linarith` "failure" was indeed a
false statement over `ℚ` (`U = -1`), and your shift trick is what we were missing. Thank you.

We are now stuck on a **single `Finset.card_bij`**, and we have failed three ways. This is a
pure Lean-API problem, not mathematics. We need the literal term, checked, not a sketch.

## The target

```lean
def liveIoc (P : Finset ℕ) (u v : ℕ) : Finset ℕ :=
  (Finset.Ioc u v).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)

lemma liveIoc_insert_card {p : ℕ} {P : Finset ℕ} (hp : Nat.Prime p) (hpP : p ∉ P)
    (u v : ℕ) :
    (liveIoc (insert p P) u v).card + (liveIoc P (u/p) (v/p)).card =
      (liveIoc P u v).card
```

## What works

The partition is done and compiles: with `S := liveIoc P u v`, `notp := S.filter (¬ p ∣ ·)`,
`byp := S.filter (p ∣ ·)`, we have `notp ∪ byp = S` disjoint, hence
`notp.card + byp.card = S.card`. We also proved `notp = liveIoc (insert p P) u v`.

## The exact failure

Only `byp.card = (liveIoc P (u/p) (v/p)).card` remains, via `k ↦ k * p`. Three concrete
obstacles, each reproduced:

**1. `set` + `rw` corrupts the endpoints.** After `rw [hbyp]`, the goal displays the target
as `liveIoc P (u/p/p) (v/p/p)` — the `u/p` gets rewritten again. So `Nat.lt_mul_of_div_lt`
expects `u / p / p < k` when `hk1 : u < k`. We do not know how to stop the rewrite from
descending into the target's arguments. `change` did not fix it.

**2. `intro k hk` on the `hmem` obligation destructs the `List.Mem`.** Writing
`intro k hk; obtain ⟨hkS, hkp⟩ := Finset.mem_filter.mp hk` produces
"`cases` failed: Dependent elimination failed … `List.filter … = k :: as`".
We had to use `(Finset.mem_filter.mp hk).1` / `.2` directly, and even then the goal under
`hmem` was `k * p ∈ Finset.Ioc (u/p) (v/p)`, i.e. **without** the outer `liveIoc` filter,
while the hypotheses were about `k ∈ S` — the filter layers (`S` vs `Ioc`) are misaligned by
one, and we could not work out which layer `card_bij` hands us.

**3. The divisibility transport is the only real content.** For `q ∈ P` we need
`q ∣ k * p ↔ q ∣ k`, using `p ∉ P` and `q ≠ p`. Our attempt
`(hp.dvd_mul.mp hqd).resolve_right (fun hqp => hpP (hqp ▸ hq))` failed with
"invalid `▸` notation, argument `hqp`" — we do not have the right idiom for rewriting a
membership through an equality of primes.

## What we need

The **complete, compiled** proof of `liveIoc_insert_card` (or of just the `byp` bijection, if
you prefer to state it separately), in this Mathlib `v4.36.0`, with no `sorry`. We will paste
it and build immediately. If the cleanest route avoids `Finset.card_bij` entirely — e.g.
`Finset.card_image_of_injOn`, or an equivalence of `Finset`s, or `Nat.card_congr` — use that.

Everything else in your plan is already green; this is the last lever.
