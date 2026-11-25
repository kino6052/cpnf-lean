# One clean arithmetic lemma, and what Lean refuses

I am blocked on a short arithmetic step. All sources are attached. Please give the
correct Lean proof, or tell me the statement is false.

## The situation

`CpnfLean/Correspondence.lean` proves `admissible_iff_score` and `head_le_iff`, so the head
is a first crossing of

```lean
def score (n : ℕ) : ℕ := min (twinLo n).minFac (twinHi n).minFac
```

I want the payoff: **a passing row is a twin pair.** If `twinLo n ≤ score n`, then no
prime `≤ 6n-1` divides either member, and both members should be prime because a
composite `m ≤ 6n+1` has a prime factor at most `√m < 6n-1`.

The route is a standard primality test:

- if `m` is composite then `m.minFac ^ 2 ≤ m` (the least prime factor is at most the
  remaining cofactor);
- so if `B < m.minFac` and `m ≤ B * B` then `m` is prime.

The first part is proved and compiles:

```lean
theorem minFac_sq_le {m : ℕ} (hm : 2 ≤ m) (hlt : m.minFac < m) :
    m.minFac * m.minFac ≤ m := by
  obtain ⟨t, ht⟩ := Nat.minFac_dvd m
  have htm : t ∣ m := by rw [ht]; exact dvd_mul_left t m.minFac
  have ht2 : 2 ≤ t := by rcases t with _ | _ | t <;> omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : t ≠ 1)
  have hqm : q ∣ m := hqd.trans htm
  have hqge : m.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqm
  have hqt : q ≤ t := Nat.le_of_dvd (by omega) hqd
  calc m.minFac * m.minFac ≤ m.minFac * t := Nat.mul_le_mul_left _ (le_trans hqge hqt)
    _ = m := ht.symm
```

## The blocked lemma

```lean
theorem prime_of_minFac_gt {m B : ℕ} (hm : 2 ≤ m) (hB : m ≤ B * B) (h : B < m.minFac) :
    Nat.Prime m := by
  rcases Nat.lt_or_ge m.minFac m with hlt | hge
  · exfalso
    have hsq : m.minFac * m.minFac ≤ m := minFac_sq_le hm hlt
    have h2 : B * B ≤ m.minFac * m.minFac := Nat.mul_le_mul (le_of_lt h) (le_of_lt h)
    -- GOAL: False, from h2 : B*B ≤ c, hsq : c ≤ m, hB : m ≤ B*B
    sorry
  · have hpos : 0 < m := by omega
    have heq : m.minFac = m := le_antisymm (Nat.minFac_le hpos) hge
    have hne : m ≠ 1 := by omega
    have := Nat.minFac_prime hne
    rwa [heq] at this
```

The second branch compiles. The first branch does not, and this is the whole problem: with
`c := m.minFac * m.minFac` in context, the hypotheses are

```
h2 : B * B ≤ c
hsq : c ≤ m
hB  : m ≤ B * B
```

and the goal is `False`. That is a three-term cycle `B*B ≤ c ≤ m ≤ B*B`.

- `omega` says "could not prove the goal", with a model where `a := m`, `b := c`,
  `d := B*B` and `a - d ≤ 0`, `a - b ≥ 0`, `b - d ≥ 0`.
- `linarith [h2, hsq, hB]` says "failed to find a contradiction".
- I also could not close the bare form `example (m B c : ℕ) (h2 : B * B ≤ c) (h3 : c ≤ m)
  (hB : m ≤ B * B) : False`.

Since `B * B` is a term rather than an atom, I suspect the products are being treated as
independent variables, but the cycle is purely linear once `B * B` is named.

## What I want back

1. **The working proof of the first branch**, ideally as a self-contained `example` with
   exactly those three hypotheses. If naming `B * B` (e.g. `set D := B * B`) is needed,
   say so — I have had trouble with `set` and `omega` elsewhere in this file.
2. **Whether the statement `prime_of_minFac_gt` is even true as stated** — in particular
   the boundary `m = B * B` with `B = 2`, `m = 4`: then `m.minFac = 2`, `h : 2 < 2` fails,
   so it is `h` that excludes it. Confirm I have not got the strictness backwards.
3. **The final payoff lemma**, whatever shape makes it go through:

```lean
theorem twin_of_score_row {n : ℕ} (hn : 1 ≤ n) (h : twinLo n ≤ score n) :
    Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)
```
   with the `2 ≤ n`-style side condition added if `n = 1` needs handling separately
   (at `n = 1` the pair is `(5,7)` and both are prime, so it should hold).

Constraints: only `import Mathlib`, no new axioms, no `sorry`. Please do not restate the
`score`/`head_le_iff` material — it compiles; I only need the arithmetic.
