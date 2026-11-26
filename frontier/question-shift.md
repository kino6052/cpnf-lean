# One Lean recursion-depth bug. Everything else is done.

We are NOT asking you to redo the math. The inclusion–exclusion bound is **proved and compiled**.
We hit a single Lean elaborator bug on the last, purely mechanical step (the shift trick), and
we have failed four variations. We need the literal term that avoids it.

## What now compiles (all green, in this Mathlib v4.36.0)

```lean
def sieveRho (P : Finset ℕ) : ℚ := ∏ p ∈ P, (1 - 1/(p:ℚ))
def liveIoc (P : Finset ℕ) (u v : ℕ) : Finset ℕ :=
  (Finset.Ioc u v).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)

theorem sieve_discrepancy (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) :
    ∀ u v : ℕ, u ≤ v →
    |((liveIoc P u v).card : ℚ) - sieveRho P * ((v:ℚ)-(u:ℚ))| ≤ (2:ℚ)^P.card - 1
```

This is your two-sided discrepancy induction, exactly as you specified: `liveIoc_insert_card`
(the `k ↦ k*p` bijection, with `hP : ∀ q ∈ P, Nat.Prime q` — thank you, that was the fix),
`div_width_err`, `err_step`. All proved.

## The last step: transport `¬ p ∣ 6n±1` to `¬ p ∣ n`

For `f n = 6n − 1` and `f n = 6n + 1`, a single shift `s` makes `p ∣ (n + s) → p ∣ f n`. We need

- `6·s + 1 = 5·M` for the low mark, and `6·s − 1 = M` for the high mark, where `M = ∏ ninePrimes = 33426748355`.

So `loShift = 27855623629` and `hiShift = 5571124726`, both correct (we verified with a calculator).

## The bug: recursion depth on huge literal defs

`native_decide` proves the equalities fine. But the moment a huge-literal `def` meets a
definitional commute, the elaborator recurses. **Minimal reproducer**:

```lean
import Mathlib
def loShift : ℕ := 27855623629
example {n p : ℕ} (h : p ∣ n + loShift) : p ∣ 6 * (n + loShift) :=
  dvd_mul_of_dvd_left h 6   -- maximum recursion depth reached
example {n p : ℕ} (h : p ∣ n + loShift) : p ∣ (n + loShift) * 6 :=
  dvd_mul_of_dvd_left h 6   -- this one is fine
```

`dvd_mul_of_dvd_left : a ∣ b → a ∣ b * c`, so the failure is the defeq check
`(n + loShift) * 6 =?= 6 * (n + loShift)` commuting a multiplication whose factor is a
`def` holding an 11-digit numeral. `set_option maxRecDepth 20000` does not help — it is an
infinite/unbounded elaboration, not a deep one.

## What we need

The compile-ready `twinLo_shift` / `twinHi_shift` (or the single shared lemma), stated as

```lean
theorem twinLo_shift {n p : ℕ} (hp : p ∈ ninePrimes) (h : p ∣ n + loShift) : p ∣ twinLo n
theorem twinHi_shift {n p : ℕ} (hp : p ∈ ninePrimes) (h : p ∣ n + hiShift) : p ∣ twinHi n
```

with `twinLo n := 6*n − 1`, `twinHi n := 6*n + 1`, `ninePrimes := {5,7,11,13,17,19,23,29,31}`.
Any of these fixes is acceptable: a `show`/`change` that avoids the defeq commute, a
`Nat.mul_comm` rewrite before the `dvd` step, a different `dvd` lemma with the factor already
on the correct side, or a different witness for `s` that sidesteps the huge literal. Just give
us the term that compiles; we will paste it and build.
