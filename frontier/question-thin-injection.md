# Finish `thinBad_le_baseBudget` — the count bound. Here is the exact compiling state.

I have the hard injectivity core compiling. One theorem is left, and I want the complete
Lean proof from you (do not hand it back as a signature). The check command is
`lake env lean CpnfLean/ThinInjection.lean`.

## The compiling context (verbatim, `import CpnfLean.ThinBlock`)

`CpnfLean.ThinBlock.lean` already defines (all compiling, no `sorry`):

```lean
def thinBlock (X : ℕ) : Finset ℕ := (blk X).filter (fun n => n % 14 = 11)
def thinSignal (X : ℕ) : Finset ℕ :=
  (thinBlock X).filter (fun n => PowerMember (twinLo n) ∧ PowerMember (twinHi n))
def thinBad (X : ℕ) : Finset ℕ :=
  (thinSignal X).filter (fun n => HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n))
def baseBudget (B : ℕ) : Finset ℕ := (Finset.range B).filter Nat.Prime

theorem thin_exponent_ge_five {n p e : ℕ} (hn : n % 14 = 11) (he : 2 ≤ e)
    (hm : p^e = twinLo n ∨ p^e = twinHi n) : 5 ≤ e
-- plus thin_no_square, thin_no_cube
```

`PowerMember m := Nat.Prime m ∨ HigherPrimePower m`,
`HigherPrimePower m := ∃ p ∈ Finset.Icc 2 m, Nat.Prime p ∧ ∃ e ∈ Finset.Icc 2 m, p^e = m`.

The following already compiles (my current working file, verbatim):

```lean
import Mathlib
import CpnfLean.ThinBlock
namespace CPNF

noncomputable def hppBase {m : ℕ} (h : HigherPrimePower m) : ℕ := Classical.choose h
noncomputable def hppExp {m : ℕ} (h : HigherPrimePower m) : ℕ :=
  Classical.choose (Classical.choose_spec h).2.2
lemma hppBase_prime {m : ℕ} (h : HigherPrimePower m) : Nat.Prime (hppBase h) :=
  (Classical.choose_spec h).2.1
lemma hppBase_pow {m : ℕ} (h : HigherPrimePower m) : (hppBase h) ^ (hppExp h) = m :=
  (Classical.choose_spec (Classical.choose_spec h).2.2).2
lemma hppExp_ge_two {m : ℕ} (h : HigherPrimePower m) : 2 ≤ hppExp h :=
  (Finset.mem_Icc.mp (Classical.choose_spec (Classical.choose_spec h).2.2).1).1

lemma pow_double_le {p : ℕ} (hp : 2 ≤ p) {a b : ℕ} (hab : a < b) : 2 * p ^ a ≤ p ^ b := by
  have h1 : p ^ a * p ≤ p ^ b := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : p ^ a * 2 ≤ p ^ a * p := Nat.mul_le_mul_left _ hp
  calc 2 * p ^ a = p ^ a * 2 := by ring
    _ ≤ p ^ a * p := h2
    _ ≤ p ^ b := h1

lemma thinBlock_bounds {X n : ℕ} (hn : n ∈ thinBlock X) :
    6 * X < twinLo n ∧ twinHi n ≤ 12 * X + 1 := by
  have hb : n ∈ blk X := (Finset.mem_filter.mp hn).1
  have hXn : X < n := (Finset.mem_Ioc.mp hb).1
  have hn2 : n ≤ 2 * X := (Finset.mem_Ioc.mp hb).2
  constructor
  · unfold twinLo; omega
  · unfold twinHi; omega

theorem base_inj {X n₁ n₂ m₁ m₂ : ℕ} (hX : 0 < X)
    (hne : n₁ ≠ n₂)
    (hb₁ : n₁ ∈ thinBlock X) (hb₂ : n₂ ∈ thinBlock X)
    (c₁ : m₁ = twinLo n₁ ∨ m₁ = twinHi n₁)
    (c₂ : m₂ = twinLo n₂ ∨ m₂ = twinHi n₂)
    (h₁ : HigherPrimePower m₁) (h₂ : HigherPrimePower m₂)
    (hbase : hppBase h₁ = hppBase h₂) : False := by
  -- (full proof omitted here; it compiles — uses pow_double_le and thinBlock_bounds)
  sorry

end CPNF
```

(`base_inj` is fully proved in my file, not sorry — I elided its body here for brevity. It
establishes: same base `p`, two thin-block rows → same row.)

## What I need from you, as a complete compiling file

1. A deterministic choice `thinBase : ℕ → ℕ` such that for `n ∈ thinBad X`, `thinBase n` is
   the base prime of a certificate `HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n)`
   (prefer the lower member), and prove:

```lean
theorem thinBad_le_baseBudget {X B : ℕ} (hB : 12 * X + 1 < B ^ 5) :
    (thinBad X).card ≤ (baseBudget B).card
```

   using `Finset.card_le_card_of_injOn` and `base_inj`. You must show for `n ∈ thinBad X`:
   - `Nat.Prime (thinBase n)` and `thinBase n < B` (the `< B` uses `thin_exponent_ge_five`:
     `p^5 ≤ p^e = member ≤ 12X+1 < B^5`, then `Nat.pow_lt_pow_iff_left`),
   - injectivity via `base_inj` (need the two rows' certificates and the shared base).

2. Then, if it also compiles, the corollary:

```lean
theorem boxed_of_fifth_root_signal {X B : ℕ} (hB : 12 * X + 1 < B ^ 5)
    (hs : (baseBudget B).card < (thinSignal X).card) :
    WindowWitness X
```

   or whatever the cleanest endpoint is given `boxed_of_thin_slack` (already in
   `ThinBlock.lean`).

Give me the **full file body** (inside `namespace CPNF ... end CPNF`), not a sketch. Every
lemma must be `by`-proved, no `sorry`. I will compile it verbatim.

Paper and all Lean sources attached for context.
