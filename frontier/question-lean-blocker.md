# A Lean/Mathlib technical blocker, with a concrete goal

We are formalizing an unconditional "top-band exclusion" for twin-index coverage. The
mathematics is settled; one *Lean* step keeps failing. Please give the exact tactic script.

## The blocker

We need:

```lean
theorem gcd_mod_self (n : ℕ) : (n % 210).gcd 210 = n.gcd 210
```

Attempts that FAILED:

1. `rw [Nat.gcd_rec 210 n]` — signature is `Nat.gcd_rec (m n : ℕ) : m.gcd n = (n % m).gcd m`.
   With `m = n`, `n = 210` it rewrites `n.gcd 210` to `(210 % n).gcd n` — wrong argument.
2. `rw [Nat.gcd_rec n 210]` — rewrites `n.gcd 210` to `(210 % n).gcd n`. Also wrong.
3. `Nat.gcd_comm 210` — "Did not find an occurrence of the pattern `Nat.gcd 210 ?n`" in
   `(n % 210).gcd 210 = n.gcd 210`. (Argument order of `gcd_comm` is confusing us.)
4. `simp [Nat.Coprime, Nat.gcd_rec]` — "Possibly looping simp theorem: Nat.gcd_rec" and
   max recursion depth exceeded.
5. `Nat.gcd_add_mul_right_right 210 n 1 : 210.gcd (n + 1 * 210) = 210.gcd n` — this gives
   *periodicity of 210*, which we already use elsewhere (`Coprime (b+210) 210 ↔ Coprime b 210`),
   but does not directly give `gcd (n % 210) 210 = gcd n 210`.

What we actually want mathematically is trivial: `gcd (n mod 210) 210 = gcd n 210`, because
210 | 210. In Lean's `Nat`, `n % 210` is the remainder.

**Please give a compiling proof of `gcd_mod_self`,** using only Mathlib v4.36.0, and say which
lemma it rests on (`Nat.gcd_dvd`? `Nat.dvd_gcd_iff`? `Nat.mod_mod_of_dvd`? `Nat.gcd_rec`
applied to the right pair?).

## The bigger target this unblocks

Once `gcd_mod_self` is available, the real theorem is the wheel block count:

```lean
/-- Exactly 48 integers coprime to 210 in any block `[a+1, a+210]`. -/
theorem wheel_block (a : ℕ) :
    ((Finset.Icc (a + 1) (a + 210)).filter (fun b => Nat.Coprime b 210)).card = 48
```

Our plan: `[a+1, a+210]` is a translate of `[1,210]`, `b ↦ a + b` is a bijection there,
and `Coprime (a+b) 210 ↔ Coprime ((a+b) % 210) 210` by `gcd_mod_self`; then reduce to the
`decide`-closed base case
`((Finset.Icc 1 210).filter (fun b => Nat.Coprime b 210)).card = 48` (this one compiles).

Our failing attempt at the translate:

```lean
theorem icc_shift (a : ℕ) : Finset.Icc (a + 1) (a + 210) = (Finset.Icc 1 210).map
    ⟨fun b => a + b, fun x y h => Nat.add_left_cancel h⟩ := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - a, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨b, ⟨h1, h2⟩, rfl⟩
    omega   -- FAILS: the embedding's toFun does not reduce
```

**Also give a compiling proof of `wheel_block`** (a direct `Finset.card_bij` or
`Finset.card_image` route is fine — we do not need `icc_shift` as a separate lemma).

## Constraint

Mathlib v4.36.0, `import Mathlib`, no `sorry`, no `axiom`. Give the full tactic scripts.
