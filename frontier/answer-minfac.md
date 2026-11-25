`prime_of_minFac_gt` is true. The bare three-hypothesis `example` is false: take `B = 2` and `c = m = 4`. The cycle forces equality, not `False`, so naming `B * B` cannot help.

In the actual first branch, use just `hsq` and `hB` to get `m.minFac * m.minFac ≤ B * B`. On `ℕ` this implies `m.minFac ≤ B`, contradicting the original **strict** `h`. You don't need `h2`:

```lean
theorem prime_of_minFac_gt {m B : ℕ} (hm : 2 ≤ m)
    (hB : m ≤ B * B) (h : B < m.minFac) : Nat.Prime m := by
  rcases Nat.lt_or_ge m.minFac m with hlt | hge
  · exfalso
    have hsq := minFac_sq_le hm hlt
    exact (not_le_of_gt h)
      (Nat.mul_self_le_mul_self_iff.mp (hsq.trans hB))
  · have heq : m.minFac = m :=
      le_antisymm (Nat.minFac_le (by omega : 0 < m)) hge
    have hp := Nat.minFac_prime (by omega : m ≠ 1)
    simpa only [heq] using hp
```

Your `m = 4`, `B = 2` check is exactly right: `m ≤ B * B` holds, and it is `h : 2 < 2` that fails. Weakening `h` to `≤` would make the theorem false.

For the payoff, the row excludes prime factors **strictly below** `twinLo n`, not factors equal to it: the lower prime divides itself. Use `B = 3 * n` instead. For every `n ≥ 1`, this is strictly below the lower member, yet `B * B` already covers the upper member. Here is the proof inside `namespace CPNF`, after the arithmetic lemma:

```lean
theorem twin_of_score_row {n : ℕ} (hn : 1 ≤ n) (h : twinLo n ≤ score n) :
    Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  have hlo : twinLo n ≤ (twinLo n).minFac := h.trans (min_le_left _ _)
  have hhi : twinLo n ≤ (twinHi n).minFac := h.trans (min_le_right _ _)

  have hcut : 3 * n < twinLo n := by
    unfold twinLo
    omega
  have h3 : 3 ≤ 3 * n := by omega
  have hmul : 3 * (3 * n) ≤ (3 * n) * (3 * n) :=
    Nat.mul_le_mul_right (3 * n) h3
  have hcover : twinHi n ≤ (3 * n) * (3 * n) := by
    unfold twinHi
    omega
  have horder : twinLo n ≤ twinHi n := by
    unfold twinLo twinHi
    omega

  exact ⟨prime_of_minFac_gt (by omega) (horder.trans hcover) (hcut.trans_le hlo),
         prime_of_minFac_gt (by omega) hcover (hcut.trans_le hhi)⟩
```

No separate `n = 1` branch is needed: the same cutoff gives `3 < 5` and `7 ≤ 3 * 3`.
