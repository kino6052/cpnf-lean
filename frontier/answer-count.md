Use `Finset.card_bij` with `k ↦ D * k + r`. The key to surjectivity is to work with **`n + (D - r)` rather than `n - r`**: adding `D - r` takes the target residue to zero, even when `r = D`. The resulting multiple is positive, so its multiplier has the form `k + 1`.

```lean
import Mathlib

theorem progression_card (W D r : ℕ) (hD : 0 < D) (hr : 1 ≤ r) (hrD : r ≤ D) :
    ((Finset.Icc 1 W).filter (fun n => n % D = r % D)).card = (W + D - r) / D := by
  have hbound (k : ℕ) :
      k ∈ Finset.range ((W + D - r) / D) ↔ D * k + r ≤ W := by
    rw [Finset.mem_range]
    change k.succ ≤ (W + D - r) / D ↔ D * k + r ≤ W
    rw [Nat.le_div_iff_mul_le hD, Nat.succ_mul, Nat.mul_comm k D]
    omega
  symm
  calc
    (W + D - r) / D = (Finset.range ((W + D - r) / D)).card :=
      (Finset.card_range _).symm
    _ = _ := by
      apply Finset.card_bij (fun k _ => D * k + r)
      · intro k hk
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (hbound k).mp hk⟩, ?_⟩
        rw [Nat.add_mod]
        simp
      · intro a ha b hb he
        exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_right_cancel he)
      · intro n hn
        obtain ⟨hI, hm⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn1, hnW⟩ := Finset.mem_Icc.mp hI
        have hz : (n + (D - r)) % D = 0 := by
          rw [Nat.add_mod, hm, ← Nat.add_mod, show r + (D - r) = D by omega,
            Nat.mod_self]
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hz
        cases q with
        | zero =>
          rw [Nat.mul_zero] at hq
          omega
        | succ k =>
          rw [Nat.mul_succ] at hq
          have he : D * k + r = n := by omega
          exact ⟨k, (hbound k).mpr (he ▸ hnW), he⟩
```

The only local helper is `hbound`, proved inline. Its rewrite order matters: first remove the division with `Nat.le_div_iff_mul_le hD`, then expand the successor product and put `k * D` in the same order as `D * k`. At that point `omega` only needs to treat `D * k` as a single atom. No rational-floor lemma or split on `W < r` is needed.