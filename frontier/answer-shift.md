Use `dvd_mul_of_dvd_right h 6`: it produces `p ∣ 6 * (n + s)` in exactly that order. Paste this inside `namespace CPNF`, after the shift definitions:

```lean
private theorem shift_sub_dvd {n p s c : ℕ}
    (h : p ∣ n + s) (hc : p ∣ c) :
    p ∣ (6 * n + 6 * s) - c := by
  have hm : p ∣ 6 * (n + s) := dvd_mul_of_dvd_right h 6
  rw [Nat.mul_add] at hm
  exact Nat.dvd_sub hm hc

private theorem lo_shift_aux {n p s : ℕ}
    (h : p ∣ n + s) (hc : p ∣ 6 * s + 1) : p ∣ twinLo n := by
  have he : (6 * n + 6 * s) - (6 * s + 1) = twinLo n := by
    unfold twinLo
    omega
  exact he ▸ shift_sub_dvd h hc

private theorem hi_shift_aux {n p s : ℕ}
    (hs : 0 < s) (h : p ∣ n + s) (hc : p ∣ 6 * s - 1) : p ∣ twinHi n := by
  have he : (6 * n + 6 * s) - (6 * s - 1) = twinHi n := by
    unfold twinHi
    omega
  exact he ▸ shift_sub_dvd h hc

private theorem nine_lo_offset : ∀ p ∈ ninePrimes, p ∣ 6 * loShift + 1 := by
  native_decide

private theorem nine_hi_offset : ∀ p ∈ ninePrimes, p ∣ 6 * hiShift - 1 := by
  native_decide

theorem twinLo_shift {n p : ℕ} (hp : p ∈ ninePrimes)
    (h : p ∣ n + loShift) : p ∣ twinLo n :=
  lo_shift_aux (s := loShift) h (nine_lo_offset p hp)

theorem twinHi_shift {n p : ℕ} (hp : p ∈ ninePrimes)
    (h : p ∣ n + hiShift) : p ∣ twinHi n :=
  hi_shift_aux (s := hiShift) (by native_decide) h (nine_hi_offset p hp)
```

All rewriting is on the variable `s`; only the closed numerical checks use `native_decide`. The low-side subtraction identity holds even at `n = 0` because both sides truncate to zero.
