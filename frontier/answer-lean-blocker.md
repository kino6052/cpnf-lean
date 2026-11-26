Use `(Nat.gcd_rec 210 n).symm`: its left side is exactly `(n % 210).gcd 210`, and its right side is `210.gcd n`. One application of `Nat.gcd_comm` finishes.

For `wheel_block`, translation by `a` need not preserve coprimality. Instead, shift the block **one step** by induction. The overlapping entries stay fixed, and the entering endpoint `a + 211` has the same gcd as the leaving endpoint `a + 1`.

```lean
import Mathlib

theorem gcd_mod_self (n : ℕ) : (n % 210).gcd 210 = n.gcd 210 := by
  exact (Nat.gcd_rec 210 n).symm.trans (Nat.gcd_comm 210 n)

theorem wheel_block (a : ℕ) :
    ((Finset.Icc (a + 1) (a + 210)).filter (fun b => Nat.Coprime b 210)).card = 48 := by
  induction a with
  | zero =>
    change ((Finset.Icc 1 210).filter (fun b : ℕ => Nat.Coprime b 210)).card = 48
    decide
  | succ a ih =>
    have hend : Nat.Coprime (a + 211) 210 ↔ Nat.Coprime (a + 1) 210 := by
      have hm : (a + 211) % 210 = (a + 1) % 210 := by
        rw [show a + 211 = (a + 1) + 210 by omega, Nat.add_mod_right]
      change (a + 211).gcd 210 = 1 ↔ (a + 1).gcd 210 = 1
      rw [← gcd_mod_self (a + 211), ← gcd_mod_self (a + 1), hm]

    refine Eq.trans ?_ ih
    apply Finset.card_bij (fun x _ => if x = a + 211 then a + 1 else x)
    · intro x hx
      obtain ⟨⟨hl, hu⟩, hc⟩ :
          (a.succ + 1 ≤ x ∧ x ≤ a.succ + 210) ∧ Nat.Coprime x 210 := by
        simpa only [Finset.mem_filter, Finset.mem_Icc] using hx
      by_cases h : x = a + 211
      · subst x
        simp only [if_pos rfl, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, by omega⟩, hend.mp hc⟩
      · simp only [if_neg h, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, hc⟩
    · intro x hx y hy he
      have hxl := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1
      have hyl := (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1
      change (if x = a + 211 then a + 1 else x) =
        (if y = a + 211 then a + 1 else y) at he
      split_ifs at he <;> omega
    · intro y hy
      obtain ⟨⟨hl, hu⟩, hc⟩ :
          (a + 1 ≤ y ∧ y ≤ a + 210) ∧ Nat.Coprime y 210 := by
        simpa only [Finset.mem_filter, Finset.mem_Icc] using hy
      by_cases h : y = a + 1
      · subst y
        refine ⟨a + 211, Finset.mem_filter.mpr ⟨?_, hend.mpr hc⟩, if_pos rfl⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · refine ⟨y, Finset.mem_filter.mpr ⟨?_, hc⟩, if_neg (by omega)⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
```
