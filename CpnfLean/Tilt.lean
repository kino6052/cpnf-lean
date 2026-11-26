import Mathlib

/-!
# CPNF — the tilted-moment extraction

The frontier's plan attacks the twin problem by *not* asking whether `p+2` is prime, but by
counting its prime factors. Let `r n = Ω(n) - 1` (prime factors with multiplicity, minus one).
Then `r n = 0` exactly when `n` is prime; nothing is approximated.

The bridge from factor-count moments to a genuine twin count is the alternating binomial kernel.
With five terms:

`Λ₅(r) = Σ_{j=0}^{5} (-1)^j C(r,j)`

* at `r = 0` it equals `1`;
* at `r ≥ 1` it equals `-C(r-1,5)`, which is `≤ 0`.

So `1[r=0] ≥ Λ₅(r)` **for every `r`, pointwise** — the extraction is exact and finite. Weighting by
any nonnegative positive measure turns this into a lower bound for the weighted mass of twins
(`weighted_extraction`). This is the half of the plan that needs no analysis, and it fixes the
error budget before any moment estimate is attempted: five moments, each off by `ε`, leave the
twin mass at least `1/15 - 5ε`.

No `sorry`, no `axiom`.
-/


theorem alternating_sum_choose (m k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ((m + 1).choose j : ℤ)
      = (-1 : ℤ) ^ k * (m.choose k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      have hpas := Nat.choose_succ_succ m k
      have hpasZ : ((m + 1).choose (k + 1) : ℤ) = (m.choose k : ℤ) + (m.choose (k + 1) : ℤ) := by
        exact_mod_cast hpas
      rw [hpasZ]
      ring_nf

theorem alt_choose_five (r : ℕ) (hr : 1 ≤ r) :
    (∑ j ∈ Finset.range 6, (-1 : ℤ) ^ j * ((r).choose j : ℤ))
      = - ((r - 1).choose 5 : ℤ) := by
  have hid := alternating_sum_choose (r - 1) 5
  rw [show (r - 1 + 1) = r by omega] at hid
  rw [hid]
  norm_num

theorem kernel_le_indicator (r : ℕ) :
    (∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * (Nat.choose r j : ℝ))
      ≤ (if r = 0 then (1 : ℝ) else 0) := by
  by_cases hr : r = 0
  · subst hr
    simp [Finset.sum_range_succ]
  · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
    have hR : (∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * (Nat.choose r j : ℝ))
        = - ((r - 1).choose 5 : ℝ) := by
      have hZ := alt_choose_five r hr1
      have := congrArg (fun z : ℤ => (z : ℝ)) hZ
      push_cast at this
      simpa using this
    rw [hR, ite_eq_right (fun h => absurd h hr)]
    have : (0:ℝ) ≤ ((r - 1).choose 5 : ℝ) := Nat.cast_nonneg _
    linarith

/-- **The extraction lemma.** For any finite set with nonnegative weights, the weighted mass of
labels `r = 0` is at least the alternating binomial sum of the weighted moments. -/
theorem weighted_extraction {ι : Type*} (S : Finset ι) (w : ι → ℝ) (r : ι → ℕ)
    (hw : ∀ s ∈ S, 0 ≤ w s) :
    (∑ s ∈ S, if r s = 0 then w s else 0)
      ≥ ∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * ∑ s ∈ S, w s * (Nat.choose (r s) j : ℝ) := by
  have key : (∑ s ∈ S, w s * (∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * (Nat.choose (r s) j : ℝ)))
      = ∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * ∑ s ∈ S, w s * (Nat.choose (r s) j : ℝ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [← key]
  apply Finset.sum_le_sum
  intro s hs
  by_cases h0 : r s = 0
  · rw [h0]
    have : (∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
      simp [Finset.sum_range_succ]
    rw [this, mul_one]
    simp
  · have := kernel_le_indicator (r s)
    rw [ite_eq_right (fun h => absurd h h0)] at this
    have hm := mul_le_mul_of_nonneg_left this (hw s hs)
    rw [mul_zero] at hm
    simp only [ite_eq_right (fun h => absurd h h0)]
    exact hm/-! ## The error budget

The frontier's second claim, checked exactly: the quintic truncation of `e^{-2}` is `1/15`, while
the cubic truncation is `-1/3` — useless even with perfect moments. Five terms therefore buy a
positive budget of `1/15`, enough to absorb five absolute errors of `1/100`. -/

theorem quintic_truncation_exp_neg_two :
    (∑ j ∈ Finset.range 6, (-1 : ℝ) ^ j * (2 : ℝ) ^ j / (j.factorial : ℝ)) = 1/15 := by
  norm_num [Finset.sum_range_succ]

theorem cubic_truncation_exp_neg_two :
    (∑ j ∈ Finset.range 4, (-1 : ℝ) ^ j * (2 : ℝ) ^ j / (j.factorial : ℝ)) = -1/3 := by
  norm_num [Finset.sum_range_succ]


