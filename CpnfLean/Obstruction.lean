import Mathlib
import CpnfLean.Wheel

/-!
# CPNF — the scale obstruction: overload lives in the last 16 levels

The frontier's unconditional restriction on the certificate. On a node of length `L ≥ 65536`,
the nine primes `{5,7,11,13,17,19,23,29,31}` already force the sum of the two column densities
below the wheel capacity, uniformly in the node's starting point:

  `a ≤ ρ·L + 512`,  `b ≤ ρ·L + 512`,  `c ≥ (33/35)·L − 2`,  with `ρ = Π (1−1/p) < 460/1000`.

Hence `a + b < c` for `L ≥ 65536`, so `forced = 0`. Positive overload therefore requires
`t − d ≤ 15`. No argument that produces overload on growing nodes can work, even if twins hold.

This file proves the two *numerical* certificates. The inclusion–exclusion proof that a marked
row avoids all nine primes (so each column obeys `hS`/`hT`) is the progression-counting step,
and is not yet compiled.

No `sorry`, no `axiom`.
-/

namespace CPNF


theorem nine_prime_density :
    (1 - 1/5 : ℚ) * (1 - 1/7) * (1 - 1/11) *
    (1 - 1/13) * (1 - 1/17) * (1 - 1/19) *
    (1 - 1/23) * (1 - 1/29) * (1 - 1/31) < 460/1000 := by
  norm_num

theorem forced_zero_of_nine_prime_bounds
    {S T U : Finset ℕ} {t d j : ℕ} {L : ℤ}
    (hL : 65536 ≤ L)
    (hS : 1000 * colCount S t d j ≤ 460 * L + 512000)
    (hT : 1000 * colCount T t d j ≤ 460 * L + 512000)
    (hU : 33 * L ≤ 35 * colCount U t d j + 70) :
    forced S T U t d j = 0 := by
  unfold forced
  apply max_eq_left
  omega

end CPNF
