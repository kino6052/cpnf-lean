import Mathlib
import CpnfLean.Overload

open ArithmeticFunction

/-!
# CPNF — the one missing arithmetic input

Everything else is a theorem. This file names exactly what is not.

Split the divisor sum on `p + 2` at `x ^ (1/3)`. The **small-divisor** part is unconditional
Bombieri–Vinogradov: one prime in a reduced residue class `-2 mod d`, `d <= x^(1/3)`, main term
`(2*C2 + o(1)) * x` with `C2 = ∏_{l>2} (1 - 1/(l-1)^2) ~ 0.6602`. Since `C2 >= 9/16`, the main
term beats `x/8`.

The **large-divisor** part is `largeDivisorTail`. The complete sum telescopes to

  `sum_{d | p+2} mu(d) log(Y/d) = Lambda(p+2)`,

so `A(x) + B(x) = sum_{x<p<=2x} log p * Lambda(p+2)`. Proper prime powers contribute `o(x)`.
Hence if `B` is never very negative on a cofinal sequence, `p+2` is prime infinitely often, and
`CofinalNodeOverload` follows with `d = s`, `j = n - 2^s - 1` at width 1.

The floor below is *weaker* than the true asymptotics and still suffices: the margin below
`2*C2` is what matters, not a square-root cancellation rate. It is not proved here, and it is
not claimed to be easy — it is the honest location of the gap.

No `sorry`, no `axiom`: the missing input is a **named hypothesis**, not a gap in a proof.
-/

namespace CPNF
open scoped BigOperators
noncomputable def largeDivisorTail (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc x (2*x)).filter Nat.Prime,
    Real.log (p : ℝ) *
      ∑ d ∈ (p+2).divisors.filter (fun d => x < d^3),
        (ArithmeticFunction.moebius d : ℝ) *
          Real.log (((2*x+2 : ℕ) : ℝ) / (d : ℝ))
def CofinalLargeDivisorFloor : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
    -(2^t : ℝ) ≤ largeDivisorTail (2^t)

/-- The telescoping identity behind the reduction: the complete divisor sum on `m` is `Λ m`.

`log m = Σ_{d|m} Λ d` is von Mangoldt's identity, and Möbius inversion turns it into
`Λ m = Σ_{d|m} μ d · log(m/d)`. So the *truncated* sums `A` (small divisors) and `B` (large
divisors) add up to something that is nonnegative and mostly zero: it counts prime powers.
That is why the reduction has no unspecified truncation error. -/
theorem vonMangoldt_eq_sum_moebius_mul_log (m : ℕ) (hm : 0 < m) :
    (Λ m : ℝ) = ∑ d ∈ m.divisors, (moebius d : ℝ) * Real.log ((m : ℝ) / (d : ℝ)) := by
  have hinv := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun d : ℕ => (Λ d : ℝ))
    (g := fun n : ℕ => if n = 0 then 0 else Real.log (n : ℝ))).mp
    (fun n hn => by
      rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hn)]
      exact @vonMangoldt_sum n) m hm
  rw [← hinv]
  rw [Nat.sum_divisorsAntidiagonal
      (f := fun a b : ℕ => (moebius a : ℝ) * (if b = 0 then 0 else Real.log (b : ℝ)))]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hdvd hm)
  have hle : d ≤ m := Nat.le_of_dvd hm hdvd
  have hne : m / d ≠ 0 := by
    intro h
    have := Nat.div_eq_zero_iff.mp h
    omega
  rw [ite_eq_right hne, Nat.cast_div hdvd (by exact_mod_cast hd0)]

end CPNF
