import Mathlib
import CpnfLean.Overload

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
end CPNF
