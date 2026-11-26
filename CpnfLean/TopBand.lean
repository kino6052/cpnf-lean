import Mathlib
import CpnfLean.Head
import CpnfLean.Correspondence
import CpnfLean.Ladder
import CpnfLean.Wheel

/-!
# CPNF — top-band exclusion (rung 3 of the unconditional ladder)

The frontier's correction: the top band gives an **upper** bound on the number of rows hit
(`bandHits`), and the `20` argument gives a **lower** bound on the *complement* `L - U`.
The forced quantity is `L ≤ 20 * (L - U)`, not `U ≥ L/20`.

Two counterexamples (compiled by `native_decide`) refute the two wrong claims from earlier
drafts: (i) a single top-band prime can hit 19 rows of a class, so "≤ 2 hits" is false;
(ii) a nonempty class can be rough and nonpassing with **no** top-band hit.

The pointwise bridge is `middle_or_pass_of_not_top`, and the arithmetic is
`top_exclusion_arithmetic` (pure `omega`).
-/

namespace CPNF

/-- Rows of the block `(X, 2X]` in the residue class `n % M = r`. -/
def classBlock (X M r : ℕ) : Finset ℕ :=
  (blk X).filter (fun n => n % M = r)

/-- Primes in the band `(√X, √(12X+1)]`. -/
def bandPrimes (X : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt X) (Nat.sqrt (12 * X + 1))).filter Nat.Prime

/-- Rows of a class hit by some band prime. -/
def bandHits (X M r : ℕ) : Finset ℕ :=
  (classBlock X M r).filter
    (fun n => ∃ q ∈ bandPrimes X, q ∣ twinLo n ∨ q ∣ twinHi n)

/-- **Counterexample (i):** one top-band prime, one residue class, nineteen hits. -/
example :
    11 ∈ bandPrimes 100 ∧
    ((classBlock 100 1 0).filter
      (fun n => 11 ∣ twinLo n ∨ 11 ∣ twinHi n)).card = 19 := by
  native_decide

/-- **Counterexample (ii):** a nonempty class is rough and nonpassing, with no top-band hit. -/
example :
    classBlock 100 128 126 = {126} ∧
    126 ∈ midB 100 3 ∧ score 126 ≠ twinLo 126 ∧
    (∀ q ∈ bandPrimes 100, Nat.Coprime q 128) ∧
    bandHits 100 128 126 = ∅ := by
  native_decide

/-- **The pointwise bridge.** A rough row that is not in the top band is either below-scale
    or passing. Uses `rough_split`, not `local_slack_iff`. -/
theorem middle_or_pass_of_not_top (X z n : ℕ)
    (hr : n ∈ rough X z) (ht : n ∉ midT X z) :
    n ∈ midB X z ∨ score n = twinLo n := by
  rcases rough_split X z n hr with hp | hb | htop
  · exact Or.inr (Finset.mem_filter.mp hp).2
  · exact Or.inl hb
  · exact False.elim (ht htop)

/-- **The arithmetic.** If the hit count `U` is bounded by the wheel, and the class is large
    enough, then at least a twentieth of the class is *unhit*. Pure `omega`. -/
theorem top_exclusion_arithmetic (k L U : ℕ)
    (hcount : 210 * U ≤ 192 * L + 60480 * k)
    (hsize : 8064 * k ≤ L) :
    20 * U ≤ 19 * L ∧ L ≤ 20 * (L - U) := by
  omega

end CPNF
