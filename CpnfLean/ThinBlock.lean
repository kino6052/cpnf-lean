import Mathlib
import CpnfLean.PowerRefund

/-!
# CPNF — thin the block: kill squares and cubes, budget drops to X^(1/5)

The frontier's bold close-gap move. Restrict to `n ≡ 11 (mod 14)`. On this progression
neither `6n−1` nor `6n+1` can be a square or a cube (residue obstructions mod 3, 4, 7), so
every proper prime power on either side has exponent ≥ 5 (`thin_exponent_ge_five`).

Consequence (compiled here): `boxed_of_thin_slack` — cofinal thin-block signal excess gives
`WindowWitness`. The remaining step (`thinBad_le_baseBudget`, the injection that a given
prime base accounts for at most one row) is stated separately and proved in `ThinInjection.lean`.

All unconditional, no `sorry`.
-/

namespace CPNF


def thinBlock (X : ℕ) : Finset ℕ :=
  (blk X).filter (fun n => n % 14 = 11)

def thinSignal (X : ℕ) : Finset ℕ :=
  (thinBlock X).filter
    (fun n => PowerMember (twinLo n) ∧ PowerMember (twinHi n))

-- 1. Both square obstructions, simultaneously.
theorem thin_no_square {n : ℕ} (hn : n % 14 = 11) (a : ℕ) :
    a^2 ≠ twinLo n ∧ a^2 ≠ twinHi n := by
  have s3 : a^2 % 3 = 0 ∨ a^2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have h := Nat.mod_lt a (by decide : 0 < 3)
    interval_cases v : a % 3 <;> decide
  have s4 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by
    rw [Nat.pow_mod]
    have h := Nat.mod_lt a (by decide : 0 < 4)
    interval_cases v : a % 4 <;> decide
  unfold twinLo twinHi
  constructor <;> intro he <;> rw [he] at s3 s4 <;> omega

-- 2. Both cube obstructions, simultaneously.
theorem thin_no_cube {n : ℕ} (hn : n % 14 = 11) (a : ℕ) :
    a^3 ≠ twinLo n ∧ a^3 ≠ twinHi n := by
  have c7 : a^3 % 7 = 0 ∨ a^3 % 7 = 1 ∨ a^3 % 7 = 6 := by
    rw [Nat.pow_mod]
    have h := Nat.mod_lt a (by decide : 0 < 7)
    interval_cases v : a % 7 <;> decide
  unfold twinLo twinHi
  constructor <;> intro he <;> rw [he] at c7 <;> omega

-- 3. A proper-power certificate on either side starts at exponent five.
theorem thin_exponent_ge_five {n p e : ℕ}
    (hn : n % 14 = 11) (he : 2 ≤ e)
    (hm : p^e = twinLo n ∨ p^e = twinHi n) :
    5 ≤ e := by
  by_contra! h
  have sq := thin_no_square hn p
  have cu := thin_no_cube hn p
  have sq₂ := thin_no_square hn (p^2)
  have fourth : (p^2)^2 = p^4 := by ring
  rw [fourth] at sq₂
  interval_cases e <;> tauto





def thinBad (X : ℕ) : Finset ℕ :=
  (thinSignal X).filter (fun n =>
    HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n))

def baseBudget (B : ℕ) : Finset ℕ :=
  (Finset.range B).filter Nat.Prime





theorem boxed_of_thin_slack {K X : ℕ} (hK : K ≤ X)
    (hs : (thinBad X).card < (thinSignal X).card) :
    WindowWitness K := by
  classical
  have hout : ∃ n ∈ thinSignal X, n ∉ thinBad X := by
    by_contra h
    apply (not_lt_of_ge
      (Finset.card_le_card (show thinSignal X ⊆ thinBad X from by
        intro n hn
        by_contra hb
        exact h ⟨n, hn, hb⟩))) hs
  obtain ⟨n, hn, hb⟩ := hout
  have sig := (Finset.mem_filter.mp hn).2
  have hthin : n ∈ thinBlock X := (Finset.mem_filter.mp hn).1
  have hblk : n ∈ blk X := (Finset.mem_filter.mp hthin).1
  have hXn : X < n := (Finset.mem_Ioc.mp hblk).1
  have clean :
      ¬ (HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n)) :=
    fun h => hb (Finset.mem_filter.mpr ⟨hn, h⟩)
  have hp : Nat.Prime (twinLo n) :=
    sig.1.resolve_right (fun h => clean (Or.inl h))
  have hq : Nat.Prime (twinHi n) :=
    sig.2.resolve_right (fun h => clean (Or.inr h))
  obtain ⟨y, hy, hw, hsc⟩ :=
    window_witness_of_twin (by omega : 1 ≤ n) hp hq
  exact ⟨y, n, hy, by omega, by omega, hw, hsc⟩


end CPNF
