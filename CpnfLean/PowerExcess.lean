import Mathlib
import CpnfLean.Ladder
import CpnfLean.Coverage

/-!
# CPNF — the power-excess route to the boxed condition (post-RH)

The frontier's answer to "use RH": **RH does not supply the needed fixed-shift correlation.**
So this file states the correlation directly, as a finite, unweighted, one-sided condition:

* `powerPairRows X` — rows of `(X, 2X]` where both members are prime powers (exponent ≥ 1);
* `powerErrorRows X` — rows where either member is a *proper* prime power (exponent ≥ 2).

`windowWitness_of_power_excess`: signal > budget on a block forces a twin row, hence a
`WindowWitness K`. `boxed_of_cofinal_power_excess`: cofinal signal-excess gives the boxed
condition, hence (via `windowWitness_iff_oftenDirect`) twin primes.

The honest wall: this is fixed-shift **correlation**, the second moment — the parity problem
is not bypassed, and neither RH nor a finer top-band count supplies this input. This file is
a conditional (no `sorry`), exactly as the frontier specified.
-/

namespace CPNF


/-- `m` is a proper prime power `p^e` with `p` prime and `e ≥ 2`. -/
def HigherPrimePower (m : ℕ) : Prop :=
  ∃ p ∈ Finset.Icc 2 m, Nat.Prime p ∧ ∃ e ∈ Finset.Icc 2 m, p ^ e = m

/-- `m` is prime or a higher prime power. -/
def PowerMember (m : ℕ) : Prop := Nat.Prime m ∨ HigherPrimePower m

instance decHigherPrimePower (m : ℕ) : Decidable (HigherPrimePower m) := by
  unfold HigherPrimePower
  infer_instance

instance decPowerMember (m : ℕ) : Decidable (PowerMember m) := by
  unfold PowerMember
  infer_instance

/-- Rows of `(X, 2X]` where both members are prime powers (allowing exponent 1). -/
def powerPairRows (X : ℕ) : Finset ℕ :=
  (blk X).filter (fun n => PowerMember (twinLo n) ∧ PowerMember (twinHi n))

/-- Rows where either member is a proper prime power. -/
def powerErrorRows (X : ℕ) : Finset ℕ :=
  (blk X).filter (fun n => HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n))

/-- **Signal exceeding budget forces a twin row.** A signal row outside the error set has
    both members prime, hence is a twin index. -/
theorem windowWitness_of_power_excess {K X : ℕ} (hK : K ≤ X)
    (hexcess : (powerErrorRows X).card < (powerPairRows X).card) :
    WindowWitness K := by
  classical
  have hout : ∃ n ∈ powerPairRows X, n ∉ powerErrorRows X := by
    by_contra h
    have hsub : powerPairRows X ⊆ powerErrorRows X := by
      intro n hn
      exact not_not.mp (fun hnot => h ⟨n, hn, hnot⟩)
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hexcess
  obtain ⟨n, hn, hnot⟩ := hout
  have hnS : PowerMember (twinLo n) ∧ PowerMember (twinHi n) :=
    Finset.mem_filter.mp hn |>.2
  have hclean : ¬ (HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n)) := by
    intro hc
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mp hn |>.1, hc⟩)
  have member_prime (m : ℕ) (hm : PowerMember m) (hc : ¬ HigherPrimePower m) : Nat.Prime m := by
    rcases hm with hp | hpp
    · exact hp
    · exact False.elim (hc hpp)
  have hp := member_prime (twinLo n) hnS.1 (fun h => hclean (Or.inl h))
  have hq := member_prime (twinHi n) hnS.2 (fun h => hclean (Or.inr h))
  have hb : n ∈ blk X := Finset.mem_filter.mp hn |>.1
  have hXn : X < n := (Finset.mem_Ioc.mp hb).1
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h, hh, hw, hs⟩ := window_witness_of_twin hn1 hp hq
  exact ⟨h, n, hh, hn1, by omega, hw, hs⟩

/-- **The boxed condition from cofinal power excess.** If signal exceeds budget on blocks
    arbitrarily far out, then `WindowWitness` holds for every `K`. -/
theorem boxed_of_cofinal_power_excess
    (H : ∀ K : ℕ, ∃ X : ℕ, K ≤ X ∧
      (powerErrorRows X).card < (powerPairRows X).card) :
    ∀ K : ℕ, WindowWitness K := by
  intro K
  obtain ⟨X, hK, he⟩ := H K
  exact windowWitness_of_power_excess hK he

end CPNF
