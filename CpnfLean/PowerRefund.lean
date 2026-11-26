import Mathlib
import CpnfLean.PowerExcess

/-!
# CPNF — the power refund: tighten the budget to `error ∩ signal`

The bold chisel: the budget in `PowerExcess.lean` charged a row even when its *other* member
rules it out of the signal. Charge instead only the intersection
`chargedPowerRows = powerErrorRows ∩ powerPairRows`.

Then an explicit infinite family shows the old budget genuinely overcounts:
`6·nₖ + 1 = 11^(48k+2)` and `119 | 6·nₖ − 1` (with `119 = 7·17`). The upper member is a proper
prime power (so the row is an error row), but the lower member has two distinct prime factors
(so the row is *not* a signal row). Thus on the blocks `Xₖ = nₖ − 1` the charged set is a
*proper* subset of the error set.

Consequence: a **tie** `powerErrorRows ≤ powerPairRows` now suffices for a window witness,
where the earlier statement needed strict excess. Unconditional finite lemmas:
`refund_strict`, `refund_row_spec`, `refund_residue`; the tie theorem is conditional only on
that weak comparison.
-/

namespace CPNF


def chargedPowerRows (X : ℕ) : Finset ℕ :=
  powerErrorRows X ∩ powerPairRows X

theorem windowWitness_of_charged_excess {K X : ℕ} (hK : K ≤ X)
    (h : (chargedPowerRows X).card < (powerPairRows X).card) :
    WindowWitness K := by
  classical
  have hout : ∃ n ∈ powerPairRows X, n ∉ powerErrorRows X := by
    by_contra hnone
    have sub : powerPairRows X ⊆ chargedPowerRows X := by
      intro n hn
      apply Finset.mem_inter.mpr
      exact ⟨by
        by_contra he
        exact hnone ⟨n, hn, he⟩, hn⟩
    exact (not_lt_of_ge (Finset.card_le_card sub)) h
  obtain ⟨n, hn, he⟩ := hout
  have hb : n ∈ blk X := (Finset.mem_filter.mp hn).1
  have hs : PowerMember (twinLo n) ∧ PowerMember (twinHi n) :=
    (Finset.mem_filter.mp hn).2
  have clean : ¬ (HigherPrimePower (twinLo n) ∨
      HigherPrimePower (twinHi n)) :=
    fun bad => he (Finset.mem_filter.mpr ⟨hb, bad⟩)
  have hp : Nat.Prime (twinLo n) :=
    hs.1.resolve_right (fun bad => clean (Or.inl bad))
  have hq : Nat.Prime (twinHi n) :=
    hs.2.resolve_right (fun bad => clean (Or.inr bad))
  have hXn : X < n := (Finset.mem_Ioc.mp hb).1
  have hn1 : 1 ≤ n := by omega
  obtain ⟨y, hy, hw, hsc⟩ := window_witness_of_twin hn1 hp hq
  exact ⟨y, n, hy, hn1, by omega, hw, hsc⟩



private theorem no_power_of_seven_seventeen {m : ℕ}
    (h7 : 7 ∣ m) (h17 : 17 ∣ m) : ¬ PowerMember m := by
  intro hm
  rcases hm with hp | hh
  · have ha := hp.eq_one_or_self_of_dvd 7 h7
    have hb := hp.eq_one_or_self_of_dvd 17 h17
    omega
  · obtain ⟨p, _, hp, e, _, he⟩ := hh
    rw [← he] at h7 h17
    have ha : 7 ∣ p := (by decide : Nat.Prime 7).dvd_of_dvd_pow h7
    have hb : 17 ∣ p := (by decide : Nat.Prime 17).dvd_of_dvd_pow h17
    have ha' := hp.eq_one_or_self_of_dvd 7 ha
    have hb' := hp.eq_one_or_self_of_dvd 17 hb
    omega

def refundUpper (k : ℕ) : ℕ := 11 ^ (48 * k + 2)
def refundRow (k : ℕ) : ℕ := (refundUpper k - 1) / 6
def refundBlock (k : ℕ) : ℕ := refundRow k - 1

private theorem refund_residue (k : ℕ) : refundUpper k % 714 = 121 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have step : refundUpper (k+1) = refundUpper k * 11^48 := by
      unfold refundUpper
      rw [show 48 * (k+1) + 2 = (48*k+2) + 48 by omega, pow_add]
    rw [step, Nat.mul_mod, ih,
      show (11:ℕ)^48 % 714 = 1 by decide]

private theorem refund_growth (e : ℕ) : e + 1 ≤ 11^e := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ]
    omega

theorem refund_block_ge (k : ℕ) : k ≤ refundBlock k := by
  have hg : 48*k+2+1 ≤ refundUpper k := refund_growth _
  unfold refundBlock refundRow
  omega

theorem refund_row_spec (k : ℕ) :
    refundRow k ∈ powerErrorRows (refundBlock k) ∧
    refundRow k ∉ powerPairRows (refundBlock k) := by
  have hr := refund_residue k
  have hi : twinHi (refundRow k) = refundUpper k := by
    unfold twinHi refundRow
    omega
  have hl : twinLo (refundRow k) = refundUpper k - 2 := by
    unfold twinLo refundRow
    omega
  have h7 : 7 ∣ twinLo (refundRow k) := by rw [hl]; omega
  have h17 : 17 ∣ twinLo (refundRow k) := by rw [hl]; omega
  have hrow : 2 ≤ refundRow k := by unfold refundRow; omega
  have hblk : refundRow k ∈ blk (refundBlock k) := by
    apply Finset.mem_Ioc.mpr
    unfold refundBlock
    constructor <;> omega
  have hh : HigherPrimePower (twinHi (refundRow k)) := by
    rw [hi]
    have hg : 48*k+2+1 ≤ refundUpper k := refund_growth _
    exact ⟨11, Finset.mem_Icc.mpr ⟨by decide, by omega⟩,
      by decide, 48*k+2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  refine ⟨Finset.mem_filter.mpr ⟨hblk, Or.inr hh⟩, ?_⟩
  intro hs
  have hm : PowerMember (twinLo (refundRow k)) :=
    ((Finset.mem_filter.mp hs).2).1
  exact no_power_of_seven_seventeen h7 h17 hm



theorem refund_strict (k : ℕ) :
    (chargedPowerRows (refundBlock k)).card <
      (powerErrorRows (refundBlock k)).card := by
  obtain ⟨he, hs⟩ := refund_row_spec k
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fun n hn => (Finset.mem_inter.mp hn).1, ?_⟩
  intro eq
  have hc : refundRow k ∈ chargedPowerRows (refundBlock k) := eq ▸ he
  exact hs (Finset.mem_inter.mp hc).2

theorem windowWitness_of_refund_tie {k : ℕ}
    (h : (powerErrorRows (refundBlock k)).card ≤
         (powerPairRows (refundBlock k)).card) :
    WindowWitness k :=
  windowWitness_of_charged_excess (refund_block_ge k)
    (lt_of_lt_of_le (refund_strict k) h)


end CPNF
