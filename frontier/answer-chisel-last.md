The budget in `PowerExcess.lean` charges a row even when its *other* member rules it out of the signal. There is an explicit infinite family where we can refund that charge:
\[
6n_k+1=11^{48k+2},\qquad 119\mid 6n_k-1,\qquad 119=7\cdot17.
\]
The upper member puts \(n_k\) in `powerErrorRows`; the two distinct prime divisors of the lower member keep \(n_k\) out of `powerPairRows`. Thus on the blocks \(X_k=n_k-1\), **even a tie in the original ledger suffices**. The signal is unchanged.

Here is a single proposed file `CpnfLean/PowerRefund.lean`, in three consecutive pieces. I have not run Lean here; the check command is `lake env lean CpnfLean/PowerRefund.lean`. No RH or GRH declaration is needed.

### 1. A refund valid on any block

**Status:** unconditional finite implication. **Builds on:** `powerPairRows`, `powerErrorRows`, and `window_witness_of_twin`. Instead of charging all error rows, charge their intersection with the signal. If that intersection is strictly smaller than the signal, some signal row has neither member a higher prime power. This reuses the extraction argument of `windowWitness_of_power_excess`, not its stronger hypothesis.

```lean
import CpnfLean.PowerExcess

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
```

### 2. Construct a charged-but-not-signal row arbitrarily far out

**Status:** unconditional, including the strict budget saving below. **Builds on:** the actual bounded-exponent definition `HigherPrimePower` from `PowerExcess`. The useful finite computation is \(11^{48}\equiv1\pmod{714}\), with \(714=6\cdot119\). Induction then keeps the upper member congruent to \(121\) modulo \(714\). One congruence proves both that the row index is integral and that its lower member is divisible by 7 and 17. The growth lemma also supplies the exponent bound required by the project definition.

```lean
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
    decide

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
```

### 3. Strict budget saving, and the tie theorem

**Status:** `refund_strict` is unconditional for every `k`. `windowWitness_of_refund_tie` is conditional only on the displayed weak count comparison. **Builds on:** the two pieces above. The constructed row witnesses that the charged set is a *proper* subset of the old error set. The strict inequality needed for extraction therefore comes from the budget side, not from an assumed strict signal estimate.

```lean
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
```

For a small numerical check, `k = 0` gives `refundBlock 0 = 19`, `refundRow 0 = 20`, and the pair is \((119,121)=(7\cdot17,11^2)\). `refund_block_ge` is what upgrades this from one example to a strict saving on a cofinal sequence of blocks. The result does **not** assume or prove that the weak comparison holds on that sequence; it proves that the old budget overcounts there, with a named row witnessing each overcount.
