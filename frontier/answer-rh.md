**Route 2: use a finite prime-power correlation at shift two.** RH is not known to supply this correlation; neither GRH nor ordinary Elliott–Halberstam is known to suffice. The conditional theorem below does not need RH at all, so its validity does not depend on the reported Lean release.

Here is the distribution input I would target. On the block `blk X = (X, 2*X]`, count two things:

* **Signal:** rows on which both members are prime powers, allowing exponent one.
* **Budget:** rows on which *either* member is a proper prime power, meaning \(p^e\) with \(p\) prime and \(e\ge2\). Do **not** test the other member.

Ask that **signal exceed budget on cofinally many blocks**. This is a one-sided, finite, unweighted version of a Hardy–Littlewood prime-pair correlation lower bound. It asks for no density constant and no estimate on every block. Its useful feature is that the budget can be bounded by enumerating individual powers, without knowing anything about prime pairs.

### Lean statement and proof

The following is proposed source against your interfaces, not a claim that I ran your checkout.

```lean
import CpnfLean.Ladder

namespace CPNF

-- Bounded searches throughout; no decidability axioms for number-theoretic predicates.
def higherPrimePower (m : ℕ) : Bool :=
  (Finset.Icc 2 m).any fun p =>
    decide (Nat.Prime p) &&
      (Finset.Icc 2 m).any (fun e => decide (p ^ e = m))

def powerMember (m : ℕ) : Bool :=
  decide (Nat.Prime m) || higherPrimePower m

def powerPairRows (X : ℕ) : Finset ℕ :=
  (blk X).filter fun n =>
    powerMember (twinLo n) = true ∧ powerMember (twinHi n) = true

def powerErrorRows (X : ℕ) : Finset ℕ :=
  (blk X).filter fun n =>
    higherPrimePower (twinLo n) = true ∨
    higherPrimePower (twinHi n) = true

theorem windowWitness_of_power_excess {K X : ℕ} (hK : K ≤ X)
    (hexcess : (powerErrorRows X).card < (powerPairRows X).card) :
    WindowWitness K := by
  classical
  have hout : ∃ n ∈ powerPairRows X, n ∉ powerErrorRows X := by
    by_contra! h
    exact (Nat.not_lt_of_ge (Finset.card_le_card h)) hexcess
  obtain ⟨n, hn, hnot⟩ := hout
  obtain ⟨hb, hlo, hhi⟩ := Finset.mem_filter.mp hn
  have hclean :
      ¬ (higherPrimePower (twinLo n) = true ∨
         higherPrimePower (twinHi n) = true) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hb, h⟩)
  have member_prime (m : ℕ) (h : powerMember m = true)
      (hc : ¬ higherPrimePower m = true) : Nat.Prime m := by
    cases he : higherPrimePower m <;> simp_all [powerMember]
  have hp := member_prime _ hlo (fun h => hclean (Or.inl h))
  have hq := member_prime _ hhi (fun h => hclean (Or.inr h))
  have hXn : X < n := (Finset.mem_Ioc.mp hb).1
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h, hh, hw, hs⟩ := window_witness_of_twin hn1 hp hq
  exact ⟨h, n, hh, hn1, by omega, hw, hs⟩

theorem boxed_of_cofinal_power_excess
    (H : ∀ K : ℕ, ∃ X : ℕ, K ≤ X ∧
      (powerErrorRows X).card < (powerPairRows X).card) :
    ∀ K : ℕ, WindowWitness K := by
  intro K
  obtain ⟨X, hK, he⟩ := H K
  exact windowWitness_of_power_excess hK he

end CPNF
```

**Proof idea.** If every signal row belonged to the error set, monotonicity of `Finset.card` would contradict strict excess. On a signal row outside the error set, each member is prime or a higher prime power, and neither is a higher prime power. Apply your compiled `window_witness_of_twin` to those two primality proofs. This produces the actual height `h` and its strict `score` inequality, not merely a positive block count. Your `windowWitness_iff_oftenDirect` then gives `OftenDirect` if desired.

### How much distribution is actually being requested?

There is a simple correlation-free ceiling for the budget. Put \(B=12X+1\). To list every possible contaminant it suffices to list
\[
 p^e,\qquad 2\le p\le\operatorname{Nat.sqrt}(B),\qquad
 2\le e\le\operatorname{Nat.log}(2,B),\qquad p^e\le B .
\]
Indeed \(p^2\le p^e\le B\) and \(2^e\le B\). Each listed value occurs on **at most one row across both signs**: its residue modulo six determines the sign, and then its value determines the index. Thus even `Nat.sqrt B * Nat.log 2 B` is a valid, deliberately loose integer budget. The code uses the smaller actual error count; it does not need a formalization of this ceiling.

There is also a precise minimality distinction. Write \(S\) for the signal set and \(E\) for the error set. The **exact** threshold is \(|S|>|S\cap E|\): in fact \(S\setminus E\) consists exactly of the twin rows. But that threshold is just a reformulation. The proposed input \(|S|>|E|\) is sufficient, **not claimed necessary**. It buys something specific for the extra strength: the entire quantity on the right is a one-member error budget. The open obligation is a lower bound on the left, not an estimate hidden in the definition of the error.

**The wall is fixed-shift correlation, not a missing value of the Elliott–Halberstam level.** This route bypasses the top-band inequality; it does not bypass the parity problem. And in the existing route, even supplying `210 * U ≤ 192 * L + 60480 * k` together with `8064 * k ≤ L` only proves that some fraction is **unhit by the top band**. It does not prove that fraction contains a passing row. Your compiled `classBlock 100 128 126 = {126}` example isolates precisely the pointwise failure: the row is unhit and belongs to `midB`. The new conditional puts the missing information where it belongs—on two members of the **same** row—and neither an RH axiom nor a finer count of band primes supplies it.
