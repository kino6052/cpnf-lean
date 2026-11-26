**Idea.** Change the rows before changing the estimate. Keep the block \((X,2X]\), but retain only \(n\equiv11\pmod {14}\). On this progression **neither** \(6n-1\) **nor** \(6n+1\) can be a square or a cube. Yet the two linear forms remain locally admissible. Consequently, every proper prime power on either side has exponent at least **five**. There is a second saving: throughout the entire block, a given prime base can account for at most **one** error row, even counting both sides. The result is a conditional route with an \(X^{1/5}\)-scale error budget instead of a square-root-scale budget. It uses the alternate endpoint `∀ K, WindowWitness K`, not a tie on the original unfiltered blocks. The fixed-shift lower bound is still an open hypothesis; the reduction in its required scale is unconditional.

### 1. The first three lemmas

Here is the file prefix I would try tonight. These are proof scripts, not a reported build.

```lean
import CpnfLean.PowerRefund

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

end CPNF
```

The choice of `11` is deliberate. Modulo \(7\) the members are \(2,4\), whereas cubes are \(0,1,6\). Modulo \(3\) the lower member is \(2\); modulo \(4\) the upper is \(3\). There is no fixed prime divisor obstruction introduced by the restriction: writing \(n=14j+11\) gives \(84j+65,84j+67\). The primes dividing \(84\) divide neither constant, and any other prime excludes at most two classes of \(j\), fewer than its modulus.

### 2. The new counting step: one base, one row, *across both signs*

Use the following two finite sets. `B` is an integer cutoff, not a real fifth root.

```lean
namespace CPNF

def thinBad (X : ℕ) : Finset ℕ :=
  (thinSignal X).filter (fun n =>
    HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n))

def baseBudget (B : ℕ) : Finset ℕ :=
  (Finset.range B).filter Nat.Prime

end CPNF
```

The next unconditional theorem signature is:

```lean
theorem thinBad_le_baseBudget {X B : ℕ}
    (hB : 12 * X + 1 < B^5) :
    (thinBad X).card ≤ (baseBudget B).card
```

**Proof.** For each `n ∈ thinBad X`, choose a proper-power certificate, preferring the lower side if both have certificates. Write its value as \(v=p^e\). The first three lemmas and block membership give
\[
             p^5\le v\le12X+1<B^5.
\]
So send the row to \(p\in\texttt{baseBudget B}\). To prove injectivity, the important bound is the *lower* endpoint: every member value under consideration is at least \(6X+5\). Two distinct powers of the same prime, ordered \(v<w\), satisfy \(2v\le w\). This contradicts
\[
             w\le12X+1<2(6X+5)\le2v .
\]
Thus a shared base gives a shared value. A lower value cannot equal an upper value, by reduction modulo \(6\); within either side the value determines \(n\). This proves injectivity. In Lean the final count is `Finset.card_le_card_of_injOn`; the only power-gap fact needed is `pow_add` with the larger exponent written as `e + (d + 1)`.

In particular there is **no sum over exponents, no logarithmic loss for that sum, and no factor of two for the signs**. Taking \(B\) to be the least natural number with \(12X+1<B^5\) bounds the bad signal by the number of primes strictly below \(B\).

### 3. Conditional endpoint and exact hypothesis

The extraction step does not require an estimate:

```lean
namespace CPNF

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
```

The **exact** hypothesis for this filtered extraction is cofinal `thinBad < thinSignal`. It just says a clean signal survives. The point of the base injection is to give a different, **signal-only analytic target** with an independently calculable threshold. With `thinBad_le_baseBudget` in scope, the rest of that route is:

```lean
namespace CPNF

theorem boxed_of_fifth_root_signal
    (H : ∀ K : ℕ, ∃ X B : ℕ, K ≤ X ∧ 12*X+1 < B^5 ∧
      (baseBudget B).card < (thinSignal X).card) :
    ∀ K : ℕ, WindowWitness K := by
  intro K
  obtain ⟨X, B, hK, hB, hs⟩ := H K
  exact boxed_of_thin_slack hK
    (lt_of_le_of_lt (thinBad_le_baseBudget hB) hs)

end CPNF
```

**What would discharge `H`?** For example, for any fixed \(\epsilon>0\), an unweighted lower bound \(|\texttt{thinSignal}\ X|\ge X^{1/5+\epsilon}\) on arbitrarily large blocks would do. It need not identify a single exponent-one row, need not hold on the lacunary `refundBlock`s, and need not approach a Hardy–Littlewood asymptotic. It **does** need to count the two forms at the same input. A one-variable prime number theorem, with or without an RH error term, is not that estimate.

### 4. Where I would push next

The fifth root is not intrinsic. For example, to eliminate fifth powers too, impose \(n\equiv6\pmod {11}\) in addition to \(n\equiv11\pmod {14}\). Then \(6n-1,6n+1\equiv2,4\pmod {11}\), while fifth powers modulo \(11\) are \(0,1,10\). Exponent six is already excluded because it is even. **The same base injection now has a seventh-root budget.** This extension costs just one CRT class and a finite residue-table lemma; it does not require a new counting argument.

More generally, for a fixed odd prime exponent \(\ell\), choose a fresh prime \(q\equiv1\pmod\ell\). The set of \(\ell\)-th powers modulo \(q\), including zero, has size \(1+(q-1)/\ell\). For sufficiently large \(q\) the two translated forbidden sets together have size less than \(q\), so one can choose a class avoiding powers on both sides. CRT combines any **fixed finite** list of these restrictions. This drives the power-error exponent as low as desired on a corresponding fixed progression. It does not justify letting the modulus grow with \(X\) inside a nonuniform correlation estimate.

That is the proposed improvement: **remove exponents locally, then charge bases globally**. It makes the proper-power budget arbitrarily small in polynomial scale. The part not proved here is cofinal fixed-shift signal above that smaller budget; no unconditional twin-prime conclusion follows without it.
