I would prove the bound on `Ioc u v` first, by deleting one prime at a time. The key is to induct on a **two-sided discrepancy**, not on an upper bound. The recurrence then gives an error of \(2^9-1=511\), and you never have to construct a powerset or invoke `Finset.prod_sub`.

There is an interface distinction worth preserving: `loMark_no_nine_dvd` says `¬ p ∣ twinLo n`, **not** `¬ p ∣ n`. So the literal `range L` theorem about divisibility of the row index is true, but is not by itself the column theorem. A single translation of the interval handles both columns below.

### Statements

Here are the Lean interfaces I would use, inside `namespace CPNF`. The proof below is a proof sketch with Lean fragments, not a claimed v4.36.0 compilation.

```lean
def sieveRho (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P, (1 - 1 / (p : ℚ))

def liveIoc (P : Finset ℕ) (u v : ℕ) : Finset ℕ :=
  (Finset.Ioc u v).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)
```

The helper theorem to prove is:

```lean
-- sieve_discrepancy
∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
  ∀ u v : ℕ, u ≤ v →
    |((liveIoc P u v).card : ℚ) -
      sieveRho P * ((v : ℚ) - (u : ℚ))| ≤
    (2 : ℚ)^P.card - 1
```

The literal public lemma requested is:

```lean
-- nine_range_le
∀ {A : Finset ℕ} {L : ℕ},
  A ⊆ Finset.range L →
  (∀ n ∈ A, ∀ p ∈ ninePrimes, ¬ p ∣ n) →
  (A.card : ℚ) ≤ sieveRho ninePrimes * (L : ℚ) + 512
```

For the marks, the useful public interface is instead:

```lean
-- nine_column_le
∀ {A : Finset ℕ} {u L : ℕ} (f : ℕ → ℕ),
  A ⊆ Finset.Ioc u (u + L) →
  (∀ n ∈ A, ∀ p ∈ ninePrimes, ¬ p ∣ f n) →
  (∃ s : ℕ, ∀ n ∈ A, ∀ p ∈ ninePrimes, p ∣ n + s → p ∣ f n) →
  (A.card : ℚ) ≤ sieveRho ninePrimes * (L : ℚ) + 512
```

The shift premise needs only the displayed implication. In particular you do not need to formalize an inverse in `ZMod` or prove a CRT bijection.

### 1. The exact counting step

Fix `p ∉ P` with `p` prime and all members of `P` prime. Write `S := liveIoc P u v`. Prove the **natural-number addition identity**

\[
|\operatorname{liveIoc}(\operatorname{insert} p P,u,v)|
+|\operatorname{liveIoc}(P,u/p,v/p)|=|S|.
\]

There are just two finset obligations:

1. Partition `S` into `S.filter (fun n => ¬ p ∣ n)` and `S.filter (fun n => p ∣ n)`. The first equals `liveIoc (insert p P) u v` by `ext n; simp [liveIoc]; tauto` (or unpack `Finset.mem_filter` explicitly). The filters are disjoint and have union `S`, both by membership. Apply `Finset.card_union_of_disjoint`.
2. Use `Finset.card_bij` from `liveIoc P (u/p) (v/p)` **to** the second filter, with map `fun k _ => k*p`. The endpoint conversion for either `w := u` or `w := v` is precisely
   ```lean
   have ep (k w : ℕ) : k ≤ w / p ↔ k * p ≤ w :=
     Nat.le_div_iff_mul_le hp.pos
   ```
   Negate `ep` for the strict lower endpoint. For `q ∈ P`, `q ∣ k*p ↔ q ∣ k`: use `(hq.dvd_mul).mp` and exclude `q ∣ p` by `hp.eq_one_or_self_of_dvd q`, `hq.ne_one`, and `p ∉ P`. This proves preservation of the filter in both directions. Injectivity is cancellation by `hp.pos`. For surjectivity unpack `p ∣ n` as `⟨k, hk⟩` and commute the factors in `hk`.

This step is inclusion–exclusion in recursive form: the second summand counts **exactly** the previously surviving rows removed by `p`. It is not an estimate on a union.

### 2. The only rounding lemma

For \(0<p\), put \(D=v-u\) and \(D'=\lfloor v/p\rfloor-\lfloor u/p\rfloor\), taking both **differences in `ℚ`**. Then
\[
                    |D/p-D'|\le 1 .
\]
The two endpoint remainders are subtracted, not added; this is why there is only one unit of rounding per insertion. Here is the Lean fragment I would isolate:

```lean
private lemma div_width_err (u v p : ℕ) (hp : 0 < p) :
    |((v : ℚ) - (u : ℚ)) / (p : ℚ) -
      ((↑(v / p) : ℚ) - (↑(u / p) : ℚ))| ≤ 1 := by
  have decomp (w : ℕ) :
      (p : ℚ) * (↑(w / p) : ℚ) + (↑(w % p) : ℚ) = (w : ℚ) := by
    exact_mod_cast Nat.div_add_mod w p
  have small (w : ℕ) : (↑(w % p) : ℚ) < (p : ℚ) := by
    exact_mod_cast Nat.mod_lt w hp
  have pos : (0 : ℚ) < p := by exact_mod_cast hp
  have eqn :
      ((v : ℚ) - (u : ℚ)) / p -
        ((↑(v / p) : ℚ) - (↑(u / p) : ℚ)) =
      ((↑(v % p) : ℚ) - (↑(u % p) : ℚ)) / p := by
    field_simp [ne_of_gt pos] <;> linarith only [decomp v, decomp u]
  rw [eqn, abs_le]
  constructor
  · apply (le_div_iff₀ pos).2
    linarith [small u, (show (0 : ℚ) ≤ ↑(v % p) by positivity)]
  · apply (div_le_iff₀ pos).2
    linarith [small v, (show (0 : ℚ) ≤ ↑(u % p) by positivity)]
```

Keep the casts **outside** `w / p` in `decomp`: that quotient must be natural division. In contrast, the division of the width on the left of `eqn` must be rational division.

### 3. The discrepancy induction

Induct on `P` **before introducing `u v`**, since the second invocation of the IH is on different endpoints. At `∅`, `liveIoc ∅ u v = Finset.Ioc u v`; use `Nat.card_Ioc` and `Nat.cast_sub huv`. The discrepancy is zero.

For the insertion step let \(r=\texttt{sieveRho P}\), \(B=2^{|P|}-1\). Prove \(0\le r\le1\) separately by `Finset.induction_on` and `Finset.prod_insert`: for a prime \(q\), `hq.two_le` gives \(0\le1-1/q\le1\). Denote the two old discrepancies by
\[
e=|S|-rD,\qquad e'=|\operatorname{liveIoc}(P,u/p,v/p)|-rD'.
\]
Here the bars on finsets denote cardinality. Apply the IH at `u v huv` and at `u/p, v/p` using `Nat.div_le_div_right huv`. It gives \(|e|,|e'|\le B\).

After casting the addition identity of step 1 to `ℚ`, the new **signed** discrepancy is exactly
\[
                    e-e' + r(D/p-D').
\]
For Lean, rewrite `sieveRho (insert p P)` by `Finset.prod_insert`, replace the new cardinality by the difference of the old two using the cast identity, then `ring` (`simp only [div_eq_mul_inv]` first if needed). The estimate now has no finsets in it:

```lean
private lemma err_step {e e' r z B : ℚ}
    (he : |e| ≤ B) (he' : |e'| ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hz : |z| ≤ 1) :
    |e - e' + r*z| ≤ 2*B + 1 := by
  have hm : |r*z| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hr0]
    simpa using (mul_le_mul hz hr1 hr0 (by norm_num : (0:ℚ) ≤ 1))
      -- the product in this bound is |z| * r
      <;> first | assumption | linarith
  rw [abs_le] at he he' hm ⊢
  constructor <;> linarith [he.1, he.2, he'.1, he'.2, hm.1, hm.2]
```

In the `hm` proof, to avoid any dependency on commutativity in `simp`, use this direct replacement for the `simpa ...` lines:

```lean
    calc
      r * |z| ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr0
      _ ≤ 1 := by simpa using hr1
```

Finally `Finset.card_insert_of_notMem`, `pow_succ`, and `ring` give \(2B+1=2^{|P|+1}-1\). This closes the helper theorem. The recurrence starts at **zero**, so the final error is 511, not 512.

### 4. Specialization and the actual node shift

* **Literal `range L`.** Zero cannot belong to `A`: specialize avoidance to `p := 5` (`by decide : 5 ∈ ninePrimes`) and use `dvd_zero`. Thus `A ⊆ liveIoc ninePrimes 0 L`; the upper endpoint may harmlessly include `L`. Apply `Finset.card_le_card`, cast, and take the upper half of `abs_le.mp` from the helper. `by decide` proves `ninePrimes.card = 9` and the closed bounded statement `∀ p ∈ ninePrimes, Nat.Prime p`.
* **Shifted column.** Inject `A` into `liveIoc ninePrimes (u+s) (u+s+L)` by `n ↦ n+s`, using `Finset.card_le_card_of_injOn`. Endpoint membership and injectivity are `omega`; for avoidance, a divisor of `n+s` would divide `f n` by the shift premise. This interval still has rational width **exactly `L`**. No estimate on `s` is needed.
* **Construct the two shifts.** Let \(M=\prod_{p\in\texttt{ninePrimes}}p\). It is \(1\bmod 6\) (closed computation). Write \(M=6b+1\). Take `s := b` for `twinLo` and `s := M-b` for `twinHi`. Then \(6s+1=M\) in the low case and \(6s-1=5M\) in the high case. Thus \(6(n+s)\) differs from the corresponding member by a multiple of every `p ∈ ninePrimes`, provided `1 ≤ n` on the low side. For a short Lean implementation, compute the constant `b` as `((∏ p ∈ ninePrimes, p) - 1) / 6`, split `hp : p ∈ ninePrimes` into the nine numeral cases as in `ninePrimes_le`, reduce the closed shift with `norm_num` or a separate `by decide` equality, unfold `twinLo`/`twinHi`, and use `omega` on divisibility by the now **literal** prime. This constructs the shift premise for the node without ever claiming that the marked **indices** avoid prime divisors.

For the existing `ℤ` certificate, prove once `sieveRho ninePrimes ≤ 460/1000` by closed rational computation (`decide` suffices). Multiply this inequality by `(L : ℚ)` using `mul_le_mul_of_nonneg_right` and `positivity`. At that point `linarith` gives the rational version of `1000 * A.card ≤ 460 * L + 512000`; `exact_mod_cast` transfers it to `ℤ`.

### The `linarith` reproducer

It is **false over `ℚ`**. Take `L = 0`, `U = -1`, `a = 1`. Both hypotheses hold and the conclusion is `1 ≤ 0`. The missing fact for that particular goal is `0 ≤ U`; with it the proof is just `by linarith`, without `h2`. To get the stronger `a ≤ L - 9`, you would need `9 ≤ U`, not `U ≤ 9`. Likewise a union upper bound gives a lower bound on the **full complement**, not necessarily even a lower bound on an arbitrary subset `A` of that complement. No tactic change fixes either direction.
