There is no proof with `D` as specified. The wheel gives an **upper** bound on the number of rows hit by top-band primes. The `20` argument gives a **lower** bound on the number of rows **outside** that hit set. Also, `q > Nat.sqrt X` does not give at most two hits in a class block.

Both distinctions can be checked on small finite inputs. Here is Lean code for the counterexamples, using the global band `(Nat.sqrt X, Nat.sqrt (12*X+1)]`, which contains every possible `midT` score in `blk X`.

```lean
import CpnfLean.Ladder
import CpnfLean.Wheel

namespace CPNF

def classBlock (X M r : ℕ) : Finset ℕ :=
  (blk X).filter (fun n => n % M = r)

def bandPrimes (X : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt X) (Nat.sqrt (12 * X + 1))).filter Nat.Prime

def bandHits (X M r : ℕ) : Finset ℕ :=
  (classBlock X M r).filter
    (fun n => ∃ q ∈ bandPrimes X, q ∣ twinLo n ∨ q ∣ twinHi n)

-- One top-band prime, one residue class, nineteen hits.
example :
    11 ∈ bandPrimes 100 ∧
    ((classBlock 100 1 0).filter
      (fun n => 11 ∣ twinLo n ∨ 11 ∣ twinHi n)).card = 19 := by
  native_decide

-- A whole nonempty class is rough and nonpassing, with no top-band hit.
example :
    classBlock 100 128 126 = {126} ∧
    126 ∈ midB 100 3 ∧ score 126 ≠ twinLo 126 ∧
    (∀ q ∈ bandPrimes 100, Nat.Coprime q 128) ∧
    bandHits 100 128 126 = ∅ := by
  native_decide

end CPNF
```

The second example has `twinLo 126 = 755 = 5 * 151` and `twinHi 126 = 757`, a prime. Its killer is above `z = 3` but **below** the top band. It refutes the proposed inclusion of nonpassing rows in `D`, even when the class has no passing row. An unspecified additive error could of course make a numerical inequality true; it would not validate that inclusion.

### The corrected per-prime statement

Here is the exact Lean type of a valid replacement lemma, in `namespace CPNF` with `classBlock` as above. This is a proof obligation, **not** one of the compiled lemmas.

```lean
#check (∀ (X M r q : ℕ), 0 < M → r < M → Nat.Prime q →
    3 < q → Nat.Coprime q M →
    ((classBlock X M r).filter
      (fun n => q ∣ twinLo n ∨ q ∣ twinHi n)).card ≤
      2 * (((classBlock X M r).card + q - 1) / q))
```

For the proof, put `L = (classBlock X M r).card`. If `L = 0` the claim is immediate. Otherwise, starting at its least row `a`, the class consists of `a + M*j` for `0 ≤ j < L`: the rows satisfying the interval bounds are consecutive in progression order. In `j`, each sign gives one residue modulo `q`, since `6*M` is invertible modulo `q`. There are at most `(L + q - 1) / q` occurrences of each residue. For the last step one can shift to `1 ≤ j+1 ≤ L` and apply `progression_card` with the positive representative in `[1,q]`. The parametrization and modular cancellation need proofs in addition to `progression_card`; `wheel_block` proves neither.

In particular, **`L ≤ q`** suffices for two hits. `X < q*q` is not a substitute. The issue is not simultaneous divisibility at one row: a prime dividing both members would divide their difference `2`, yet both members are odd. The issue is repetition of the *same* sign on different rows. In the paper's CRT argument the period in `n` is `M*q`, not `M`.

### Where the constants actually go

One can recover all the listed constants for a **corrected exclusion argument**. To avoid endpoint errors choose `k ≥ 1`, `t = 210*k`, `X = t*t`. Write `S = classBlock X M r`, `L = S.card`, and **`U = (bandHits X M r).card`**. Here `M > 0`, `r < M`, and the band primes must be coprime to `M`.

* Every band prime is in `(t,4*t]` since `12*t*t+1 ≤ (4*t)^2`. In `(t,2*t]` use `k` consecutive blocks of length `210`; in `(2*t,4*t]` use `2*k`. The left endpoints for `wheel_block` are respectively `t+210*i` for `i<k` and `2*t+210*i` for `i<2*k`. All these primes exceed `7`, hence are coprime to `210`. By disjoint addition of `wheel_block` counts the two prime counts are **at most** `48*k` and `96*k`. The factor of two in the second count is the length of the second interval. For general `X`, taking `k = Nat.sqrt X / 210` and ignoring the remainder does not give this proof.
* For each prime use the corrected per-prime bound, weakened to `2*(L/q + 1)` with natural division. A union bound now gives
  \[
  U\ \le\ 96k\,\bigl(L/t+1\bigr)+192k\,\bigl(L/(2t)+1\bigr).
  \]
  Thus `96*k` and `192*k` here count the two **signs** per candidate; `288*k` is their sum, the additive endpoint allowance. This is an **upper** bound, with no lower-bound information on primality or distinct hits.
* Multiply by `210` and use `t*(L/t) ≤ L` and `(2*t)*(L/(2*t)) ≤ L`. The result is `210*U ≤ 192*L + 60480*k`, where `60480 = 210*288`. The product bounds for natural division are inequalities, not rewrites.
* The size hypothesis **`8064*k ≤ L`** suffices for `20*U ≤ 19*L`: after multiplying the latter comparison by `210`, the margin in the coefficient of `L` is `210*19 - 20*192 = 150`, and `20*60480 = 150*8064`. This size hypothesis is not automatic for arbitrary `M`. The more useful formulation for small classes retains the endpoint error instead.

Here is the last step, including the direction of the conclusion, as a complete Lean theorem:

```lean
theorem top_exclusion_arithmetic (k L U : ℕ)
    (hcount : 210 * U ≤ 192 * L + 60480 * k)
    (hsize : 8064 * k ≤ L) :
    20 * U ≤ 19 * L ∧ L ≤ 20 * (L - U) := by
  omega
```

So the quantity forced to be at least a twentieth of the class is `L - U`, **not `U`**.

### Connecting exclusion to the compiled ladder

The appropriate pointwise theorem uses `rough_split`, not `local_slack_iff`:

```lean
namespace CPNF

theorem middle_or_pass_of_not_top (X z n : ℕ)
    (hr : n ∈ rough X z) (ht : n ∉ midT X z) :
    n ∈ midB X z ∨ score n = twinLo n := by
  rcases rough_split X z n hr with hp | hb | htop
  · exact Or.inr (Finset.mem_filter.mp hp).2
  · exact Or.inl hb
  · exact False.elim (ht htop)

end CPNF
```

To apply this on `S \ bandHits X M r`, two bridges matter:

1. A `midT` row in `S` is in `bandHits`: take `q = score n`. It is the least prime factor of one of the two members, hence prime and a divisor (`Nat.minFac_prime`, `Nat.minFac_dvd`); the defining square inequalities of `midT` put it in the band. The converse is not needed: an incidental top-band divisor need not be the score.
2. One needs **`S ⊆ rough X z`** to count every row of the complement as middle or passing. This holds if the class actually avoids every possible prime divisor up to `z`. Coprimality of the *top-band primes* to `M` does not imply it. Simply filtering `S` by roughness and using its new cardinality as `L` in the per-prime lemma is also invalid: the filtered progression need not be consecutive.

With those bridges and no witness in `S`, the resulting bound is `L ≤ 20 * (S ∩ midB X z).card` under the stated size condition. `local_slack_iff`, by contrast, only gives failure of strict slack under no witness in the block; together with `rough_card` this says `|rough| = |midB| + |midT|`. It does not delete the `midB` summand or put its rows in `bandHits`.

**Wall check.** The corrected square-scale *upper* estimate uses finite progression counting and the wheel, not an analytic estimate. Reversing it to force *top hits* would require new lower-bound information about actual prime incidences and their overlaps. Nor does forcing many *middle deaths* give strict slack: those deaths still count on the nonpassing side of `local_slack_iff`. Neither `score_unbounded` nor the unique-factor lemma in `Charge.lean` supplies the missing comparison.
