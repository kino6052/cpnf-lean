**Attack: use a real character to detect the composite impostors in a Chen sieve.** Don’t try to raise the roughness cutoff from \(h^5\) to \(h^2\). Instead, change what has to be detected at the lower cutoff. Chen’s theorem supplies primes \(p\) for which \(p+2\) is prime or a product of two primes, counted with multiplicity. On rows where a real Dirichlet character \(\chi\) has \(\chi(p+2)=-1\), every composite impostor has **exactly one** prime factor \(q\) with \(\chi(q)=+1\). Charge the impostor to that factor, even when it is the *larger* factor. This gives a finite subtraction with no multiplicity loss. The analytic reason to try it is specific: a real character with an exceptional zero can have unusually few \(+1\) primes in the relevant weighted sense. Heath-Brown’s *Prime twins and Siegel zeros* gives an actual conditional twin-prime theorem in this regime. The proposed finite lemma is a way to expose this mechanism in CPNF, not a claim that an exceptional zero exists or that Heath-Brown’s proof uses this particular subtraction.

### First lemma: exact charge for the semiprime error

Here is the statement I would formalize. Use an integer-valued multiplicative function in the finite lemma; periodicity and analytic hypotheses belong only in the later estimates. The finset `S` need not be all the rows of an interval, so one can impose character conditions or other restrictions without changing the lemma.

```lean
namespace CPNF

def TwoPrimeProduct (m : ℕ) : Prop :=
  ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ m = a * b

def plusPrimes (χ : ℕ → ℤ) (z U : ℕ) : Finset ℕ :=
  (Finset.Ioc z U).filter (fun q => Nat.Prime q ∧ χ q = 1)

-- Proposed statement, not a claim of a checked build.
theorem chen_charge_exact
    (S : Finset ℕ) (χ : ℕ → ℤ) (z H : ℕ)
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hS : ∀ n ∈ S,
      1 ≤ n ∧ twinHi n ≤ H ∧ z < score n ∧
      Nat.Prime (twinLo n) ∧ χ (twinHi n) = -1 ∧
      (Nat.Prime (twinHi n) ∨ TwoPrimeProduct (twinHi n))) :
    S.card =
      (S.filter (fun n => score n = twinLo n)).card +
      ∑ q ∈ plusPrimes χ z (H / (z + 1)),
        (S.filter (fun n => q ∣ twinHi n)).card
```

**Proof.** Reverse the order of the finite incidence sum, and fix a row \(n\). Write \(m=6n+1\).

* If \(m\) is prime, its only prime divisor is itself, of character \(-1\). Its incidence count is zero, and `twin_iff_score_eq_lo` puts it in the first summand.
* Otherwise \(m=ab\) for primes \(a,b\). Since \(\chi(a)\chi(b)=-1\) in \(\mathbb Z\), the two values are \(+1,-1\) in some order. In particular \(a\ne b\). Call the positive-character factor \(q\) and the other \(r\). Both exceed \(z\), because \(z<\operatorname{score}(n)\le m.\mathrm{minFac}\). Thus \(q(z+1)\le qr=m\le H\), putting \(q\) in the indicated finset. Any prime dividing \(ab\) equals \(a\) or \(b\), so the incidence count is **one**. The first summand does not count this row.

The upper endpoint \(H/(z+1)\), **not** \(\sqrt H\), matters: the sign picks out a unique factor, but does not pick out the smaller one. No estimate on prime distribution enters the identity.

### The estimate to attack

Take \(X\le n\le 2X\), \(H=12X+1\), and form `S` from the rows satisfying `hS`. For \(X\ge1\) it suffices to beat the following **upper bound** for the charge:
\[
 B_\chi(X,z)=
 \sum_{q\in\mathrm{plusPrimes}(\chi,z,\lfloor H/(z+1)\rfloor)}
 \#\{r\text{ prime}:r>z,\ \chi(r)=-1,\ 
         6X+1\le qr\le H,\ qr\equiv1\pmod 6,\ qr-2\text{ prime}\}.
\]
Indeed \((q,r)\) recovers \(n=(qr-1)/6\). The proposed analytic task is to obtain a **Chen lower bound for \(|S|\)** and a **strictly smaller upper bound for \(B_\chi\)** on cofinally many scales. For the upper bound one can drop \(\chi(r)=-1\) and use an upper-bound sieve on the two linear forms \(r,qr-2\) for fixed \(q\); one should retain the restriction \(\chi(q)=+1\) in the outer sum. This is an estimate on prime factors of one sign, not an estimate asserting that a twin row exists. The two estimates must use the *same* character, roughness cutoff, and scale.

### Why this takes a different route through the four walls

1. **Parity:** Chen leaves a genuine prime-versus-semiprime ambiguity. The character provides extra arithmetic data: on a negative-character semiprime the positive-character factor is mandatory. Multiplicativity gives the charge; only an independently proved **scarcity** of those factors could make the charge small. Without scarcity, the identity has not broken parity.
2. **Sifting ratio:** No lower-bound sieve is run to \(\sqrt H\). The lower bound sought is for almost primes at a smaller cutoff; the final removal is by the signed-factor budget. Only *after* finding a prime row does one choose the certification threshold via `window_witness_of_twin`.
3. **Fixed modulus:** Even if \(\chi\) is periodic, the incidence test is \(q\mid 6n+1\) on the actual integer. The character predicts the sign of a factor that must occur, not whether a fresh prime hits a lift.
4. **Prime order:** The argument sums over indices and actual factorizations. In particular the bound for \(B_\chi\) uses the fact that the other member is **\(qr-2\)**. Replacing the index domain by a sparse cubic domain does not preserve the proposed Chen lower bound.

**Likely failure point.** For an ordinary character there is no reason for the \(+1\) factor budget to be small enough. Conversely, even given a favorable bias, an unrestricted Chen lower bound cannot simply be restricted to \(\chi(6n+1)=-1\): the lower bound must survive that selection uniformly at the conductor and scale where the bias is useful. These are coupled requirements. Heath-Brown’s exceptional-zero result is evidence that character bias can matter at twin-prime strength, **not** a source of such characters on demand.

If the strict comparison worked cofinally, it would prove the **boxed condition itself**: the exact charge leaves a row with `score n = twinLo n`, and the existing Lean lemmas supply its window. I do not know an unconditional route to that comparison. The unconditional deliverable is `chen_charge_exact`: it turns the entire composite error on a character-selected Chen set into a disjoint, explicitly bounded factor sum that can be estimated separately.
