**My answer is option 4.** There is a divisor-switching reduction in which the low column supplies a provably positive main term, and the entire missing input is a **one-sided bound on a Möbius sum over large divisors of \(p+2\)**. The hypothesis does not test whether \(p+2\) is prime, does not count common marks, and does not require an asymptotic for the Möbius sum. Even a negative contribution of nearly the size of the main term is tolerable.

Here is the cut, including the constant and the direction of the inequality.

### The missing lemma

Write \(\mu\) for the Möbius function, \(\log\) for the natural logarithm, and set
\[
 C_2=\prod_{\ell>2,\ \ell\ {\rm prime}}
       \left(1-\frac1{(\ell-1)^2}\right).
\]
At scale \(x=2^t\), put \(Y=2x+2\) and \(D=\lfloor x^{1/3}\rfloor\). Define
\[
 B(x)=
 \sum_{\substack{x<p\le 2x\\p\ {\rm prime}}}\log p
 \sum_{\substack{d\mid p+2\\d>D}}
       \mu(d)\log(Y/d).
\]
One sufficient missing lemma is
\[
 \boxed{\qquad
 \forall T\ \exists t\ge T,\qquad B(2^t)\ \ge\ -C_2\,2^t .
 \qquad} \tag{LD}
\]
In fact \(C_2\) on the right can be replaced by **any fixed \(c<2C_2\)**. The strict margin below \(2C_2\), not a conjectural square-root cancellation rate, is the point.

Here is a Lean declaration of the input. It uses `d^3 > x` so no real cube roots or rounding lemmas enter the definition.

```lean
import Mathlib
import CpnfLean.Overload

namespace CPNF

open scoped BigOperators

noncomputable def largeDivisorTail (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc x (2*x)).filter Nat.Prime,
    Real.log (p : ℝ) *
      ∑ d ∈ (p+2).divisors.filter (fun d => x < d^3),
        (ArithmeticFunction.moebius d : ℝ) *
          Real.log (((2*x+2 : ℕ) : ℝ) / (d : ℝ))

-- A rational-constant version; 1 < 2*C₂, as shown below.
def CofinalLargeDivisorFloor : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
    -(2^t : ℝ) ≤ largeDivisorTail (2^t)

end CPNF
```

The rational-constant version is **weaker** than (LD) and still suffices. Here is the proof, separating the known analysis from the new input.

### 1. The complementary sum is unconditionally positive

Let \(A(x)\) be the same sum as \(B(x)\) with \(d\le D\). Then
\[
                         A(x)=(2C_2+o(1))x.                 \tag{1}
\]
This is a one-column theorem. To prove it, take \(x>2\), so \(p+2\) is odd. Interchange the sums; for each odd \(d\le D\) the inner prime sum is in the **reduced** residue class \(-2\bmod d\). The Bombieri–Vinogradov theorem for the prime Chebyshev function
\(\vartheta(u;d,a)=\sum_{p\le u,\ p\equiv a\bmod d}\log p\) gives
\[
 A(x)=x\sum_{\substack{d\le D\\d\ {\rm odd}}}
           \frac{\mu(d)}{\varphi(d)}\log(Y/d)+o(x).
\]
Indeed \(D\le \sqrt{x}/(\log x)^b\) eventually for every fixed \(b\); the extra coefficient is at most \(\log Y\), absorbed by requesting a saving of three powers of \(\log x\) at the two endpoints. Here \(\varphi\) is Euler's totient.

For clarity, the main-term evaluation needs **cancellation**, not just the formal value of an Euler product. Define \(a(d)=\mathbf1_{2\nmid d}\mu(d)/\varphi(d)\). For \(\Re s>0\),
\[
 \sum_{d\ge1}a(d)d^{-s}=\frac{H(s)}{\zeta(1+s)},\qquad
 H(s)=\frac1{1-2^{-1-s}}
 \prod_{\ell>2}
 \frac{1-\ell^{-s}/(\ell-1)}{1-\ell^{-1-s}},
\]
where the product runs over primes. The Dirichlet series of \(H\) converges absolutely already at \(s=-1/4\): the sum of absolute nonconstant terms of each odd local factor there is
\[
 \frac{\ell^{1/4}}{\ell(\ell-1)(1-\ell^{-3/4})}.
\]
In particular \(H(0)=2C_2\).

Explicitly, if \(h\) denotes the coefficients of \(H\), then \(a=h*(\mu(n)/n)\), with \(*\) Dirichlet convolution. The classical zero-free-region prime number theorem gives, for every fixed \(J>0\),
\[
 \sum_{n\le u}\frac{\mu(n)}n=O_J((\log u)^{-J}),\qquad
 \sum_{n\le u}\frac{\mu(n)\log n}{n}=-1+O_J((\log u)^{-J}).
\]
These follow by partial summation from the classical Mertens-function bound; the limiting constants are the value and negative derivative of \(1/\zeta(1+s)\) at zero. Convolving, splitting the \(h(k)\) sum at \(k=\sqrt D\), gives
\[
 \sum_{d\le D}a(d)=O_J((\log D)^{-J}),\qquad
 \sum_{d\le D}a(d)\log d=-H(0)+o(1).
\]
For the large-\(k\) tail, \(\sum_{k>\sqrt D}|h(k)|\ll D^{-1/8}\), enough even against powers of \(\log D\). Expanding \(\log(Y/d)\) now proves (1).

There is no numerical dependence on a tabulation of \(C_2\). The product over **all** integers \(m\ge2\) of \(1-m^{-2}\) telescopes to \(1/2\). The product for \(C_2\) uses only \(m=\ell-1\) and omits, in particular, \(m=3\). Hence \(C_2\ge(1/2)/(1-1/9)=9/16\). The Lean floor of \(-x\) therefore leaves an explicit asymptotic margin of at least \(x/8\).

### 2. Why that floor makes the overload cofinal

Let \(\Lambda(m)=\log q\) for \(m=q^e\) a prime power with \(e\ge1\), and zero otherwise. For \(m=p+2>1\) the *complete* divisor sum satisfies
\[
 \sum_{d\mid m}\mu(d)\log(Y/d)=\Lambda(m).
\]
Indeed the constant \(\log(Y/m)\) multiplies \(\sum_{d\mid m}\mu(d)=0\), and the remaining identity is Möbius inversion of \(\log m=\sum_{d\mid m}\Lambda(d)\). Thus there is no truncation error of unspecified sign:
\[
 \sum_{x<p\le2x}\log p\,\Lambda(p+2)=A(x)+B(x).
\]
On the cofinal sequence supplied by `CofinalLargeDivisorFloor` this is at least \((1/8-o(1))x\).

Proper prime powers cannot supply this mass. There are at most \(\sqrt Y\log_2 Y\) possibilities for \(q^e\le Y\), \(e\ge2\), by counting bases and exponents, each contributing at most \((\log Y)^2\). Their total is \(o(x)\). So for all sufficiently large scales on that sequence there is a prime \(p\in(x,2x]\) with \(p+2\) prime.

To produce the actual `CofinalNodeOverload` indices, note that \(p>3\) forces \(p\equiv5\bmod6\) for such a pair. Set \(n=(p+1)/6\), \(s=\lfloor\log_2(n-1)\rfloor\), \(N=2^s\). The use of **\(n-1\)** matters at exact powers of two: it gives \(N<n\le2N\) with precisely your half-open convention. Both prime members exceed \(N\), so `minFac_eq_self_of_prime` puts \(n\) in both mark sets. Set
\[
                         d=s,\qquad j=n-N-1.
\]
Then \(j<N\), `node s s j` is \(\{n\}\), and the three counts in `forced` are \(1,1,1\). Since \(p\) is unbounded, so is \(s\). This proves the conditional implication to the stated overload, not just to a witness on a nondyadic block.

### 3. Where to attack the input

The useful alternative form of the **same** missing sum is
\[
 B(x)=\sum_{k<Y/D}
       \ \sum_{\substack{d>D,\ x<kd-2\le2x\\kd-2\ {\rm prime}}}
       \mu(d)\log(kd-2)\log(Y/d).
\]
Here \(k=(p+2)/d\). This gives a concrete division of labor: small divisors have already been paid for by distribution of **one prime in progressions**; what remains is the sign of \(\mu(d)\) against primality of \(kd-2\), summed over complementary factors. In particular the \(k=1\) sum contains \(\mu(p+2)\log p\log(Y/(p+2))\). Even the sign being tested there depends on factor parity. One should not remove that term as a rounding error or replace the signed coefficients by absolute values. Nor does the reduction require a separate estimate for every \(k\): cancellation *between* cofactor ranges is allowed.

This is what the dyadic telescope alone does not supply. If twins stop, the complete sum is \(o(x)\) by the proper-power bound, and **the large-divisor tail must equal \(-2C_2x+o(x)\) on every sufficiently large scale**. To rule that out, it suffices to prevent that much negative bias cofinally often. I do not have an unconditional proof of the floor. The positive small-divisor term is a theorem; preventing its cancellation is the missing arithmetic lemma.
