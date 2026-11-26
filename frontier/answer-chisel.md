**Yes to the polynomial witness.** In fact, for all sufficiently large \(h\), **every** interval of \(h^5\) consecutive positive indices contains an \(n\) with `h < score n`. This is a lower-bound sieve theorem, not a consequence of replacing the factorial by an lcm. There is also a separate, elementary result: on \((X,2X]\), the **entire top band** of primes from \(\sqrt X\) to the twin cutoff misses a proportion tending to one. The important distinction is *of which set*: it misses almost all **indices**, not necessarily almost all **survivors of the smaller primes**.

First, one correction to the stated wall matters for the Lean targets. `head_le_of_factor` takes the hypothesis
```lean
hlo : twinLo (head k) ≤ score (head k)
```
which, by `twin_of_score_row`, **already says the head is a twin**. Its contrapositive retains `hlo`. The unconditional inference available from `minFac_le_of_tail` is from **score** escaping \(t\), not from **index** escaping \(t\). The unconditional wall theorem to build on is `twin_iff_sq_test`.

### 1. An elementary top-band exclusion, on the actual short interval

Here is a finite theorem with small constants. Let \(t=\lfloor\sqrt X\rfloor\), \(I=(X,2X]\cap\mathbb N\), and take
\[
 B_X=\{p:\ p\text{ prime},\ t<p,\ p^2\le 12X+1\}.
\]
For \(t\ge 10000\),
\[
 20\,\#\{n\in I:\ \forall p\in B_X,\ \neg\texttt{hit}\ p\ n\}\ \ge X .
\]
In particular this is not a count on a full primorial period substituted for a count in \(I\).

**Proof.** All the primes in question lie in \((t,4t]\), since \(X<(t+1)^2\). Split at \(2t\). In \((u,2u]\) there are at most \(48(u/210+1)\) primes for \(u\ge 7\): there are exactly 48 residues coprime to 210 per period. Each prime there hits at most \(2(X/u+1)\) indices of \(I\), by the two progression counts. Summing for \(u=t,2t\), the number hit is at most
\[
 \frac{32}{35}X+\frac{48}{35}t+144X/t+192
 \ \le\ \frac{19}{20}X
\]
for the indicated range, using \(t^2\le X\). All divisions in this proof can be rational divisions followed by clearing denominators. The only wheel computation, `φ 210 = 48`, is a closed finite calculation.

A stronger first-order target replaces \(1/20\) survival by arbitrarily small **loss**:
\[
 \forall A\ge1\ \exists X_0\ \forall X\ge X_0,\qquad
 A\,\#\{n\in I:\exists p\in B_X,\ \texttt{hit}\ p\ n\}\le X.
\]
Use the identical two-block proof with a fixed wheel \(M\) instead of 210. Its leading loss bound is \(4\varphi(M)X/M\); the remaining terms divided by \(X\) go to zero for fixed \(M\), by the displayed counting argument. One can choose \(4A\varphi(M)/M<1\) entirely elementarily: for \(M=\prod_{p\le b}p\), the finite Euler product \(M/\varphi(M)\) dominates \(\sum_{j\le b}1/j\) by geometric expansion and factorization. Dyadic grouping makes this last sum arbitrarily large.

**What this buys:** one may even pre-sieve by any **fixed** bottom wheel with positive survivor fraction and still retain a positive fraction after imposing the whole top band: choose the top loss smaller than half the bottom wheel’s fraction, allowing for the bottom wheel’s end-period error. The word *fixed* matters. This subtraction gives no positive lower bound after pre-sieving by **all** \(p\le t\).

### 2. A polynomial bound for the first crossing

The Lean-facing target is
```lean
∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ a : ℕ,
  ∃ n : ℕ, a < n ∧ n ≤ a + h^5 ∧ h < score n
```
Here is specifically what external mathematics proves it. Apply the dimension-two lower-bound beta sieve (for example, the beta sieve in Friedlander–Iwaniec, *Opera de Cribro*) to the indices \(a<n\le a+H\), with \(H=h^5\), sifting primes \(5\le p<z=h+1\). The data to supply are:

* For squarefree \(d\) supported on the sifting primes, simultaneous hits occupy exactly \(\rho(d)=2^{\omega(d)}\) classes modulo \(d\), by CRT; \(\omega(d)\) counts distinct prime divisors. Thus their count is \(H\rho(d)/d+r_d\), with \(|r_d|\le\rho(d)\), **uniformly in \(a\)**.
* The dimension condition is the usual Mertens product bound for \(\prod_{w\le p<z,\ p\ge5}(1-2/p)^{-1}\), of dimension two. It follows from the ordinary prime Mertens product by extracting \((1-1/p)^{-2}\); the correction factors are \(1+O(p^{-2})\).
* Take level \(D=H/(\log H)^{10}\). The total absolute remainder for the beta-sieve weights (of modulus at most one) is at most
  \[
  \sum_{d\le D}2^{\omega(d)}
     \le \sum_{d\le D}\sum_{e\mid d}1
     \le D(1+\log D).
  \]
  This is negligible compared with \(H/(\log h)^2\).
* The ratio \(\log D/\log z\) tends to **5**, strictly above the dimension-two beta-sieve lower-bound threshold. Hence the lower bound is a positive constant times \(H/(\log h)^2\) for sufficiently large \(h\), uniformly in the starting point. Each survivor has `h < score n`.

More generally the same proof works with any fixed exponent strictly above the sifting limit of the lower-bound theorem used. **The content here is not a positive constant density:** it is a lower bound large enough to force a witness, in every translate. The analytic sieve input is substantive and is not in `Count.lean`; `progression_card` is a starting point for the first bullet, not a substitute for the third and fourth together.

With \(a=0\) this gives exactly the requested large-\(h\) polynomial location. If an exponent valid for **every \(h\ge1\)** is desired, enlarge it to absorb the finitely many factorial witnesses for \(2\le h<h_0\); \(n=1\) handles \(h=1\). Taking the product of primes \(5\le p\le h\) as the index is a different construction: it forces the **single** safe residue \(0\) at every prime, and that product grows faster than every polynomial. The sieve obtains its gain by retaining **all** \(p-2\) safe residues at each prime.

### 3. A first-order gap property and its exact payoff

Use a gap measured in **indices** but parameterized by **score**. For integers \(h,a,L\ge0\) write
\[
 \mathrm{HitWindow}(h,a,L)
 \quad:\!\iff\quad
 \exists n,\ a<n\le a+L\ \land\ h<\texttt{score}\ n .
\]
There are three genuinely different strengths:

* **Fixed-scale bounded gaps:** \(\forall h\ \exists L\ \forall a,\ \mathrm{HitWindow}(h,a,L)\). Elementary: take \(L=\prod_{5\le p\le h}p\) over primes and use a multiple of \(L\). Part 2 improves the gap bound to \(h^5\) eventually. Neither bound places a witness inside the certification window.
* **A constant gap independent of \(h\)** is false, even if the allowed starting points are arbitrarily large. For any proposed length \(L\ge1\), choose distinct primes \(p_i>3\), \(1\le i\le L\), and solve \(6(a+i)\equiv1\bmod p_i\) by CRT. For \(h=\max_i p_i\), the whole interval fails. Translating \(a\) by the product repeats the failure.
* **One well-placed gap bound**, not one in every translate, suffices for directness. A sharp target using your existing `window` is
  \[
  \boxed{\quad
  \forall K\ \exists h,n,\quad
     1\le n,\quad K\le n\le\texttt{window}\ h,\quad
     h<\texttt{score}\ n .
  \quad}
  \]
  This is **equivalent** to `OftenDirect`. Forward: the witness satisfies \(6n+1\le h^2<\texttt{score}(n)^2\); apply `twin_iff_sq_test` and `direct_of_twin`. Reverse: take a cofinal twin and put \(h=6n-2\). Its score is \(6n-1\), and \((6n-2)^2\ge6n+1\) for \(n\ge1\).

Thus there is no distinguished “weakest” extra property without a restriction on the language of hypotheses: the conclusion itself is weakest up to implication. But the boxed equivalence identifies exactly **which instance of interval hitting** is needed. It does **not** demand uniform gaps, a twin in every dyadic interval, or even that the qualifying \(h\)'s have bounded ratios. The gap between Parts 2 and 3 is quantitative: the known guarantee gives room of order \(h^5\); the sufficient window ends at \((h^2-1)/6\), and must contain a witness **beyond \(K\)**.

### 4. The no-go that is actually a theorem

There is **no known prohibition on a combinatorial proof** at the twin cutoff, and no density or analytic fact known to be necessary for every proof. Exact finite inclusion–exclusion even *decides* every individual finite window. What is missing is a uniform or cofinal positivity proof, not a decision procedure.

There is, however, a clean impossibility theorem for the paper’s **fixed-modulus projection**. For any \(M\ge1\), old residue \(r<M\), and fresh prime \(q\ge5\) coprime to \(M\), the \(q\) lifts \(r+jM,\ 0\le j<q\), contain **exactly two hits and exactly \(q-2\) misses** for `hit q`. Multiplication by \(6M\) permutes residues modulo \(q\). Thus the projection of the hits to residues modulo \(M\) is **all** residues, and the projection of the misses is also **all** residues. Neither projection can track a representative’s death. More strongly, for any finite list of fresh primes, *every* old residue has arbitrarily large lifts missing the whole list: impose \(n\equiv0\bmod q\) at each fresh prime. This precisely invalidates the finite-subcover step in Appendix D, without ruling out arguments that keep the interval and the lifts.

My suggested formalization order is **the lift-count lemma, the \(1/20\) top-band theorem, then the boxed equivalence**. All three are finite arithmetic with the infrastructure shown. Keep the \(h^5\) interval theorem as a separate sieve formalization target: it is an unconditional improvement to `score_unbounded`, whereas promoting its exponent and location to the boxed window is the unresolved step.
