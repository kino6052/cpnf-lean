**Class: tilted factor-count moments on shifted primes.** Sample a genuine prime \(p\), factor the *same integer* \(p+2\) in several marked ways, and compare the resulting moments. The fixed difference survives every marking as the exact equation \(qm-p=2\); there is no relaxation to independent forms or to local densities.

### 1. The object

For an integer \(X>e^e\), put \(L=\log\log X\). For \(X<p\le 2X\), write
\[
r_p=\Omega(p+2)-1,
\]
where \(\Omega\) counts prime factors with multiplicity. Control the single polynomial
\[
F_X(u)=\sum_{X<p\le 2X\atop p\ {\rm prime}}
                \left(\frac{u}{L}\right)^{r_p}.
\]
The subtraction of **one** matters: \(F_X(0)\) is exactly the twin count, with no prime-power error. But the point at which I would estimate this polynomial is **\(u=2\), not \(u=0\)**.

Give \(p\) probability proportional to \((2/L)^{r_p}\), and denote expectation by \(E_X\). This is a positive probability measure. The plan needs only five of its factorial moments, and it does **not** need an asymptotic for the normalizing constant \(F_X(2)\).

### 2. The first move

Prove the **one-mark estimate**
\[
\boxed{\qquad
\left|E_X r_p-2\right|\le \frac1{100}
\quad\text{for all sufficiently large dyadic }X.
\qquad} \tag{1}
\]
Here and below dyadic means \(X=2^t\). The predicted value \(2\) is a research prediction, not an invocation of a limit theorem. Ordinary factor-count theorems for typical \(p+2\) do not establish it under this tilt.

There is a specific sum to attack. Order the prime factors of \(p+2\) with multiplicity and reserve one occurrence of its largest factor. A mark is any other occurrence. Write \(P^+(n)\) for the largest prime factor and \(v_q(n)\) for the multiplicity of \(q\). Then, with \(z=2/L\),
\[
F_X(2)E_X r_p
 =
 \sum_{\substack{q\ {\rm prime},\,m\ge1\\
                  X<qm-2\le2X\\ qm-2\ {\rm prime}}}
 z^{\Omega(qm)-1}
 \bigl(v_q(qm)-{\bf1}_{q=P^+(qm)}\bigr).
\]
This gives a first experiment with a falsifiable outcome: split this sum at \(q=X^{1/L}\), retaining the weight on the cofactor. The prediction is that the small-\(q\) part supplies \((2+o(1))F_X(2)\) and the rest is \(o(F_X(2))\). The reason for that cutoff is \(\log\log(X^{1/L})=L-\log L\): it preserves the leading reciprocal-prime mass while making a product of five such marked primes at most \(X^{5/L}\).

Estimate (1) is **not** twins under another name. A distribution supported entirely on \(r=2\) passes it exactly and has no twins. Proving (1) would instead establish a quantitative law for a rare, positively weighted population of shifted primes.

### 3. The chain

1. **One mark:** prove (1), comparing the marked and unmarked sums rather than evaluating either main term separately.
2. **Up to five marks — the open extension:** on a common cofinal sequence of those blocks prove \(\left|E_X\binom{r_p}{j}-2^j/j!\right|\le 1/100\) for \(2\le j\le5\), by marking distinct nonreserved factor occurrences.
3. **Finite extraction:** the odd Taylor truncation gives \({\bf1}_{r=0}\ge\sum_{j=0}^{5}(-1)^j\binom rj\). Consequently \(F_X(0)/F_X(2)\ge 1/15-5/100=1/60\).
4. **CPNF finish:** \(F_X(2)>0\) by Bertrand’s postulate, so each such block contains a twin; for \(p>3\) take \(n=(p+1)/6\) and apply `window_witness_of_twin`.

The choice **five** buys something exact. At mean two the cubic truncation gives \(-1/3\), useless even with perfect moment estimates. The quintic gives \(+1/15\), enough to tolerate five absolute errors of \(0.01\). There is no analytic continuation and no limit interchange in the extraction.

### 4. The wall

**The hard step is not putting five small marks into one modulus. It is deleting the marks without losing control of the tilted cofactor.** Even for one small \(q\), after deletion one has to compare sums over \(m\) with \(qm-2\) prime and weight \(z^{\Omega(m)-1}\). A count of primes \(p\equiv-2\bmod q\) has discarded exactly that weight. And replacing it by its ordinary mean is not a harmless approximation: here \(z=2/L\to0\), so one additional cofactor prime costs a factor \(L/2\). An exceptional bias among cofactors with very few factors can therefore change the answer by order one.

I would attack **one deletion before five insertions**: establish the displayed small-mark comparison *summed over \(q\)*, not uniformly for each \(q\), and separately bound the large-mark contribution. For the extension the corresponding objects are products \(Q\) of up to five marked occurrences, with \(Qm-2\) prime; repeated marks at the same prime value must be counted with occurrence multiplicity, not discarded as if \(Q\) were squarefree. Success on (1) alone does not authorize iteration: the once-marked population is a different measure. Stability of the comparison in those marked populations is the new obligation.

### 5. Verdict and unconditional remainder

The finite extraction is attackable now, by Lean. The one-mark comparison is a concrete analytic-number-theory project; I do not have its proof. The five-moment assertion is a **specific finite fragment of a Poisson law for exponentially tilted \(\Omega(p+2)-1\) on primes**. I would not label it a known consequence of the classical Sathe–Selberg theorem, nor claim it is equivalent to the twin-prime conjecture. The implication proved above is one-way.

What survives unconditionally is an exact **obstruction on every twin-free block**: at least one of the five binomial moments must differ from \(2^j/j!\) by at least \(1/75\), since the signed errors must erase \(1/15\). More sharply, their signed sum must be at most \(-1/15\). Chen’s theorem supplies infinitely many rows with \(r_p\le1\); it does not control these tilted moments or separate \(r_p=0\) from \(r_p=1\). No new unconditional lower bound for twins is being inferred.

For Lean, the first deliverable should be independent of primes and logarithms: for a finite set \(S\), weights \(w_s\ge0\), and labels \(r_s:\mathbb N\), prove
\[
\sum_{s:r_s=0}w_s\ \ge\
\sum_{j=0}^{5}(-1)^j\sum_{s\in S} w_s\,\mathrm{Nat.choose}(r_s,j).
\]
The pointwise proof is equality at \(r=0\); at \(r\ge1\) the right-hand kernel is \(-\binom{r-1}{5}\) by Pascal cancellation. That lemma fixes the error budget *before* any analytic work. The first analytic milestone is then unambiguous: **measure one nonlargest prime-factor occurrence under the \(2/\log\log X\) tilt, to absolute error \(0.01\).**
