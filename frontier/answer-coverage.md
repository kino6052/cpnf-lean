For the deterministic CPNF order, the cover is unique if each index is assigned to its **first** hitting prime. The death heads are exactly the strict records of those assignments. This gives a tail-cover equivalence, a quantitative lower bound on the moduli any tail cover must use, and a comparison process with an actual endless chase. It does not decide (A).

## 1. The exact cover and its order constraints

Write \(L_n=6n-1,\ U_n=6n+1\), for \(n\ge1\). For each prime \(p\ge5\) define
\[
 E_p=\{n:6n\equiv\pm1\pmod p\},\qquad
 F_p=E_p\setminus\bigcup_{5\le r<p,\ r\ {\rm prime}}E_r .
\]
The \(F_p\) partition the positive indices: \(n\in F_p\) precisely when \(p=s(n):=\operatorname{score}(n)\). The subtraction is essential. It says not just that \(p\) can hit \(n\), but that it owns the death of \(n\) in prime order.

Here is a sequence description that skips all non-death stages. Set
\[
 a_1=1,\qquad q_i=s(a_i),\qquad
 a_{i+1}=\min\left(\mathbb N_{>0}\setminus\bigcup_{p\le q_i}E_p\right),
\]
where unions over \(E_p\) use primes \(p\ge5\). The minimum exists: a positive multiple of the product of the primes in the union misses every class. Inductively, \(a_i\) is the least index left after the previous death; no intervening prime below \(q_i\) hits it, and \(q_i\) does. Thus \((a_i,q_i)\) are **all and only** the head/killer pairs at deaths. Equivalently the \(a_i\) are the strict score records: \(a_{i+1}\) is the first index with score greater than \(q_i\). In particular the killers increase strictly. One must use **all** primes through \(q_i\) in the recursion, not just the record killers; primes that never move the head still remove future candidates.

Define the square-truncated classes
\[
 C_p=E_p\cap\{n:p^2\le U_n\}.
\]
Then the following are equivalent:
\[
\begin{aligned}
 &\text{CPNF has an endless chase};\\
 &\exists i_0\ \forall i\ge i_0:\quad q_i^2\le U_{a_i};\\
 &\exists N\quad [N,\infty)\cap\mathbb N\ \subseteq\ \bigcup_{p\ge5} C_p .
\end{aligned}
\]
Indeed, a non-twin has a composite member whose least prime factor is at most \(\sqrt{U_n}\), so its first hit already meets the square cutoff. Conversely \(\sqrt{U_n}<L_n\), so every hit meeting the cutoff is proper. A twin has score \(L_n\), strictly greater than every earlier score since \(s(m)\le L_m\). Hence no twin can hide between successive death heads. This proves all three equivalences. The size comparison is with the **member**, not the index \(a_i\).

One consequence concerns the distinction between (A) and (A′): **on the original full index set, freedom to choose the order or a subset of the actual proper-divisor classes cannot help construct a tail cover.** Any such cover implies there are no twins on the tail; if there are no twins there, the canonical first hits already cover it properly. The finite-period covering problem and the unrestricted abstract covering problem are different from this one.

## 2. Two necessary conditions on a tail cover

These apply even to a proposed subfamily \(P\) of primes satisfying \([N,\infty)\subseteq\bigcup_{p\in P}C_p\). They concern all moduli used to cover the tail, **not** just the record killers.

**First, \(\sum_{p\in P}1/p\) must diverge.** Suppose it converges. By CRT the density of indices missed by the primes of \(P\) up to \(z\), even without the square truncation, is
\[
 \delta_z=\prod_{\substack{p\in P\\p\le z}}(1-2/p)\ \ge\ \delta>0,
\]
where \(\delta\) is the limiting product. Fix \(z\) so that \(2\sum_{p\in P,\ p>z}1/p<\delta/2\). Up to \(X\), a remaining modulus can contribute only if \(p\le\sqrt{6X+1}\), and then contributes at most \(2X/p+2\) indices. Their union therefore has size at most \(\delta X/2+O(\sqrt X)\). But the small-prime survivors number \(\delta_z X+O_z(1)\), by periodicity at **fixed** \(z\). A positive proportion remain uncovered. The square cutoff is what makes the accumulated endpoint errors harmless here.

**Second, a tail cover must use polynomially many distinct moduli within each sufficiently large square-scale budget.** For example, there is an absolute \(c>0\) such that for all sufficiently large integers \(X\),
\[
 \boxed{\quad
 \#\{p\in P:X^{1/5}<p\le\sqrt{12X+1}\}
 \ \ge\ c\,\frac{X^{1/5}}{(\log X)^2}.
 \quad}
\]

Here is the analytic input and why it applies. Use the dimension-two lower-bound beta sieve (Diamond–Halberstam–Richert), whose lower sifting limit \(\beta_2\) is less than \(4.3\). Sieve \(X<n\le2X\) by \(E_p\) through \(z=X^{1/5}\). For each squarefree \(d\) coprime to \(6\), the simultaneous-hit count is
\[
 X\,\frac{2^{\omega(d)}}d+O(2^{\omega(d)}),
\]
by CRT, where \(\omega(d)\) counts its distinct prime factors. The local product has dimension two by Mertens' theorem. At level \(D=X^{9/10}\) the summed remainder is \(O(D\log D)\), using \(2^{\omega(d)}\le\tau(d)\), the divisor count. This is negligible compared with \(X/(\log X)^2\), and \(\log D/\log z=4.5>\beta_2\). The lower-bound sieve thus leaves at least \(c_0X/(\log X)^2\) indices, for some \(c_0>0\), after **all** primes through \(z\).

If there is a tail cover, each such index needs a modulus in the displayed band: the lower endpoint follows from survival and the upper endpoint from proper first-factor size for \(C_p\). Each modulus there hits at most \(2X/z+2\) indices of the interval. Division gives the claimed bound. The same argument permits \(X^\alpha\) in place of \(X^{1/5}\) for fixed \(0<\alpha<1/\beta_2\), taking the level exponent sufficiently close to one.

This is a partial obstruction, not a shortage contradiction: the available band contains far more primes than the bound demands. What it rules out is a chase explained by a thin supply of additional covering moduli at these scales.

## 3. A comparison chase with the same primes, residues, and least-head rule

For (B), change **only the candidate domain**, to
\[
 \mathcal D=\{x^3/6:x\ge6,\ 6\mid x\}.
\]
Keep the actual forms \(6n\pm1\), enumerate the same primes in increasing order, and always take the least surviving \(n\in\mathcal D\).

* Every finite stage has a head. Choose \(x\) divisible by \(6\) and by every blocker. Then \(x^3\pm1\) avoid every blocker.
* Every head dies. Its first hitting prime is the least prime factor of \((x^3-1)(x^3+1)\), which the enumeration reaches in finite time.
* Every death is proper. Both members factor:
  \[
   x^3-1=(x-1)(x^2+x+1),\qquad
   x^3+1=(x+1)(x^2-x+1).
  \]

Thus the cubic construction used to witness unbounded scores also supplies a deterministic endless chase on a restricted domain. There is no adversary, no rearrangement of primes, and no failure of finite-stage survival. What this isolates is **not** a special property of the prime order that prevents a chase: that order is identical in both processes. A proof for CPNF must exploit the availability of indices outside the restricted domain, or equivalently arithmetic of the forms on the full interval that is lost under cubic substitution.

## 4. Where the coverage argument stops

At fixed modulus \(M\), a fresh prime \(q\nmid 6M\) hits exactly two of the \(q\) lifts of **each** old residue modulo \(Mq\). It neither kills nor spares that old residue as a whole. Thus the fixed-modulus argument fails before parity enters: it interchanges a prime for each representative with a finite set covering all representatives.

After repairing that error, the quantitative problem is different. The beta sieve proves many uncovered indices at \(z=X^{1/5}\). To force even one twin on \(X<n\le2X\) by the same strategy, it suffices to retain one index through \(z=\sqrt{12X+1}\); at this cutoff and for large \(X\), survival is **exactly** being a twin. At level near \(X\) the sifting ratio is then near \(2\), outside the positive lower-bound range used above. This is where coverage based on local divisibility counts encounters the classical lower-bound sieve barrier. It is not an impossibility theorem for every coverage proof.

**Ledger:** the ordered cover is exact; a convergent-reciprocal tail cover is impossible; a tail cover needs the stated band of additional moduli; and deterministic proper deaths forever are constructible on the cubic subdomain. What remains open is whether, on arbitrarily large full index blocks, the larger primes necessarily **miss at least one of the same indices** missed by the smaller primes. Neither the abundance of small-prime survivors nor the increasing order of their eventual killers proves that.
