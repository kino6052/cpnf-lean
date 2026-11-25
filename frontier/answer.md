**The readout reframes twin primality; it does not, on the stated lemmas, prove it.** The first result I would formalize is a *bridge theorem*: on the canonical run from the empty blocker set, non-stagnation of the least-index readout is equivalent to unboundedness of ordinary twin primes. This is a theorem about the semantics, not an appeal to the twin prime conjecture. It tells you exactly what a proposed bypass would have to prove.

### 1. What input is missing?

Write \(B_k\) for the blockers, \(y_k=\max B_k\) at nonempty stages, and \(A_k\) for the admissible positive indices in \([1,W(y_k)]\). The missing statement is **cofinal window nonemptiness**:
\[
\forall K\;\exists k\ge K,\quad A_k\ne\varnothing.
\]
You do **not** need nonemptiness at every stage. You do need a witness in the actual initial segment, not somewhere in a period.

Here is the bridge proof, using `Nat.Prime` only in the *external correctness theorem*, not in the process definition.

* **Canonical-prefix invariant.** \(B_k\) is the initial segment of the primes through \(y_k\). Inductively, the next prime survives, and every smaller integer at least 2 has a prime divisor already in the prefix. Thus the least survivor is exactly the next prime.
* **Window exactness.** For \(1\le n\le W(y_k)\), membership in \(A_k\) is equivalent to \(6n-1,6n+1\) both being primes greater than \(y_k\). A composite member would have a prime divisor at most its square root, hence at most \(y_k\); a prime member at most \(y_k\) would itself be a blocker. The converse is immediate.
* **Non-stagnation implies unbounded twins.** Each nonempty stage reads out a twin pair above \(y_k\), and the stage maxima increase without bound. Repeated readout of an index does not invalidate this implication.
* **Unbounded twins imply non-stagnation.** For a sufficiently large twin pair \(p,p+2\), take the stage whose maximum \(y\) is the prime immediately preceding \(p\). By Bertrand’s postulate, \(p<2y\), so \(p+2\le y^2\) for \(y\ge3\). The pair has form \(6n\pm1\) and witnesses \(A_k\ne\varnothing\). Such stages are unbounded. The readout need not choose *that* witness: it chooses some witness, which suffices.

Bertrand here is an elementary, unconditional size bound used in the **converse** to ensure visibility. It does not supply twins.

There is no known proof of cofinal nonemptiness for this window. There is also no justification for saying that *analytic* input is logically unavoidable. What is unavoidable is arithmetic control strong enough to place an admissible index in these particular windows cofinally often. To see why the qualitative process properties are insufficient, keep the **identical** least-survivor trajectory but use the finite, monotone, unbounded window \(W'(y)=\lfloor(y-1)/6\rfloor\). Its readout is always empty: both members are at most \(y\), hence blocked. This does not refute the quadratic-window claim; it shows that a proof must use more than the qualitative properties listed.

### 2. What does “without foresight” buy?

The true precise statement is the canonical-prefix invariant. There is no adversary choosing the next blocker, but there is also no randomness or independence: there is one trajectory. “The blockers cannot be chosen adversarially” does not imply “the unique trajectory avoids a bad configuration.”

Distinguish two covering claims:

* **Cover all integer lifts** of the old admissible residues by finitely many new prime blockers: impossible, regardless of the selection rule. Take a positive index divisible by every old and new blocker. Both members are then \(\pm1\) modulo each blocker. In fact CRT gives a surviving lift of **each** old admissible class for new primes coprime to the old modulus.
* **Cover every index of the current window**: a different proposition. The CRT witness can be outside the window. Whether the canonical trajectory can have such covers at *every sufficiently late stage* is exactly the stagnation question, not something already ruled out by determinism.

The relation between consecutive blockers from Bertrand is useful for visibility of existing twins. It gives no twin pair by itself.

### 3. Exact density-free counting

Yes. Use finite inclusion-exclusion with **exact endpoint terms**. For a finite set of prime blockers discard 2 and 3, which kill no index, and call the remainder \(P\). For \(S\subseteq P\), put \(d_S=\prod_{q\in S}q\). Let \(T_S\subseteq\{1,\ldots,d_S\}\) represent the CRT classes satisfying
\[
6r\equiv 1\ \text{or}\ -1\pmod q \qquad(q\in S).
\]
There are exactly \(2^{|S|}\) classes, since the two choices are distinct for each \(q>3\). For \(S=\varnothing\) use \(d_S=1,\ T_S=\{1\}\). Then the exact survivor count in \([1,W]\) is
\[
\boxed{\displaystyle
\sum_{S\subseteq P}(-1)^{|S|}
  \sum_{r\in T_S}\left\lfloor\frac{W+d_S-r}{d_S}\right\rfloor .}
\]
The inner term counts \(r,r+d_S,\ldots\) through \(W\). Inclusion-exclusion removes the union of the kill sets. For Lean, prove the one-progression count in `ℕ`, then cast to `ℤ` for the alternating sum. This is valid even when \(W<d_S\), precisely where replacing the count by a period average loses the needed information.

For the CRT layer alone, the simpler exact lemma is: on adding a fresh \(q>3\), **each old admissible class has \(q\) lifts, exactly two killed and \(q-2\) retained**. They are classes modulo \(Mq\), not classes eliminated modulo \(M\). This gives the full-period count without logs. Neither exact formula by itself proves positivity in the quadratic window.

### 4. Where is the bypass?

There is no demonstrated bypass lemma. Window exactness identifies the point where the supposed semantic difference disappears: **inside the certification window, the negative divisibility test is already an exact primality test**. Not mentioning the number of prime factors changes neither the surviving set nor the witness required. A new combinatorial proof of cofinal window nonemptiness would be a genuine bypass; changing the vocabulary or computing a full-period cardinality is not one.

### 5. How to restructure Section 4

1. Prove the canonical-prefix invariant, window exactness, and the bridge theorem. Keep persistent **records** separate from current admissibility.
2. Replace Lemma 11 by the exact lift lemma above. Drop the \(2M_0/q\) old-class elimination statement as described: a new prime partially kills lifts, not whole old classes.
3. Replace Lemma 12 in the core development by the exact full-period product. Add the finite-window formula if you want an executable counting specification. Move Mertens out of the proof of progress: even a perfect full-period count is not a lower bound of the required kind on the initial window.
4. **Drop Theorem 13’s inference from stagnation to a fixed finite cover**, absent a separate proof. Stagnation says that for each late \(k\), every index *in that stage’s window* is killed by some blocker in \(B_k\). Both the domain and the available blockers depend on \(k\). It does not furnish one finite family covering all lifts of \(R_0\). Finiteness of \(R_0\) does not repair the inference, because killing a representative does not kill its class.
5. For D.2, retain global finite noncovering as the short CRT lemma in §2 above if that is the intended domain. If the intended domain is the moving window, state the exact local claim separately and leave cofinal nonemptiness open. Do not transfer a noncovering result between those domains.

The useful formalization endpoint is an **unconditional equivalence theorem plus an isolated open proposition**. It pinpoints the gap more sharply than a density estimate: the issue is not whether admissible residues exist, but whether one of their positive representatives arrives before the certification cutoff, cofinally often.