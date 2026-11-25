1. **Prove `certify_prime` first**, in `Correspondence.lean`, after `certify_le_of_dvd`:

   ```lean
   theorem certify_prime (k : ℕ) : Nat.Prime (certify k) := by
     have hm := certify_survives k
     refine Nat.prime_def_lt.mpr ⟨hm.1, ?_⟩
     intro d hdlt hdvd
     by_contra hne
     have hd0 : d ≠ 0 := by
       intro h
       subst d
       simp at hdvd
       omega
     have hd2 : 2 ≤ d := by omega
     exact (not_lt_of_ge (certify_le_of_dvd hm hdvd hd2)) hdlt
   ```

   Why: a proper divisor other than `1` would itself be a sieve member strictly below the least sieve member. This is a proposed proof, not a report of a Lean run.

2. **Use prime enumeration to eliminate the stage scan.** Yes, Lever 1 is correct, including “in order,” though that last part needs a no-skipping argument. The next proposed lemma is
   \[
   q\in\texttt{stage}\ k\quad\longleftrightarrow\quad q.\mathrm{Prime}\ \land\ q<\texttt{certify}\ k.
   \]
   Forward: use `mem_stage_iff`, step 1, and `blocker_lt_certify`. Backward: if a prime \(q<c=\texttt{certify}\ k\) were absent, no blocker could divide it: a blocker is at least 2, so a blocker dividing \(q\) would equal \(q\). Thus `next_le` gives \(c\le q\). Together with `certify_ge_idx`, this leaves no prime permanently unenumerated.

   One correction matters for the computation: `Direct k` does **not** mean that \(c\) is *either* member of some twin pair. It means it is the **lower** member of the head pair. Indeed `next_le` gives \(c\le\texttt{twinLo (head k)}\), ruling out the upper disjunct. For example, enumerating 7 is not a second direct stage for \((5,7)\).

3. **Replace the two scans by one record computation.** This is the feature I would investigate: not prime enumeration or decidable deaths separately, but the fact that the head is a **first crossing**. For positive \(n\), define the executable score
   \[
   s(n)=\min\bigl(\operatorname{minFac}(6n-1),\operatorname{minFac}(6n+1)\bigr).
   \]
   The proposed finite lemma is
   \[
   \texttt{head}\ k\le N
   \quad\longleftrightarrow\quad
   \exists n,\quad 1\le n\le N\ \land\ \texttt{certify}\ k\le s(n).
   \]
   Proof route: by step 2 a member survives exactly when its least prime factor is at least \(c\); then use `head_le` in one direction and `head_spec` in the other.

   In particular, keep only **strict prefix records** of \(s\). If the previous record score was \(a\) (use \(0\) initially) and the new record at \(n\) has score \(b\), this one row specifies the head for **every** certified prime \(a<c\le b\). All earlier indices have score at most \(a\), and \(n\) survives up to and including threshold \(b\). Its death is exactly at \(c=b\). This computes even the *indirect* deaths, without evaluating either noncomputable scan stage by stage. I would not claim a literature priority for this; of the four features, it is the **second leastness scan, coupled to the first**, that gives the most useful experiment here.

4. **Attack the square bound at record endpoints, not at every stage.** For a record row \((n,b)\), the clean bound to test is exactly
   \[
   n\le \left\lfloor\frac{b^2-2}{6}\right\rfloor.
   \]
   The `−2` is intentional: the test is \(6n+1<b^2\), not \(6n+1\le b^2\). The endpoint is the easiest stage on its plateau at which to pass the test: the head is fixed and the killer is largest. There is no reason to demand a linear bound or a bound at the start of every plateau.

   **A partial target with a different payoff:** certify how far the *next* direct death can be from a given record by testing a finite extension of the prefix. Given the current record score \(a\), search \(L<n\le N\) beyond the processed prefix \(1,\ldots,L\) for **any** row satisfying
   \[
   s(n)>a,\qquad 6n+1<s(n)^2.
   \]
   No record check on the proposed witness is necessary. To see why, put \(b=s(n)\), and take the **first** \(m\le n\) with \(s(m)\ge b\). Then \(m>L\), \(m\) is a strict record, and
   \[
   6m+1\le 6n+1<b^2\le s(m)^2.
   \]
   Hence its endpoint death passes the strict-size test. The output proves that there is a direct death with head in \((L,N]\). Conversely, if the exact scan finds no such witness, it proves there is **no** direct death with head in that interval: a direct record is itself a witness, since its score is \(6m-1\ge5\). Thus a failed bounded search has a mathematical interpretation too, not just a timeout.

5. **Separate the checker from the conjecture.** I would implement the finite record scan on `Nat.minFac`, prove its prefix invariant once, and have Lean check concrete tables by bounded reduction or by checking externally supplied factor certificates. A claimed exact `minFac` needs a minimality check, not merely a divisor. The invariant and a checked table yield a theorem about *all* the head plateaus and deaths represented by that prefix.

   **Conjectural step:** from every completed record prefix, some finite extension contains a row passing the test in step 4. I know no termination proof for that search. The precise obstruction is visible in the score: if either member is composite, its least prime factor is at most its square root, so the row cannot pass. Leastness lets you compress stages, certify whole intervals, and transfer a witness to an endpoint; it does not supply the next passing row. That is why I would build the record checker before pursuing a global head estimate: it delivers a new finite theorem even if the proposed infinite search never acquires a termination proof.
