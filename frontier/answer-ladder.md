The strongest rung I would add is a **residue-class version of the top-band exclusion**. It lets you pre-sieve by any fixed set of small primes and *still* exclude the top band on a positive fraction of the pre-sieved rows. Thus, under no witness, you can force many **middle-band** deaths, not merely many deaths. What you cannot do is rule those deaths out.

Below are theorem specifications and proof plans, not a report of a Lean build. The attachments contain neither a character definition nor a `chen_charge_exact` signature, so for that rung I give the sign convention explicitly.

## 1. `chen_charge_exact`: charge to the unique positive-sign factor

Here is a finite-table formulation. Let `H z : ℕ`, `I : Finset ℕ`, and let `s : ℕ → ℤ` be a sign table, of which only entries up to `H` are used. Equivalently use an array indexed by `Fin (H+1)`. The only table laws needed are
\[
 s(a)\in\{-1,0,1\}\quad(a\le H),\qquad
 s(ab)=s(a)s(b)\quad(1\le a,\ 1\le b,\ ab\le H).
\]
These are bounded arithmetic hypotheses, not distribution hypotheses. For a concrete character they are discharged by its multiplication law; for example the table \(0,1,-1\) indexed by residue modulo \(3\) works by nine residue cases.

Write \(m(n)=\texttt{twinHi}\ n,\ u(n)=\texttt{twinLo}\ n\); the entire statement also works with the two interchanged. Define
\[
\begin{split}
 A=\{n\in I:\;&1\le n,\ u(n)\text{ prime},\ m(n)\le H,\ s(m(n))=-1,\\
 &m(n)\text{ prime}\ \lor\
   \exists a,b\in[z+1,H],\ a,b\text{ prime},\ m(n)=ab\},\\
 P&=\{n\in A:\texttt{score}\ n=\texttt{twinLo}\ n\},\\
 Q&=\{q\in[z+1,H/(z+1)]: q\text{ prime},\ s(q)=1\},\\
 D_q&=\{n\in A\setminus P:q\mid m(n)\}.
\end{split}
\]
All intervals are natural-number `Finset.Icc`, and `/` is natural division. If desired, spell every prime test as `2 ≤ p ∧ p.minFac = p`. The exact theorem is
\[
                      \boxed{|A|=|P|+\sum_{q\in Q}|D_q|.}
\]
This is a natural-number equality, hence also an integer identity by casting. It makes **no** assertion that the selected set is large. For a nonvacuous use of the mod-\(3\) example take \(m=\texttt{twinLo}\), not `twinHi`.

**Proof and dependencies.** By `twin_iff_score_eq_lo`, a nonpassing selected row has \(m=ab\) in the second branch. Since \(s(a)s(b)=-1\), exactly one factor has sign \(+1\); call it \(q\). Its complementary factor is at least \(z+1\), so `Nat.le_div_iff_mul_le` puts \(q\) in `Q`. Any prime dividing \(ab\) divides \(a\) or \(b\), hence equals one of them. Thus there is exactly one `q ∈ Q` charging this row. In Lean one can sum the indicator of `q ∣ m n` over `Q` first (sum \(=1\) by uniqueness), then use `Finset.sum_comm` to sum over rows first. Add back `P`. No ordering of the two factors and no choice of a factorization function is needed. The **negative** sign of the product matters: for a positive product there can be zero or two positive-sign prime factors. Merely writing “character-selected” would not justify this identity.

## 2. `topBand_on_class`: an explicit \(19/20\) bound

Use the following finite sets:
```lean
def block (X : ℕ) := Finset.Ioc X (2*X)

def band (X : ℕ) :=
  (Finset.Icc 2 (Nat.sqrt (12*X+1))).filter
    (fun q => Nat.Prime q ∧ X < q*q)

def classBlock (X M r : ℕ) :=
  (block X).filter (fun n => n % M = r)

def topHits (X : ℕ) (S : Finset ℕ) :=
  S.filter (fun n => ∃ q ∈ band X, q ∣ twinLo n ∨ q ∣ twinHi n)
```

Here are sufficient explicit constants; no “sufficiently large” quantifier is needed. Put \(k=\lfloor\sqrt X\rfloor/210\) using natural division, \(a=210k\). Take \(7\le k,\ 1\le M,\ r<M\), put \(S=\texttt{classBlock}\ X\ M\ r,\ L=|S|,\ U=|\texttt{topHits}\ X\ S|\), and suppose every \(q\in\texttt{band}\ X\) is coprime to \(M\). The more useful theorem, *before* rounding it to \(19/20\), is
\[
\begin{split}
 U &\le 96k\,(L/a+1)+192k\,(L/(2a)+1),\\
 210U &\le 192L+210\cdot288k.
\end{split}
\]
In particular,
\[
              8064k\le L\quad\Longrightarrow\quad 20U\le19L.
\]
**Ordinary block corollary:** for \(X\ge1470^2\), take \(M=1,\ r=0,\ L=X\). Then \(X\ge (210k)^2\ge8064k\). This proves the requested \(19/20\) exclusion with a specified lower threshold; no small-\(X\) computation is included in that threshold.

**Proof and dependencies.** Since \(a^2\le X<(210(k+1))^2\) and \(k\ge7\), every band prime lies in \((a,4a]\): for the upper endpoint use \(k+1\le8k/7\) and \(12\cdot8^2<16\cdot7^2\). Split at \(2a\). The two intervals consist of respectively \(k\) and \(2k\) **blocks of length 210**. Each such block contains exactly 48 integers coprime to 210, and every band prime is among them. In the progression \(S\), write the rows in order as \(n_0+Mj,\ 0\le j<L\) (handle \(L=0\) separately). Since \(6M\) is invertible modulo \(q\), each of the two hits occupies at most one residue class of \(j\bmod q\). Each class occurs at most \(L/q+1\) times. Sum these bounds, allowing overlaps. This gives the first inequality. For the second, use \(a(L/a)\le L\) and \(2a(L/(2a))\le L\) **before** cancelling factors; no rational arithmetic is necessary. The \(8064\) is exactly the solution of \(20(192L+210\cdot288k)\le19\cdot210L\).

The ingredients to formalize are `CPNF.progression_card` (or its translated upper-bound corollary), `Finset.card_bij` for class parametrization, and `Finset.card_biUnion_le` for the union bound. The wheel computation itself is a closed Lean goal:
```lean
example : ((Finset.Icc 1 210).filter (fun b => Nat.Coprime b 210)).card = 48 := by
  decide
```
Translation by \(210j\) preserves the gcd. There is **not** a bound of 48 primes per dyadic interval of arbitrary size; the dyadic intervals here have bounds \(48k\) and \(96k\). Confusing these units would give an incorrect theorem.

## 3. `middle_or_pass`: a pigeonhole consequence that survives pre-sieving

Here is a finite near-witness result that uses rung 2. For **any** \(z,K\), set
\[
 M=(z+1)!,\qquad k=\max(7,\max(K,M)),\qquad
 X=(210k)^2,\qquad S=\texttt{classBlock}\ X\ M\ 0.
\]
Partition \(S\) into
\[
\begin{array}{ll}
 P:&\texttt{score}\ n=\texttt{twinLo}\ n,\\
 D:&\texttt{score}\ n\ne\texttt{twinLo}\ n\ \land\ 
                         (\texttt{score}\ n)^2\le X,\\
 E:&\texttt{score}\ n\ne\texttt{twinLo}\ n\ \land\
                         X<(\texttt{score}\ n)^2.
\end{array}
\]
Then the unconditional conclusions are
\[
\begin{gathered}
 \forall n\in S,\quad K\le n\ \land\ z<\texttt{score}\ n,\\
 |S|=|P|+|D|+|E|,\qquad
 20|E|\le19|S|,\qquad |S|\le20(|P|+|D|).
\end{gathered}
\]
In particular **if there is no window witness beyond \(K\)**, then
\[
                |S|\le20|D|.
\]
Every one of these forced rows has a prime killer \(q=\texttt{score}\ n\) with \(z<q,\ q^2\le X\). This is stronger than forcing small-prime hits among *all* indices: the forced killers here exceed **any preassigned** \(z\). The no-witness premise is not needed to compile the partition or the inequalities.

**Proof and dependencies.** Every \(2\le d\le z\) divides \(M\), hence divides \(6n\) throughout \(S\). Apply `not_dvd_pred_of_dvd`, `not_dvd_succ_of_dvd` and `minFac_gt_of_no_small_dvd`. Each band prime exceeds \(210k\ge M\), so is coprime to \(M\). There are at least \(X/M\ge44100k\) multiples of \(M\) in \((X,2X]\): the exact count is \(2X/M-X/M\) with divisions performed before subtraction. Thus rung 2 applies. For \(n\in E\), `score_sq_le_hi_of_gt` and `score_le_lo` give \(X<q^2\le\texttt{twinHi}\ n\le12X+1\); unfolding `min` and using `Nat.minFac_prime` and `Nat.minFac_dvd` gives the band hit. So \(E\subseteq\texttt{topHits}\ X\ S\). The remaining inequalities are partition arithmetic. Finally each \(n\in P\) supplies a witness by `twin_iff_score_eq_lo` and `window_witness_of_twin`.

This is a necessary consequence of no witness, **not a combinatorial impossibility**. In fact the cutoff \(z\) is fixed *before* making \(X\) large enough for the progression count. Substituting \(z=\lfloor\sqrt X\rfloor\) afterwards is invalid. That order of choices is where a tempting CRT proof fails.

## 4. Exact local endpoint and the open step

For the sharpest **lossless** version, drop the progression restriction and take \(S=(X,2X]\), \(X\ge1\). Fix any \(0\le z\le\lfloor\sqrt X\rfloor\). Compute three finite sets:
\[
\begin{aligned}
 R &= \{n\in S:z<\texttt{score}\ n\},\\
 B &= \{n\in R:(\texttt{score}\ n)^2\le X\},\\
 T &= \{n\in R:X<(\texttt{score}\ n)^2\le\texttt{twinHi}\ n\}.
\end{aligned}
\]
The last local theorem I would compile is
\[
 \boxed{\quad |B|+|T|<|R|
        \quad\longleftrightarrow\quad
        \exists n\in S,\ \texttt{score}\ n=\texttt{twinLo}\ n.\quad}
\]
Indeed the **slack is exactly the number of passing rows**, not just an upper or lower bound. A passing row has score \(6n-1>\lfloor\sqrt X\rfloor\), so it belongs to \(R\); a failing row of \(R\) falls in exactly one of \(B,T\) by `sq_test_iff` and `score_le_lo`. Conversely rows in \(B\) fail because \(X<\texttt{twinHi}\ n\), and rows in \(T\) fail by the square test. This proof needs only filter partitions and the cited pointwise lemmas. Charging by `score` rather than all dividing primes avoids any inclusion–exclusion loss.

**The first unproved assertion on this route** is that this strict inequality occurs on blocks arbitrarily far out. It is equivalent to the boxed target: a strict block supplies a twin and hence a window witness; given a sufficiently large witness at \(n\), take \(X=n-1\) to place that row in the open-left block. Even \(z=0\) suffices for the equivalence. Rung 2 bounds \(T\) against the whole block; rung 3 can do so on a fixed pre-sieved progression. Neither bounds \(B\) against the rows left over. Likewise rung 1 counts the charges exactly but gives no strict surplus of selected rows over charges.

There are two precise limits to the requested “nothing weaker suffices”:

* **For this local count**, slack one suffices; slack zero means no passing row. That is an optimality theorem, by the identity itself.
* **For proof methods**, there is no justification for saying an analytic estimate is *necessary*. A cofinal strict surplus here would be a twin-prime theorem however proved. And if `¬ WindowWitness K` implied a finite condition which you could also prove impossible for every \(K\), those two Lean theorems together would already prove the conjecture. A fixed modulus does not supply that contradiction: a new \(q\nmid M\) cuts a progression *within* each old residue, not whole residues modulo \(M\).

**Ranking.** By actual exclusion, rung 3 is strongest: it combines small-factor avoidance with a quantitative top-band bound on the *same rows*. Rung 2 supplies the numerical gain. Rung 1 removes double counting on a selected family but guarantees no rows. Rung 4 is closest by logical equivalence and closes no distribution gap; it specifies exactly what a further argument would have to make positive.
