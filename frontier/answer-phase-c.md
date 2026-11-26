**I would drop half-debt and change what is propagated down the tree.** At each node \(I\), propagate a *lower bound on overlap*, not a product of counts:
\[
L(I)=\max\{0,\ |S\cap I|+|T\cap I|-|I|\}.
\]
The point is that \(L(I_L)+L(I_R)\ge L(I)\): a positive lower bound, once found, can never be lost to a finer scale. At singletons the bound is exact. This gives a telescope with **nonnegative corrections** and a local certificate: one overloaded node at any depth finishes the block, without paying for negative contrasts elsewhere. The arithmetic question becomes whether one can detect such an overload cofinally *before* resolving singletons. I can prove the propagation and the certificate, not that arithmetic assertion.

### 1. The exact threshold in the existing telescope

Write \(R=\texttt{rootProduct t}\), \(E_d=\texttt{levelTerm t d}\), \(D=\sum_d\max(0,-E_d)\), and \(P=\sum_d\max(0,E_d)\), with \(d<t\). The weight \(2^d\) is **already included** in `levelTerm`. For the two mark sets, the root and singleton evaluations of Phase A give
\[
2^t\,\#(S\cap T)=R+\sum_{d<t}E_d=R+P-D.
\]
Thus the **necessary and sufficient** block condition is \(D<R+P\), or equivalently `0 < rootProduct t + ∑ d ∈ Finset.range t, levelTerm t d`. Cofinality of this strict inequality is the minimal signed hypothesis. If one insists on throwing away \(P\), then \(D<R\) suffices. Half-debt with \(R>0\) implies this; without root positivity, the numerical test admits the vacuous case \(R=D=0\). I do not know a proof or disproof of cofinal half-debt for the actual prime columns.

There is a sharp reason not to expect a purely marginal estimate to do the job. In a block of even length \(N\), mark the first row of each sibling pair in \(S\) and the second in \(T\). Both columns are **perfectly balanced at every split above the last**, yet the last weighted contrast is \((N/2)(-N/2)=-R\). The intersection is empty. Moving each \(T\)-mark to its sibling preserves all counts down to depth \(t-1\) and changes the last term to \(+R\). This isolates precisely the information a bound on coarse fluctuations is missing.

### 2. The first lemma I would compile

Use a third finset `U` for capacity. For the basic construction `U = blk (2^t)`; allowing a tighter `U` costs nothing in the propagation proof. Here is the proposed file fragment (not run here):

```lean
import CpnfLean.ColumnTelescope

namespace CPNF

def forced (S T U : Finset ℕ) (t d j : ℕ) : ℤ :=
  max 0 (colCount S t d j + colCount T t d j - colCount U t d j)

theorem forced_le_children (S T U : Finset ℕ) (t d j : ℕ)
    (hd : d < t) :
    forced S T U t d j ≤
      forced S T U t (d+1) (2*j) +
      forced S T U t (d+1) (2*j+1) := by
  unfold forced
  rw [colCount_split S t d j hd, colCount_split T t d j hd,
      colCount_split U t d j hd]
  omega

end CPNF
```

The identity behind this lemma is more informative than the inequality. Put \(x_I=|S\cap I|+|T\cap I|-|U\cap I|\) and \(x^+=\max(0,x)\). Then \(x_I=x_L+x_R\), and the gain is exactly
\[
g(I)=x_L^++x_R^+-(x_L+x_R)^+
=\begin{cases}
\min(|x_L|,|x_R|), & x_Lx_R<0,\\
0,&\text{otherwise}.
\end{cases}
\]
This follows by splitting on the signs and, for opposite signs, on which magnitude is larger. If \(S\cup T\subseteq U\) and all sets are in the block, a leaf has `forced = 1` exactly on \(S\cap T\), and zero otherwise. Summing the gains therefore gives the alternative exact telescope
\[
\#(S\cap T)=L(\mathrm{root})+\sum_{\text{internal }I}g(I),
\qquad L(I)=x_I^+.
\]
There are no weights and no negative terms. The gain measures how much excess in one child was concealed by unused capacity in its sibling.

### 3. The Phase C interface and the finish

This is the local hypothesis I would use. Its allowing \(d=t\) is deliberate: it keeps the interface **lossless** rather than silently requiring twin clusters.

```lean
namespace CPNF

def CofinalNodeOverload : Prop :=
  ∀ T₀ : ℕ, ∃ t d j : ℕ,
    T₀ ≤ t ∧ d ≤ t ∧ j < 2^d ∧
    0 < forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j

end CPNF
```

The lemma chain does not need the entire alternative telescope:

1. **`common_of_forced_pos`**: if \(S,T\subseteq U\) and `0 < forced S T U t d j`, then `(S ∩ T).Nonempty`. Indeed, if the intersection were empty, \(S\cap I\) and \(T\cap I\) would be disjoint; their union is contained in \(U\cap I\). `Finset.card_union_of_disjoint` and `Finset.card_le_card` contradict strict overload. This lemma needs **no** depth or node-index hypothesis.
2. **`boxed_of_cofinalNodeOverload (H : CofinalNodeOverload) : ∀ K : ℕ, WindowWitness K`**: apply `H (max K 16)`. Both inclusions into `blk` are `Finset.filter_subset`. Step 1 gives the nonempty intersection; `windowWitness_of_commonMarks` finishes since \(K,16\le t\le 2^t\).
3. Apply `windowWitness_iff_oftenDirect.mp` and `oftenDirect_iff_unboundedTwins.mp` for the classical conclusion.

Conversely, any common row \(n\) overloads the singleton `node t t (n - 2^t - 1)`. And any twin row \(n>1\) gives a common mark in its unique dyadic block: both members exceed the block cutoff and `minFac_eq_self_of_prime` applies. Thus `CofinalNodeOverload` is **equivalent to unbounded twins**, not an independent reason to believe they have been proved.

**Where I would look for a new estimate.** Do not try to overload a long interval using its full length as capacity: most rows in it cannot carry either mark. Instead use a small wheel that excludes rows known to fail **both** columns. For example, at \(N\ge 16\) remove from `blk N` the rows satisfying
\[
(5\mid 6n-1\ \land\ 7\mid 6n+1)
\quad\text{or}\quad
(7\mid 6n-1\ \land\ 5\mid 6n+1).
\]
Call the remainder \(U\). Each removed row fails both marks by `Nat.minFac_le_of_dvd`, so \(S\cup T\subseteq U\), and `forced_le_children` applies unchanged. These are two distinct classes modulo 35, hence every full 35-row interval gets **two units of capacity reduction**, unconditionally. A larger finite wheel can use the same rule: exclude a row only when it has a divisor certificate on *each* side. The new estimate would be a strict local excess of the two prime counts over this reduced capacity on cofinally many nonsingleton nodes. The wheel saving is provable; the strict excess is not established. In particular it would be a mistake to extrapolate the two-unit saving into a twin lower bound.

### 4. Exactly where an explicit formula would enter

There is no accepted proof of RH, in Lean or otherwise, and the supplied files provide no theorem proving it. Moreover, the relevant one-column estimates are for primes in the two reduced classes modulo 6; a GRH route to square-root errors would involve the corresponding Dirichlet \(L\)-functions, not just zeta.

One can specify the interface without assuming any such theorem. For \(s=\pm1\) let \(F_s(u)=\pi(6u+s;6,s\bmod 6)\), where \(\pi(x;q,a)\) counts primes at most \(x\) in class \(a\bmod q\). For a valid node \((a,c]\) with midpoint \(b\), and \(N\ge16\), its column contrast is exactly
\[
\Delta F_s=2F_s(b)-F_s(a)-F_s(c).
\]
Suppose a theorem supplies \(F_s=M_s+e_s\) with \(|e_s(u)|\le B_s(u)\) at those endpoints. Then
\[
|\Delta F_s-\Delta M_s|
\le B_s(a)+2B_s(b)+B_s(c)=:Q_s.
\]
In **one node product**, the error relative to \(\Delta M_-\Delta M_+\) is at most
\[
|\Delta M_-|Q_+ + |\Delta M_+|Q_- + Q_-Q_+.
\]
Sum this over nodes and multiply by \(2^d\) to bound the error in one `levelTerm`. This retains the main-term curvature rather than assuming equal-length children have equal expected counts. At the sibling scale, however, even square-root endpoint bounds are far larger than the individual contrasts, which are just \(-1,0,1\). They provide no useful sign for their product. No known implication from RH or GRH supplies the missing fixed-shift lower bound.

So the unconditional deliverable is a **local overlap certificate with monotone refinement and exact nonnegative gains**. The conditional finish is sharp. The unsolved step is producing a cofinal certificate for the prime columns, not proving that a certificate, once produced, survives refinement.
