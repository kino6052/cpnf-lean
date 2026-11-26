I would stop shrinking the budget and change what is counted. **My commitment is to a conditional finish:** a theorem from one explicit multiscale estimate to `∀ K, WindowWitness K`. The estimate is about one-dimensional prime counts in adjacent intervals. It has no twin predicate in it. Its difficulty is that the *fluctuations* of two such counts must be controlled together. I do not know an unconditional proof of that estimate.

The advantage over another equivalent formulation is that the proposed hypothesis is **stronger, quantitative, and falsifiable scale by scale**. There is also an exact identity to implement before attempting any estimate.

## 1. The idea: split the two columns before counting coincidences

Take \(N=2^t\), \(N\ge16\), and use the \(N\) rows \(N<n\le2N\). Mark them in two separate columns:
\[
 a_n=[N<\operatorname{minFac}(6n-1)],\qquad
 b_n=[N<\operatorname{minFac}(6n+1)].
\]
Here brackets are \(0\) or \(1\). These are **single-member** marks. On this block each member is greater than \(N\) and at most \(12N+1\le N^2\), so in each column a mark is exactly a prime. A common mark is already inside `window N`. There is no proper-power budget and no loss of residue classes.

Now bisect the block repeatedly. For each node \(I\) in the binary partition, write \(A_I,B_I\) for the two column totals, and \(L,R\) for its left and right children. Compute the signed integer
\[
 D_I=(A_L-A_R)(B_L-B_R).
\]
It is negative when the two columns favor opposite halves. The reason to compute this particular product is the exact identity
\[
 2(A_LB_L+A_RB_R)=A_IB_I+D_I.
\]
At depth \(d\), sum the \(D_I\) **with their signs first**, then weight by \(2^d\); call the result \(E_d\). Telescoping gives
\[
 \boxed{\quad N\,\#\{\text{common marks}\}
       = A_{\rm root}B_{\rm root}+\sum_{d<t}E_d.\quad}
\]

The root product is the signal that two **separate** prime-counting theorems can supply. The terms on the right tell us exactly how that signal can be lost as we resolve the two columns down to the same row. This is the new object I would build for CPNF. The binary covariance identity itself is elementary, not a claimed new theorem about primes.

## 2. Tonight’s file: the terminal interface and the split identity

This is the first code I would put in `CpnfLean/ColumnSplit.lean`. The first lemma specifies the terminal set exactly, rather than merely proving that a successful scan is sufficient. The second consumes it using the **same cutoff for the whole block**. The third is the internal-node arithmetic for the next phase. I have not run these snippets in your checkout.

```lean
import CpnfLean.Ladder

namespace CPNF

def loMarks (N : ℕ) : Finset ℕ :=
  (blk N).filter (fun n => N < (twinLo n).minFac)

def hiMarks (N : ℕ) : Finset ℕ :=
  (blk N).filter (fun n => N < (twinHi n).minFac)

theorem commonMarks_eq (N : ℕ) :
    loMarks N ∩ hiMarks N =
      (blk N).filter (fun n => N < score n) := by
  ext n
  simp only [loMarks, hiMarks, Finset.mem_inter, Finset.mem_filter,
    score, lt_min_iff]
  tauto

theorem windowWitness_of_commonMarks {K N : ℕ}
    (hK : K ≤ N) (hN : 16 ≤ N)
    (hm : (loMarks N ∩ hiMarks N).Nonempty) :
    WindowWitness K := by
  obtain ⟨n, hn⟩ := hm
  rw [commonMarks_eq] at hn
  obtain ⟨hb, hs⟩ := Finset.mem_filter.mp hn
  obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp
    (show n ∈ Finset.Ioc N (2 * N) from hb)
  have hsq : 16 * N ≤ N * N := Nat.mul_le_mul_right N hN
  have hw : n ≤ window N := by
    apply (le_window_iff (by omega : 1 ≤ N)).mpr
    omega
  exact ⟨N, n, by omega, by omega, by omega, hw, hs⟩

theorem column_split (aL aR bL bR : ℤ) :
    2 * (aL * bL + aR * bR) =
      (aL + aR) * (bL + bR) + (aL - aR) * (bL - bR) := by
  ring

end CPNF
```

In particular, `windowWitness_of_commonMarks` needs neither an asymptotic estimate nor a subsequent conversion of powers to primes. It is the end of the proof written first.

## 3. The phases and their acceptance tests

The following definitions specify the remaining interfaces. They go in `namespace CPNF` after the preceding code. `node t d j` is node \(j\) at depth \(d\), with the same open-left, closed-right convention as `blk`. Only depths `d ≤ t` and indices `j < 2^d` are used in the identity.

```lean
def node (t d j : ℕ) : Finset ℕ :=
  let N := 2^t
  let s := 2^(t-d)
  Finset.Ioc (N + j*s) (N + (j+1)*s)

def colCount (S : Finset ℕ) (t d j : ℕ) : ℤ :=
  ((S ∩ node t d j).card : ℤ)

def contrast (S : Finset ℕ) (t d j : ℕ) : ℤ :=
  colCount S t (d+1) (2*j) - colCount S t (d+1) (2*j+1)

def levelTerm (t d : ℕ) : ℤ :=
  (2 : ℤ)^d * ∑ j ∈ Finset.range (2^d),
    contrast (loMarks (2^t)) t d j *
    contrast (hiMarks (2^t)) t d j

def rootProduct (t : ℕ) : ℤ :=
  ((loMarks (2^t)).card : ℤ) * ((hiMarks (2^t)).card : ℤ)

def levelDebt (t : ℕ) : ℤ :=
  ∑ d ∈ Finset.range t, max 0 (-levelTerm t d)
```

**Phase A — exact multiscale identity. Unconditional.** Build on `column_split`. The deliverable has signature:

```lean
theorem column_telescope (t : ℕ) :
    (2 : ℤ)^t * ((loMarks (2^t) ∩ hiMarks (2^t)).card : ℤ) =
      rootProduct t + ∑ d ∈ Finset.range t, levelTerm t d
```

Proof plan: at depth \(d\) maintain \(2^d\sum_j A_jB_j\). For `d < t` the node length is twice the child length; its two `Ioc` children are disjoint and exhaust it. Apply `column_split` and reindex children by `2*j` and `2*j+1`. The last nodes are singletons, so their count products are exactly the indicators of intersection. This proof works verbatim for two arbitrary subsets of `blk (2^t)`; I would prove that generic version and specialize. Test empty columns, disjoint columns, and identical columns, not only prime data.

**Phase B — supply the marginal signal. Unconditional mathematics; an analytic formalization deliverable, not a theorem I found in the attachments.**

```lean
theorem marginal_supply :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → 0 < rootProduct t
```

Use the prime number theorem in the two *fixed* arithmetic progressions \(5,1\bmod 6\). Primes in the respective intervals \((6N-1,12N-1]\) and \((6N+1,12N+1]\) give exactly the two column counts for \(N\ge16\). Each count is asymptotic to \(3N/\log N\): subtract the two endpoint estimates for its own residue class. Thus each is eventually positive. No joint prime estimate is used. This phase can be developed against a PNT-in-progressions theorem parameter until that theorem and its dependencies have been checked in the chosen toolchain.

**Phase C — bound the loss. Open.** Here is the precise research hypothesis I would try, with the constant fixed in advance:

```lean
def CofinalHalfDebt : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
    2 * levelDebt t ≤ rootProduct t
```

This definition specifies a conjecture; it does not establish it. The ordering of the operations matters. Taking negative parts **node by node** discards cancellation among intervals of the same length. Taking the negative part **after summing all depths** would largely turn the assertion back into a lower bound on the answer. The proposed intermediate choice lets opposite node contributions cancel within a depth, but demands that positive depths need not rescue the negative ones.

The first investigation should be to compute the vector \(E_d/(A_{\rm root}B_{\rm root})\) on successive blocks, using prefix sums of the two prime columns. Inspect it by **child length** \(2^{t-d-1}\), not just by depth. This gives a concrete decision about where to invest proof effort: for long children one can try bounds for errors in prime counts in intervals; for short children one must estimate the *signed sum of products*, which expands into counts at specific shifts. An absolute bound on every node fluctuation is not a substitute. If the negative parts systematically consume the proposed margin, revisit Phase C before formalizing such estimates. Finite experiments cannot certify cofinality.

I am not claiming a derivation of Phase C from RH. No Lean RH theorem or dependency audit for one is supplied here; even granting RH, separate error estimates for prime counts do not by themselves give this signed short-scale correlation. Nor would I use the paper’s fixed-modulus covering step: a new prime coprime to the frozen modulus splits the **lifts** of an old class, not the old classes into hit and unhit classes.

**Phase D — finish. Conditional only on Phase C once B is in place.** The two target signatures are:

```lean
theorem twice_common_ge_root {t : ℕ}
    (h : 2 * levelDebt t ≤ rootProduct t) :
    rootProduct t ≤
      2 * ((2 : ℤ)^t * ((loMarks (2^t) ∩ hiMarks (2^t)).card : ℤ))

theorem boxed_of_halfDebt (H : CofinalHalfDebt) :
    ∀ K : ℕ, WindowWitness K
```

The first follows because \(E_d\ge-\max(0,-E_d)\) term by term. The telescope therefore gives \(N\,\#\text{common}\ge AB-\text{debt}\ge AB/2\). For the second, given `K`, ask `H` for a depth beyond the marginal-supply threshold and large enough that \(2^t\ge\max(K,16)\). Positive root product forces positive intersection cardinality; `windowWitness_of_commonMarks` finishes. Your existing `windowWitness_iff_oftenDirect` and `oftenDirect_iff_unboundedTwins` then deliver the classical conclusion.

**What this commits us to proving is unambiguous.** With the marginal asymptotics, the half-debt bound would give order \(N/\log^2 N\) common marks on the selected blocks, not merely one witness. That is why it is a substantive conjectural estimate rather than a new name for infinitude. The price of the plan is precisely Phase C. Its benefit is that one can now prove the identity, verify the extraction, supply the marginal signal, and isolate which interval lengths lose that signal—all without claiming to have proved the one estimate that would settle the problem.
