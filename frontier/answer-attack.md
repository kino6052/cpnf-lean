**Reduction (option 4): for the fixed target with `U = blk`, every node of length at least \(1024\) has `forced = 0`.** Thus positive overload requires
\[
                         t-d\le 9.
\]
This removes six more levels from the stated search. It rules out overload *at those levels*, not just the need to visit them on a search that descends to leaves.

The key is to prove a bound at **one exact width**, then tile. At width \(1024\) the target capacity is exactly \(1024\), not \((33/35)1024-2\). It suffices to bound each column by \(512\); a tie is already fatal to overload.

### The width-1024 certificate

Use two sets of primes with different jobs:
\[
 A=\{5,7,11,13\},\qquad B=\{17,19,23,29,31,37\},\qquad W=\prod_{p\in A}p=5005.
\]
For \(0\le r<W\), let
\[
 C(r,h)=\#\{0\le i<h:\gcd(r+i,W)=1\},\qquad
 m(h)=\min_{r<W} C(r,h),\quad M(h)=\max_{r<W} C(r,h).
\]

The whole numerical certificate is the single inequality
\[
 \boxed{\quad M(1024)+33\ \le\
 512+m(60)+m(53)+m(44)+m(35)+m(33)+m(27).\quad} \tag{1}
\]
There is no table modulo the product of the ten primes. The largest phase space in (1) has 5005 elements.

Here is Lean code for the finite certificate, including the collision constant. The extrema are expressed as folds so the computation does not need `Finset.min'` witnesses. I have not run Lean here.

```lean
import CpnfLean.Overload

namespace CPNF.Width1024

def countW (r h : ℕ) : ℕ :=
  (List.range h).foldl
    (fun s i => if Nat.gcd (r+i) 5005 = 1 then s+1 else s) 0

def upperW (h : ℕ) : ℕ :=
  (List.range 5005).foldl (fun s r => max s (countW r h)) 0

def lowerW (h : ℕ) : ℕ :=
  (List.range 5005).foldl (fun s r => min s (countW r h)) h

theorem phase_certificate :
    upperW 1024 + 33 ≤
      512 + lowerW 60 + lowerW 53 + lowerW 44 +
            lowerW 35 + lowerW 33 + lowerW 27 := by
  native_decide

def late : List ℕ := [17,19,23,29,31,37]

def collisionCost : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
      (ps.map (fun q => (1024 + p*q - 1) / (p*q))).sum +
        collisionCost ps

theorem collision_certificate : collisionCost late = 33 := by decide

end CPNF.Width1024
```

### Why the certificate applies to the actual marks

Fix **either** column and 1024 consecutive positive rows, all in a block with cutoff \(N\ge37\). Write \(f(n)=6n-1\) or \(6n+1\), according to the column. Let \(D\) be the rows on which \(\gcd(f(n),W)=1\). For each \(p\in B\), let
\[
                         E_p=\{n\in D:p\mid f(n)\}.
\]
Every mark belongs to \(D\setminus\bigcup E_p\): a divisor from \(A\cup B\) would give `minFac ≤ 37 ≤ N`.

The following three bounds prove the reduction.

1. **Initial population:** \(|D|\le M(1024)\). Write the rows as \(a+i\), \(0\le i<1024\). Modulo \(W\), \(f(a+i)=f(a)+6i\). Since \(6\) is a unit modulo \(W\), multiplying by its inverse turns this into \(r+i\) without changing coprimality to \(W\).

2. **Guaranteed removals:** \(|E_p|\ge m(\lfloor1024/p\rfloor)\). This is the important direction: it is a *lower* bound on hits **among the rows still alive after \(A\)**. The condition \(p\mid f(a+i)\) selects one class \(i=b\bmod p\), \(0\le b<p\). Put \(h=\lfloor1024/p\rfloor\). The offsets \(b+pk\), \(0\le k<h\), all fit, since \(b+p(h-1)\le ph-1<1024\). On these rows the column has values
   \[
                         f(a+b)+6pk.
   \]
   Now \(6p\), not just \(6\), is a unit modulo \(W\). Multiplying by its inverse gives \(r_p+k\bmod W\). At least \(m(h)\) of these rows therefore belong to \(D\). In order of increasing \(p\), the six values of \(h\) are exactly \(60,53,44,35,33,27\).

3. **Collision refund:** for distinct \(p,q\in B\),
   \[
                 |E_p\cap E_q|\le \left\lceil\frac{1024}{pq}\right\rceil .
   \]
   Even before imposing \(D\), simultaneous divisibility picks one offset class modulo \(pq\), since \(6\) is invertible modulo \(pq\). The sums of these ceilings for fixed smaller prime \(17,19,23,29,31\) are respectively \(14,9,6,3,1\). This is the \(33\) in (1).

For completeness, the counting inequality needed to combine them is
\[
 |D\setminus\textstyle\bigcup E_p|+\sum_p|E_p|
       \ \le\ |D|+\sum_{p<q}|E_p\cap E_q|.
\]
Indeed, at a row of \(D\) belonging to \(k\) of the sets, the two sides contribute \(\mathbf1_{k=0}+k\) and \(1+\binom{k}{2}\). This also gives a Lean proof by just seven cases, \(0\le k\le6\). Substitution of bounds 1–3 and (1) gives **at most 512 marks**. The argument applies separately to each sign; it assumes nothing about independence between signs.

### Interface to the dyadic tree

The only project-specific base lemma needed is

```lean
∀ t d j : ℕ, d + 10 = t → j < 2^d →
  forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j = 0
```

To formalize it, take \(a=2^t+j\cdot1024+1\) in the interval argument. The valid-index hypothesis gives `node t d j ⊆ blk (2^t)` since \((j+1)1024\le 2^d 2^{10}=2^t\). Thus `colCount (blk (2^t)) t d j = 1024` by `Nat.card_Ioc`, and \(2^t\ge1024>37\) supplies the cutoff hypothesis. For the phase transport in bounds 1 and 2, the reusable lemma to formalize is
\[
 \gcd(c+s k,W)=1\quad\Longleftrightarrow\quad
 \gcd(r+k,W)=1,\qquad sr\equiv c\pmod W,\quad\gcd(s,W)=1.
\]
It follows by replacing \(c+s k\) by \(s(r+k)\) modulo \(W\) and cancelling the coprime factor \(s\). This one lemma handles both signs, including the lower sign without any modular natural-number subtraction, since \(c\) is the actual positive first member of the progression. For bound 3, `card_mod_eq_le` already has the required ceiling.

Here is the generic tree step; it uses only your existing `forced_le_children` and does not rerun any sieve at larger widths.

```lean
namespace CPNF

theorem zero_above_fixed_width
    (S T U : Finset ℕ) (t k : ℕ)
    (base : ∀ d j : ℕ, d + k = t → j < 2^d →
      forced S T U t d j = 0) :
    ∀ e d j : ℕ, d + k + e = t → j < 2^d →
      forced S T U t d j = 0 := by
  intro e
  induction e with
  | zero =>
      intro d j he hj
      exact base d j (by omega) hj
  | succ e ih =>
      intro d j he hj
      have hd : d < t := by omega
      have he' : (d+1) + k + e = t := by omega
      have hj₀ : 2*j < 2^(d+1) := by rw [pow_succ]; omega
      have hj₁ : 2*j+1 < 2^(d+1) := by rw [pow_succ]; omega
      have h := forced_le_children S T U t d j hd
      rw [ih (d+1) (2*j) he' hj₀,
          ih (d+1) (2*j+1) he' hj₁] at h
      have hn : 0 ≤ forced S T U t d j := le_max_left _ _
      omega

end CPNF
```

Set \(k=10\) and \(e=t-d-10\) whenever \(d+10\le t\). The result is a **uniform obstruction for the full-block capacity specified in the target**. It does not claim the same cutoff for `wheelCap`, whose smaller capacity would require a different numerical test. Nor does it construct cofinally many twins: the remaining overload search is at lengths \(1,2,4,\ldots,512\), and its cofinality remains open.
