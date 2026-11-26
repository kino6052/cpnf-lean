At width \(512\), sieve the **sum of the two columns**, not each column separately. For each late prime there are only \(p\) choices of phase for the *whole node*, not \(p^2\) choices for its two columns. Take the minimum removal **after** fixing the early phases. There is a short finite certificate for this approach, with a branch step if the first Bonferroni bound is inconclusive.

Here is my reduction for option 4. The numerical check is given as standalone executable Python below; I have not run it or compiled a new Lean file here. I distinguish what follows from the check from what follows even without a successful check.

### The width-512 certificate

Write the rows as \(a+i+1,\ 0\le i<512\). Use a 1024-bit set, with bit \(2i\) for the low member and \(2i+1\) for the high member. For \(p\ge5\) prime and \(0\le r<p\), let \(D_{p,r}\) contain the bits for which
\[
  6(r+i+1)-1\equiv0\pmod p,\qquad
  6(r+i+1)+1\equiv0\pmod p,
\]
respectively. **Both tests use the same \(r\).** The initial set \(M\) is all bits. Assignment of phase \(r\) replaces \(M\) by \(M\setminus D_{p,r}\).

The useful bound at a partially assigned node is this. For any list \(Q\) of distinct unassigned primes define
\[
 u_p(M)=\min_{0\le r<p}|M\cap D_{p,r}|.
\]
For *every* completion of the phases the final population is at most
\[
 |M|-\sum_{p\in Q}u_p(M)
       +2\sum_{\{p,q\}\subset Q}\left\lceil\frac{512}{pq}\right\rceil. \tag{1}
\]
Indeed, in each column the intersection of two removal masks is supported in a **single** residue of \(i\bmod pq\), by coprimality of \(6\) to \(pq\) and CRT. There are two columns. The first two terms of inclusion–exclusion for the removal union now give (1). This uses no hypothesis about how many primes occur on an interval.

In particular, a node can close using the best **prefix** of \(Q\): taking additional primes is optional, not compulsory. If it does not close, branch on one more prime and *recompute* the \(u_p\)'s. This is stronger than subtracting unconditional progression minima, because a child that avoided unusually many removals is tested with its **actual** remaining bits.

Here is the entire certificate generator/check. It does not scan translates of a primorial or need as input a conjectured table of minima. On success its proof is exhaustive; on failure it returns an actual compatible phase vector, not “search budget exceeded.”

```python
from itertools import combinations

def width_certificate(L=512):
    P = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)
    D = {}
    for p in P:
        # At phase r, the killed offsets for side sign solve
        # i = -sign / 6 - 1 - r  (mod p).
        inv = pow(6, -1, p)
        masks = []
        for r in range(p):
            b = 0
            for side, sign in enumerate((-1, 1)):
                first = (-sign * inv - 1 - r) % p
                for i in range(first, L, p):
                    b |= 1 << (2*i + side)
            masks.append(b)
        D[p] = masks

    def cost(p, q):
        return 2*((L+p*q-1)//(p*q))

    # Each entry is the extra collision allowance on extending a prefix.
    inc = [[sum(cost(p, q) for q in P[k:h])
            for h, p in enumerate(P) if h >= k]
           for k in range(len(P))]

    def visit(k, M, phase):
        n = M.bit_count()
        if n <= L:
            return
        if k == len(P):
            raise ArithmeticError(("surviving phase", phase, n))

        # No lookahead needed in the first 5005-way wheel.
        if k >= 4:
            upper = n
            for j, p in enumerate(P[k:]):
                upper += inc[k][j] - min((M & b).bit_count() for b in D[p])
                if upper <= L:
                    return

        p = P[k]
        for r, b in enumerate(D[p]):
            visit(k+1, M & ~b, phase+(r,))

    visit(0, (1 << (2*L))-1, ())
    return True

if __name__ == "__main__":
    print(width_certificate())
```

### How to attach the certificate to `forced`

The soundness invariant for `visit` is an upper bound on a **single cardinal**, so it does not need any new primality bridge. At actual start \(a\), send every low mark in the node to \(2(n-a-1)\), and every high mark to \(2(n-a-1)+1\). The images are disjoint by parity and the maps are separately injective. At recursion depth \(k\), both images are in \(M\) along the path \(r_p=a\bmod p\). Indeed, deletion of a marked bit gives a divisor \(p\le61\le 2^t\) of that member, contradicting `Nat.minFac_le_of_dvd`. The cutoff holds automatically at width 512 because \(t\ge9\).

For \(d+9=t,\ j<2^d\), the node lies entirely inside `blk (2^t)`: its upper endpoint is at most \(2^t+2^d\cdot512=2^{t+1}\). Its capacity is therefore exactly \(512\). Thus a verified `True` gives the **unconditional** width-512 base theorem, not a density conjecture:
```lean
∀ d j : ℕ, d + 9 = t → j < 2^d →
  forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j = 0
```
Apply `zero_above_fixed_width` with `k := 9`. The resulting remaining widths are \(1,2,4,8,16,32,64,128,256\). This attachment is worth making explicit: the supplied `Width1024.lean` proves numerical lemmas and a lift **taking `base` as input**; its displayed Lean source does not itself discharge `base`.

For Lean reflection there is a simplification: **do not formalize Bonferroni** if exporting a certificate tree. At each closing node of type (1), export just the prefix length. In Lean prove the elementary multiplicity inequality below and sum it over bits. This handles all orders of overlap, not only pair collisions.

```lean
import Mathlib

namespace CPNF

/-- Twice the pointwise Bonferroni bound for removal multiplicity `m`. -/
theorem twice_hits_le_covered_add_pairs (m : ℕ) :
    2 * m ≤ (if m = 0 then 0 else 2) + m * (m - 1) := by
  cases m with
  | zero => decide
  | succ m =>
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
    cases m with
    | zero => decide
    | succ m => simp only [Nat.succ_eq_add_one]; nlinarith

end CPNF
```

Alternatively even the CRT collision lemma can be removed from the trusted bridge: for every prime pair used in a closing prefix, verify once by `native_decide` that `popcount (D[p,r] &&& D[q,s]) ≤ cost(p,q)` for all \(r,s\). This table depends only on the width, not on \(M\).

### A strict class reduction even before running the tree

There is a concrete width-512 family that can already be discarded without the all-branches result. Take start \(a\equiv0\) modulo every prime \(5\le p\le61\). The 1024 candidate bits then have the same removal pattern as the integers \(6(i+1)\pm1\) at the origin. They lie in \([5,3073]\), and \(56^2>3073\); hence **every surviving bit represents a prime greater than 61** in that model interval. There are fewer than 512 such bits. The following is a separate small Lean certificate for the bound, with no recursion or large modulus:

```lean
import Mathlib

namespace CPNF

def origin512 (s : ℕ) : ℕ :=
  ((List.range 512).filter (fun i =>
    let m := 6*i + 5 + 2*s
    decide (61 < m.minFac))).length

theorem origin512_bound : origin512 0 + origin512 1 ≤ 512 := by
  native_decide

end CPNF
```

Transport only the *divisors*, not primality, from the model interval to the actual interval: for a discarded bit its model `minFac` is a prime in \([5,61]\) and divides the translated member because it divides \(a\). Thus this is an excluded residue class of valid dyadic starts, not merely a calculation about small exceptional primes. The same argument discards every partial phase assignment at which (1) closes. The all-branches numerical step above is what distinguishes exclusion of those classes from elimination of the entire width; neither conclusion implies cofinal twins.
