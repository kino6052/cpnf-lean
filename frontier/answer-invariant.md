**The power-of-two restriction is on the block start, not the node start. At every fixed width, every vector of odd-prime node phases occurs in every sufficiently large power-of-two block.** In particular, the zero coordinates in the width-64 vector do not disqualify it.

There is also a stronger obstruction than the supplied single-column search: **at every dyadic width \(L\le 32\), no fixed finite set of primes can certify zero overload, even if the certificate counts both columns jointly and uses the exact node alignment.** Width 32 has a short arithmetic witness for this.

### 1. The exact node-phase theorem

Write \(L=2^k,\ t=d+k\). From `node` in `ColumnSplit.lean`, the left endpoint is
\[
b_j=2^t+jL=L(2^d+j),\qquad 0\le j<2^d.
\]
The \(i\)-th row, \(1\le i\le L\), tests \(6(b_j+i)\pm1\). Thus the effective phase is \(b_j\bmod p\), not \(2^t\bmod p\).

Let \(M\) be any odd positive modulus. Since \(L\) is invertible modulo \(M\), the map
\[
j\longmapsto 2^t+jL\bmod M
\]
is a permutation on each complete run of \(M\) consecutive node indices. Each phase occurs either \(\lfloor 2^d/M\rfloor\) or \(\lceil 2^d/M\rceil\) times. In particular, if \(2^d\ge M\), **every phase occurs at that very \(t\)**. There is no need to vary \(t\) through a multiplicative orbit.

For the listed width-64 vector, take \(M\) to be the product of the sixteen primes and \(r\) its CRT representative. An explicit valid index, as soon as \(2^{t-6}\ge M\), is the least nonnegative residue
\[
j=(r-2^t)\,64^{-1}\pmod M .
\]
If the implementation stores a shifted single-column phase, the same argument applies after undoing that shift. This realizes the finite phase; it does **not** assert primality of the survivors.

### 2. A joint-column obstruction through width 32

Consider the 64 forms
\[
6(b+i)+s,\qquad 1\le i\le32,\quad s\in\{-1,1\}.
\]
Select the forms whose value at \(b=0\) is a prime greater than 33. **There are exactly 33 selected forms:** their values are precisely the primes in \((33,193]\), and \(\pi(193)-\pi(33)=44-11=33\).

Now let \(P\) be **any** finite set of primes, not necessarily the primes in the certificate. We can make all 33 selected forms survive \(P\) simultaneously:

* For \(p\le33\), prescribe \(b=0\bmod p\). Every selected constant is a prime greater than 33.
* For \(p>33\), each selected form forbids one residue of \(b\bmod p\). The 33 forms forbid at most 33 residues, so choose an unforbidden residue.

The primes 2 and 3 never hit either sign. Combine the prescriptions for the odd primes by CRT and apply the node-phase theorem. **In every sufficiently large dyadic block there is an aligned width-32 node with at least 33 column marks in the \(P\)-sieved model.** Its capacity is 32. This beats the capacity itself, not just a proposed bound on one column.

Partition that node into aligned nodes of any dyadic width \(L\mid32\). If every child at that width had at most \(L\) surviving column entries, their total would be at most 32. Hence the same impossibility holds at widths \(16,8,4,2,1\).

This leaves **only widths 64 and 128** from the stated range as possible targets for a stronger *fixed-prime local exclusion*. At width 64 the supplied vector already obstructs its particular single-column test, but that by itself does not settle the joint test. The width-32 obstruction does settle the joint test, for **every** finite wheel.

More generally there is an exact decision problem for the fixed-prime method at width \(L\). Select \(L+1\) entries from the \(2L\) labeled forms. For every prime \(5\le p\le L+1\), require that the selected entries leave at least one allowed endpoint residue modulo \(p\). **There is a fixed-prime zero-overload certificate iff no such selection exists.** Indeed, if none exists, the primes up to \(L+1\) themselves certify the bound. If one exists, larger primes cannot obstruct it, by the same forbidden-residue count and CRT argument. Thus for 64 and 128 the appropriate finite computation is joint selection with primes up to 65 and 129 respectively, not a search over orders of 2.

### 3. Actual marks: the empirical claim fails at the leaves

At depth \(d=t\), `node t t j` is the singleton \(\{2^t+j+1\}\). With `U = blk`, its `forced` is 1 exactly if that row has both marks. For \(2^t\ge16\) these are exactly the twin rows: the forward direction is `prime_of_loMark` and `prime_of_hiMark`, and the reverse uses `minFac_eq_self_of_prime` and \(6n-1>2^t\).

Here are Lean checks using the supplied definitions. The last check tests the claim about \(t=12\) without scanning the whole block or assuming anything about the earlier certificate code.

```lean
import CpnfLean.Overload

namespace CPNF

-- The 33 constants in the joint width-32 obstruction.
example :
    (((Finset.Icc 34 193 : Finset ℕ).filter Nat.Prime).card) = 33 := by
  native_decide

-- An actual overloaded width-16 node, not a finite-wheel surrogate:
-- the block (16,32] has 19 marks across the two columns.
example :
    forced (loMarks 16) (hiMarks 16) (blk 16) 4 0 0 = 3 := by
  native_decide

-- A positive leaf in the claimed empirical range.
example :
    ∃ j ∈ Finset.range 256,
      0 < forced (loMarks 4096) (hiMarks 4096) (blk 4096) 12 12 j := by
  native_decide

end CPNF
```

Finally, there is a sign issue in the research objective: **proving eventual zero at all the last levels would refute the finish, not establish it.** In fact, eventual zero at width 1 alone is equivalent to finitely many twin primes, because the blocks partition all sufficiently large indices. The result above is a different, unconditional impossibility: a fixed collection of odd-prime phases cannot prove such confinement through width 32. Passing from its 33 simultaneous finite-wheel survivors to actual prime marks would require control of primes growing with the block. The multiplicative order of the block start gives no such control.
