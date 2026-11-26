**Method: additive combinatorics of affine-linear forms.** I test what can be deduced from counts for every system with pairwise nonproportional linear parts. The obstruction is a random-set construction with dependence at distance exactly \(2\), not a sieve, a circle integral, or a divisor-tail estimate.

**Obstruction theorem.** There is a single set \(A\subset\mathbb N\) with **no** pair \(m,m+2\), for which the prime-tuple asymptotic with the usual local factors holds for **every** fixed system of affine-linear forms with pairwise nonproportional nonzero linear parts, on the boxes specified below. In particular, \(A\) has the prime number theorem in every fixed reduced residue class.

Thus even granting the full main terms, not just existence of configurations or uniformity bounds of some fixed order, this class of inputs does not force one twin. The restriction to nonproportional linear parts is essential. Here is the construction and the estimate that proves it.

### The statistics to be preserved

Write \(\psi_i(x)=a_i\cdot x+b_i\), \(1\le i\le k\), on \(\mathbb Z^d\). Fix the forms, with \(a_i\ne0\) and no two \(a_i\) proportional over \(\mathbb Q\). Take integer boxes \(B_N=[N,2N)^d\cap\mathbb Z^d\) and assume that on these boxes
\[
cN\le \psi_i(x)\le CN
\]
for some fixed \(0<c<C\) and all sufficiently large \(N\). Define
\[
\beta_p=(1-1/p)^{-k}\,p^{-d}
 \#\{x\in\mathbb F_p^d:\ \psi_i(x)\ne0\bmod p\ \text{for every }i\}.
\]
The theorem asserts that, simultaneously for all such systems, as \(N\) tends to infinity through **all integers**,
\[
\frac{(\log N)^k}{N^d}
\sum_{x\in B_N}\prod_{i=1}^k 1_A(\psi_i(x))
\ \longrightarrow\ \prod_p\beta_p. \tag{1}
\]

### The construction: a gate invisible off three diagonals

The key step works for *any* prescribed one-point probabilities \(0\le u_m\le 1/4\). Take independent fair bits \(G_m\) and, independently of them and one another, bits \(H_m\) of means \(4u_m\). For \(m\ge3\) set
\[
Z_m=H_mG_m(1-G_{m-2}),\qquad A=\{m\ge3:Z_m=1\}.
\]
Then
\[
\mathbb E Z_m=u_m,\qquad Z_m Z_{m+2}=0
\]
exactly. More importantly, the variables at any list of sites are **jointly independent** if all pairwise differences avoid \(\{0,2,-2\}\): they read disjoint underlying bits.

For a fixed system in (1), the inputs where this independence can fail lie on
\[
(a_i-a_j)\cdot x=b_j-b_i+h,\qquad h\in\{0,2,-2\}.
\]
Each equation has at most \(N^{d-1}\) solutions in the box: fix all but a coordinate with nonzero coefficient. Consequently, for arbitrary marginals \(u\),
\[
\left|
\mathbb E\sum_{x\in B_N}\prod_i Z_{\psi_i(x)}
-\sum_{x\in B_N}\prod_i u_{\psi_i(x)}
\right|
\le 3\binom{k}{2}N^{d-1}. \tag{2}
\]
At the target pair of forms \(x,x+2\), one of those exceptional equations is instead the identity on the **whole box**. That dimension jump is the mechanism of the obstruction.

### Calibrating the marginals

It remains to make the right side of (2) have the actual prime main terms, so that the countermodel cannot be dismissed on grounds of wrong local densities. On \(2^j\le m<2^{j+1}\) put
\[
z_j=\lfloor\log(j+2)\rfloor,\qquad
W_j=\prod_{p\le z_j}p,\qquad
u_m=\frac{W_j}{\varphi(W_j)}
       \frac{1_{(m,W_j)=1}}{\log m}.
\]
Set \(u_m=0\) in finitely many initial blocks to ensure \(u_m\le1/4\). This is legitimate even using only the elementary bound
\[
W_j/\varphi(W_j)\le\prod_{2\le n\le z_j}(1-1/n)^{-1}=z_j
\]
for \(z_j\ge2\). The periodic function here specifies the desired **first marginal** of a synthetic set; no lower or upper bound for sifted primes is used.

To evaluate the deterministic sum, partition \(B_N\) according to the dyadic block of each \(\psi_i(x)\). There are \(O_{c,C,k}(1)\) pieces, each cut out by a bounded number of affine inequalities. On each piece the moduli \(W_{j_i}\) are fixed and nested. Their largest, \(W\), satisfies
\[
W\le z!\ =N^{o(1)},\qquad z=\max_i z_{j_i}=O(\log\log N).
\]
Replace every \(\log\psi_i(x)\) by \(\log N\) with relative error \(O_{c,C,k}(1/\log N)\) in the product. The remaining weight is periodic modulo \(W\) in every coordinate and bounded by \(O(z^k)\).

Tile by cubes of side \(W\). Full cubes give exactly the periodic mean; the contribution to the **normalized** average from replacing the weights by their mean on boundary cubes is
\[
O_{\psi,c,C}\!\left(z^k W/N\right)=o(1).
\]
Indeed, those cubes lie within \(O_{\psi,d}(W)\) of finitely many bounding hyperplanes; fixing all but one coordinate bounds the number of lattice sites in each such slab by \(O_{\psi,d}(WN^{d-1})\).

By the Chinese remainder theorem, the periodic mean on a piece is the product of local factors calculated with just the forms active at that prime, namely \(i\) with \(p\le z_{j_i}\). These products converge to \(\prod_p\beta_p\) uniformly over the pieces. To see why, outside a fixed finite set of primes each form cuts out a hyperplane of density \(1/p\), and each pair cuts out an intersection of density \(1/p^2\). This follows by retaining one nonzero coefficient per form and one nonzero two-by-two minor per pair modulo \(p\). For **any subset** of \(s\) active forms, the union therefore has density \(s/p+O_k(p^{-2})\), by the first two union bounds. After normalization by \((1-1/p)^{-s}\), the factor is \(1+O_k(p^{-2})\). Every fixed prime eventually sees all the forms, since \(\min_i z_{j_i}\to\infty\). This also handles a zero local factor: it is eventually present on every piece.

Summing by piece volumes proves (1) in expectation, using (2).

### One realization works at every scale

Let \(S_N=\sum_{x\in B_N}\prod_i Z_{\psi_i(x)}\). It reads \(O_{c,C}(N)\) independent bits. Changing one bit changes at most two site indicators, and each site occurs in at most \(kN^{d-1}\) summands, by solving one nonconstant linear equation. McDiarmid’s bounded-differences inequality gives, for a constant \(c_\psi>0\),
\[
\Pr\!\left(\left|S_N-\mathbb E S_N\right|>N^{d-1/4}\right)
\le 2\exp(-c_\psi N^{1/2}).
\]
This is summable in \(N\), and \(N^{d-1/4}=o(N^d/(\log N)^k)\) for every fixed \(k\). Borel–Cantelli and a countable intersection over the integer systems give one realization satisfying (1) for all of them. Taking the one-form systems \(qx+r\) with \((q,r)=1\) gives the stated progression asymptotics by dyadic summation. The no-twins property holds for **every** realization, without a probability estimate.

Here is the deterministic gate in Lean. The second lemma records the disjointness of the gate-bit addresses used in (2).

```lean
import Mathlib

namespace CPNF.AffineBarrier

def kept (g h : ℕ → Bool) (m : ℕ) : Prop :=
  3 ≤ m ∧ h m = true ∧ g m = true ∧ g (m - 2) = false

theorem no_pair (g h : ℕ → Bool) (m : ℕ) :
    ¬ (kept g h m ∧ kept g h (m + 2)) := by
  rintro ⟨⟨_, _, hm, _⟩, ⟨_, _, _, hn⟩⟩
  have he : m + 2 - 2 = m := by omega
  rw [he, hm] at hn
  cases hn

theorem disjoint_reads {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (h0 : m ≠ n) (hp : m + 2 ≠ n) (hq : n + 2 ≠ m) :
    Disjoint ({m, m - 2} : Finset ℕ) ({n, n - 2} : Finset ℕ) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega

end CPNF.AffineBarrier
```

The conclusion concerns precisely what the method can infer: **no argument whose only prime-specific premises are the statistics (1) can prove cofinal twins**. Increasing the dimension, the number of forms, or the fixed complexity does not cure the loss. The countermodel satisfies all those premises simultaneously and has identically zero mass at shift \(2\).
