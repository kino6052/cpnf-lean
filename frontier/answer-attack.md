**For the stated wheel, every overloaded node on a sufficiently large block has fewer than \(65{,}536\) rows.** In particular, no argument that produces overload on nodes of growing length can work, even if the twin-prime conjecture is true. This is an unconditional restriction on the proposed certificate, not an equivalence obtained by going to singleton leaves.

I do not have an unconditional proof of cofinal overload. My route is to use a one-column upper sieve to rule out scales, then use a genuinely two-column theorem for the conditional positive result.

### The scale obstruction

Let \(N=2^t\ge32\), let \(I=\texttt{node}\ t\ d\ j\) be a valid node, and put \(L=2^{t-d}\). Write \(a,b,c\) for its low-mark count, high-mark count, and wheel capacity. Use the nine primes
\[
P=\{5,7,11,13,17,19,23,29,31\},\qquad
\rho=\prod_{p\in P}(1-1/p)<460/1000.
\]

Here is the key estimate, **uniform in the starting point of the node**:
\[
a\le \rho L+512,\qquad b\le \rho L+512.
\]
To prove it, take either sign. A marked member has no divisor in \(P\), since every \(p\in P\) is at most \(N\). Count the rows avoiding \(P\) by inclusion–exclusion. For each \(D\subseteq P\), set \(m_D=\prod_{p\in D}p\). The simultaneous divisibilities on that **one sign** specify exactly one residue class modulo \(m_D\), since \(6\) is invertible modulo \(m_D\) (with the empty subset counting all rows). Its count on \(I\) differs from \(L/m_D\) by less than one. The main terms sum to \(\rho L\), and there are only \(2^9=512\) errors. In particular, there is **no** error proportional to the period \(\prod P\).

On the other side, the wheel deletes only the classes \(1,34\bmod 35\). Each occurs at most \(L/35+1\) times, so
\[
c\ge (33/35)L-2.
\]
For \(L\ge65536\) these inequalities give \(a+b<c\), hence `forced = 0`. Equivalently, on blocks \(N\ge32\), **positive overload requires \(t-d\le15\)**. The constant is not intended to be optimal.

### First Lean patch

These are the numerical certificate and the node-level closing lemma I would compile first. They separate the finite rational calculation from the progression-counting proof above. I have not run this patch.

```lean
import CpnfLean.Wheel

namespace CPNF

theorem nine_prime_density :
    (1 - 1/5 : ℚ) * (1 - 1/7) * (1 - 1/11) *
    (1 - 1/13) * (1 - 1/17) * (1 - 1/19) *
    (1 - 1/23) * (1 - 1/29) * (1 - 1/31) < 460/1000 := by
  norm_num

theorem forced_zero_of_nine_prime_bounds
    {S T U : Finset ℕ} {t d j : ℕ} {L : ℤ}
    (hL : 65536 ≤ L)
    (hS : 1000 * colCount S t d j ≤ 460 * L + 512000)
    (hT : 1000 * colCount T t d j ≤ 460 * L + 512000)
    (hU : 33 * L ≤ 35 * colCount U t d j + 70) :
    forced S T U t d j = 0 := by
  unfold forced
  apply max_eq_left
  omega

end CPNF
```

One source detail matters for the next patch: the pasted `Overload.lean` defines `CofinalNodeOverload` with `blk`, not `wheelCap`. Also, the pasted `Wheel.lean` contains the residue-to-kill implications; the capacity **lower** bound needs the kill-to-residue implication. If it is not in the pushed version, the missing direction for positive rows has the short proof `unfold wheelKilled twinLo twinHi at hk; rcases hk with h | h <;> omega`, with goal `n % 35 = 1 ∨ n % 35 = 34` and hypothesis `1 ≤ n`. The direction matters: proving that two classes *are* killed does not bound how many classes are killed.

### A conditional route that actually reaches the target

An analytic hypothesis independent in formulation of twin counts is the following: there is a sequence of primitive real Dirichlet characters of conductors \(q_i\to\infty\) whose \(L\)-functions have real zeros \(\beta_i<1\) satisfying
\[
(1-\beta_i)\log q_i\longrightarrow 0.
\]
Under this exceptional-zero hypothesis, Heath-Brown’s *Prime twins and Siegel zeros* gives unbounded twin primes. This is an external mathematical theorem, not a result in the attached Lean sources.

To get **the exact requested node**, take a twin index \(n>2^{\max(T_0,5)}\) supplied by that theorem. Choose the unique \(t\) with \(2^t<n\le2^{t+1}\), set \(d=t\), and take \(j=n-2^t-1\). Then \(j<2^t\) and `node t t j = {n}`. Both least factors equal their respective prime members and exceed \(2^t\); the wheel retains the row. The three counts are \(1,1,1\), so `forced = 1` for the wheel capacity, and also for the pasted `blk` capacity.

The new unconditional step **for this framework** is the scale obstruction: nine small primes already drive the sum of the two marginal densities below the wheel capacity, with a uniform and affordable endpoint error. The positive step in the conditional route is entirely different: Heath-Brown obtains information about primes **at the fixed separation two**. The exceptional-zero hypothesis is not known to hold. Without it or a replacement for that correlation input, the last sixteen levels are precisely where this argument leaves the problem open.
