**1. Verdict: the residual is equivalent to unbounded twin primes.** In fact there is a pointwise correspondence: the lower members of the positive-index twin prime pairs are exactly the values of `certify` at direct stages. This does not need a window theorem in either direction.

The key fact is that if \(m\) survives a stage, every divisor \(d\ge2\) of \(m\) survives it too. A blocker dividing \(d\) would divide \(m\). Thus `next_le` gives \(\mathrm{certify}(k)\le d\) for **every** such divisor, not just for \(m\).

* **From a direct stage to a twin.** Put \(c=\mathrm{certify}(k)\), \(L=\mathrm{twinLo}(\mathrm{head}(k))\), and \(H=L+2\). Since \(L\) survives and \(L\ge5\), we have \(c\le L<H\). The upper disjunct of `Direct` is therefore impossible: direct means \(c=L\). Neither member can be composite. A composite member would factor into two integers at least \(2\), both surviving and hence both at least \(c\). But \(L,H\le c+2<c^2\).
* **From a twin to its direct stage.** Take a positive index \(n\) with \(p=6n-1\) and \(p+2\) prime. Let \(k\) be the first stage with `certify k ≥ p`; it exists by `certify_ge_idx`. Every blocker in `stage k` is an earlier certified value (induction using `stage_zero_empty` and `stage_succ`), so is at least \(2\) and strictly less than \(p\). Neither prime is blocked. Thus `head k ≤ n` by `head_le`, and
  \[
  p\ \le\ \mathrm{certify}(k)\ \le\ \mathrm{twinLo}(\mathrm{head}(k))\ \le\ p .
  \]
  The middle inequality is `next_le` on the surviving lower member. Equality gives `Direct k` and `head k = n`.

These are proof arguments from the definitions, not claims that the correspondence is already in the files. Strict increase of `certify` makes the matching stage unique and converts unbounded matched values to cofinal matched stages; `certify_ge_idx` gives the converse. Passing from positive-index twins to ordinary unbounded twins only uses residues modulo \(6\): every twin pair above \((3,5)\) has this form.

**2. There is no weaker infinitude target here.** The relocation occurs precisely at the cofactor. At a non-direct death the struck member is \(c q\), where \(q>1\) **also survives**, so \(q\ge c\). The death does decide compositeness of that member. What the gates do not supply is a reason why arbitrarily late deaths cannot all have such a cofactor. `next_death` forces a divisor event, not a bound excluding the second factor.

That is the connection to sieve parity: excluding small factors is compatible with a product of two remaining factors. It is **not** a literal identification of `Direct` with a factor-parity test (the cofactor can itself be composite), nor is it a parity impossibility theorem for CPNF. The exact arithmetic retains the member values and so can distinguish the cases at a given death. The missing assertion is about their occurrence, not their decidability.

**3. A sharp restricted no-go is available: prime-hit data do not determine directness.** I would formalize this by *squaring the members while keeping the ordinary stage process fixed*. This gives a counterexample with the **same head sequence**, not just an abstract monotone sequence with arbitrarily assigned death labels.

Specifically, compare the two readouts \((L(n),H(n))\) and \((L(n)^2,H(n)^2)\). Every `certify k` is prime: a proper divisor at least \(2\) would survive and contradict minimality. Hence every stage blocker is prime. For each such blocker \(b\), \(b\mid x^2\) iff \(b\mid x\). Consequently the two readouts have identical admissibility at every index and stage, identical least positive heads, identical deaths and, if filtered by the same **index** window, identical search sets. Yet the squared readout has **no** direct stage: at the common head,
\[
\mathrm{certify}(k)\le L<L^2<H^2 .
\]
Thus no implication **uniform over member readouts** can deduce cofinal equality to a member solely from those shared gates and their proved growth, death and transport properties. This counterexample does **not** preserve the gap of two or a bound on the *squared member values* from the original window. It proves nothing about independence for the fixed forms \(6n\pm1\). For those forms the gates are proved facts; an internal theorem negating their implication to cofinal `Direct` would negate cofinal `Direct` itself.

For a conditional theorem on the **actual** forms, the clean size input is exact, with strict inequality:

```lean
(∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ Dies k ∧ twinHi (head k) < (certify k)^2) ↔
(∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ Direct k)
```

The proof is pointwise. At a death below that square, a proper cofactor would force the struck member to be at least \(c^2\); at a direct stage, `dies_iff` gives death and the upper member is \(c+2<c^2\). No `OftenSearch` bridge is involved. The new input would have to **establish** that strict size bound at cofinally many deaths, not merely produce more deaths. The equivalence measures exactly what such an estimate would buy; it is not evidence that the estimate is easier than twin primes.
