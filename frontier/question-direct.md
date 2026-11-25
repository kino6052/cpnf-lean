# The residual `Direct`: opening, or parity renamed?

You gave us the attack reduction. We have now proved all of tier A in Lean 4 + Mathlib,
with no `sorry` and no extra axioms. All our sources are attached at the end of this
message (about 900 lines total). What is attached is compiled, not proposed.

## What is proved

`head k` is the least positive index admissible for `stage k`, with no window constraint:

```lean
noncomputable def head (k : ℕ) : ℕ := Nat.find (exists_admissible k)
```

Proved, exactly as you specified:

- `head_mono`, `head_escapes`, `next_death`, `dies_iff`
- `transport_to_death {K n} (hn : 1 ≤ n) (hs : n ∈ searchSet K) :
      ∃ k, K ≤ k ∧ Dies k ∧ head k = head K ∧ head k ∈ searchSet k`
- plus the supporting layer: `certify_strict`, `certify_ge_idx`, `admissible_factorial`,
  `blocker_dvd_factorial`, `exists_admissible`, `head_le`, `head_spec`.

Your "useful strengthening" was the one step where we initially proved the wrong thing:
we tried to push `Admissible` *forward* into the larger blocker set. That is false, since
`Survives` is antitone in the blocker set. The goal never needed it — `head k = head K`
makes the admissibility at the death stage `head_admissible k` outright, and the window
bound transports because `window` is monotone. So the reduction holds, but for a slightly
different reason than the one sketched.

## The residual, exactly

```lean
∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ Direct k
```

with `Direct k : certify k = twinLo (head k) ∨ certify k = twinHi (head k)`.

## The question

We are not asking for further decomposition. We are asking you to judge whether this
residual is an *opening* or the parity obstruction wearing a new name.

The two worlds a death can land in are structurally different:

- **Proper-divisor death.** `certify k` properly divides `twinLo (head k)` (or the upper
  member). Then one member of the pair at `head k` is *composite*, and the new certified
  number is a factor of it. The pair is dead as a twin candidate, but nothing about
  primality of the members has been decided — the sieve simply moved on.
- **Direct death.** `certify k` *equals* a member. Then the surviving number and the
  killer are the same object, and (by your factor argument) the pair at `head k` is an
  actual twin pair.

Our residual says: cofinally often, the second kind happens. Every stage produces a
death, unconditionally and with a finite search bound, but we have no lever that forces
the quotient to be `1` rather than a proper factor.

So, three questions, in order of what would help us most:

1. **Verdict.** Is `∀ K, ∃ k ≥ K, Direct k` a genuinely weaker or differently-shaped
   statement than unbounded twin primes, or is it the same obstruction relocated? If it
   is relocated, say *where* the relocation happens: which feature of the proper-divisor
   case is doing the same work that the parity argument does in a sieve-theoretic
   approach.

2. **If it is an opening**, give the single most promising mechanism, as one Lean-checkable
   statement (signature plus the reason it should be true), not a decomposition tree. We
   will take exactly one lemma at a time.

3. **If it is parity renamed**, then say what a *negative* result could look like. We would
   rather prove a sharp no-go — "the CPNF gates plus these hypotheses cannot decide this,
   and here is the precise new input that would" — than keep producing lemmas that circle
   the same obstruction. Specifically: can we prove, in Lean, that the framework's
   available inputs do not imply `Direct` cofinally? And if the honest outcome is a
   conditional theorem, what is the cleanest hypothesis to state it under?

Two constraints on any answer:

- **Only Lean-provable claims.** If you assert something stronger than what follows from
  the attached definitions, mark it clearly as a conjecture. We have now caught four
  false statements by machine-checking (including one of our own: "a window of length `W`
  needs at least `W` blockers" is false — `{5}` kills three of eight indices at `y = 7`).
  We would rather have a modest true lemma than an inspiring false one.
- **Do not assume a window exactness or a primes-to-`OftenSearch` bridge that is not in
  the attached files.** Those are tier B and are not yet proved. If your argument needs
  one, name it as an input explicitly, as you did before.

## What we already know, so you do not spend the answer on it

We know the cofinal window nonemptiness statement is *equivalent* to unbounded twin
primes; you confirmed this twice. We are not looking for a bypass and we will not claim
one. The question is narrower: within this reduction, is `Direct` where the difficulty
concentrates, or is it where the difficulty merely becomes visible?
