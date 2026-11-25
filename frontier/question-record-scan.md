# Draft: the record scan, please attack it

A rough draft, not a claim. I want you to break it: name the false step, the gap, or the
place where I am only restating the twin conjecture. All Lean sources are attached; the
material below `score` compiles.

## What compiles already

`score n = min(minFac(6n-1), minFac(6n+1))`, and:

- `admissible_iff_score` — a pair is admissible at stage `k` iff `certify k ≤ score n`.
- `head_le_iff` — `head k ≤ N` iff some `n` with `1 ≤ n ≤ N` has `certify k ≤ score n`.
- `certify_prime`, `stage_eq_primes_lt` — stage `k` is exactly the primes below `certify k`.
- `prime_of_minFac_gt` — `m ≤ B²` and no prime factor ≤ `B` forces `m` prime.
- `twin_of_score_row` — `twinLo n ≤ score n` forces both members prime.

## Draft, part 1: records

Call `n` a **record** if `1 ≤ n` and `score m < score n` for every `1 ≤ m < n`.

Claim A (I think this is easy): if `n` is a record, `score n = b`, every earlier score is
`≤ a`, and `a < certify k ≤ b`, then `head k = n`.

I proved a version of this shape in a probe: it follows from `head_le_iff` plus the fact
that no smaller index reaches `certify k`. So one record covers every killer in `(a, b]`.
Consequence: the record list is a compressed description of all heads, including the
indirect deaths.

## Draft, part 2: the square test at endpoints

At the endpoint of a record's plateau, the killer is `b` and the head is `n`. The death is
**direct** exactly when `b` divides one of the members, i.e. `b = twinLo n` or `b = twinHi n`.

Since `b ≤ score n = min(minFac(6n-1), minFac(6n+1))`, both members have no prime factor
below `b` (weakly). So each member is either prime or equals `b` itself.

Draft test: **`6n + 1 < b²` implies the endpoint death is direct.**

Reasoning (this is the step I want attacked): if the death is not direct, then the struck
member is `c · q` with `q > 1` also surviving, and the gates force `q ≥ c`, hence the
member is `≥ b²`. The strict inequality `6n+1 < b²` rules that out, so both members are
prime. This is your earlier conditional equivalence, and I believe it is the same statement
in disguise — but I have not verified that the *direction* I need is the one that holds.

## Draft, part 3: what a scan buys

Run the scan over `1 ≤ n ≤ N`, recording strict prefixes. Two outcomes:

- Some record passes `6n + 1 < (score n)²` ⟹ `twin_of_score_row` gives a twin pair at `n`.
  Actually, the passing condition uses `score n`, so this needs `twinLo n ≤ score n`, which
  is stronger than the square test — one of these must be wrong, or one implies the other.
- No record passes ⟹ no twin pair with `1 ≤ n ≤ N`? **This is the step I doubt most.**
  A twin pair at `n` forces `score n ≥ twinLo n`, so a *record* inside the range should
  certify it — but only if that `n` is a record, which it need not be.

## The four things to attack

1. **Is the square test correctly oriented?** I have `6n+1 < b²` as the passing condition,
   but the payoff lemma `twin_of_score_row` needs `twinLo n ≤ score n`. Do these imply each
   other, or have I mixed up which one is the hypothesis I get and which is the conclusion
   I want?
2. **Does a non-record twin pair get lost?** If `n` has a twin pair but `score n` is not a
   strict record, does the scan still certify it? My draft says a record elsewhere covers a
   *plateau of killers*, not every `n`, so I suspect the "no twin pair" direction is broken.
3. **Is Claim A's quantifier right?** I want one record to cover a whole interval of
   killers; check I have not accidentally required the killer to be a score value.
4. **Is this genuinely a compression, or am I just re-indexing?** If the record list carries
   the same information as the full head sequence, say so plainly.

Tell me which of the three parts survives, and what the corrected statement of part 3 is.
