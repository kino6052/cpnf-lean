Use `y = maxBlocker k` in the correspondence theorems. The important invariant is not just that the blockers are prime: it is that **there are no missing primes up to `y`**. For the bridge, use a **positive cofinality equivalence** first; the equivalence with negations is a separate logical step.

Here is the build order. In the signatures below, use `Finset` for the finite products and counts, and `open scoped BigOperators`. Names introduced below are proposed names.

### 1. Pin down the seed and the minimum rule — process layer

Prove or expose these statements first:

```lean
stage_zero_empty : stage 0 = ∅

next_mem  (k : ℕ) : certify k ∈ sieve (stage k)
next_le   (k m : ℕ) (hm : m ∈ sieve (stage k)) : certify k ≤ m

mem_sieve_iff (B : Finset ℕ) (m : ℕ) :
  m ∈ sieve B ↔ 2 ≤ m ∧ ∀ b ∈ B, ¬ b ∣ m
```

The last signature is the **interface to check against the actual definition**, not a consequence of `sieve_nonempty`. If `sieve` has a different presentation, expose the equivalent minimum rule directly: `certify k` is least among the `m ≥ 2` not divisible by any stage member. Likewise, for the twin proofs you need `Survives B m` to express avoidance of divisibility for `m ≥ 2`, and you need `¬ Survives B 0` when `2 ∈ B`. Neither nonemptiness alone nor an arbitrary surviving choice gives a canonical prefix.

### 2. Identify the prefix — correspondence layer, first use of `Nat.Prime`

A convenient induction avoids a library convention for “the zeroth prime”. Define

```lean
def primeCut (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime
```

Prove this **local induction step**:

```lean
next_prime_of_cut (k y : ℕ) (h : stage k = primeCut y) :
  Nat.Prime (certify k) ∧ y < certify k ∧
    (∀ q : ℕ, Nat.Prime q → y < q → certify k ≤ q)
```

For the strict inequality, a surviving `m ≥ 2` with `m ≤ y` would have a prime divisor in the cut. For primality, a composite minimum would have a smaller prime divisor; that divisor also avoids the cut (otherwise the minimum would not survive). For leastness, every prime above `y` is an allowed candidate. No Bertrand here.

Then prove, in order:

```lean
prefix_step (k y : ℕ) (h : stage k = primeCut y) :
  stage (k+1) = primeCut (certify k)

max_step_of_cut (k y : ℕ) (h : stage k = primeCut y) :
  maxBlocker (k+1) = certify k

canonical_prefix (k : ℕ) :
  stage k = primeCut (maxBlocker k) ∧ (stage k).card = k
```

`prefix_step` uses `stage_succ` and the no-intervening-prime clause. `max_step_of_cut` uses insertion of the new strict maximum. The induction base needs `stage 0 = ∅`, `sup ∅ = 0` in `ℕ`, and `primeCut 0 = ∅`; the card step uses fresh insertion. This says **first `k` primes for every `k`, including zero**. In particular `certify 0 = 2`, not `stage 0 = {2}`.

Export the following small corollaries for later arithmetic:

```lean
max_strict (k : ℕ) : maxBlocker k < maxBlocker (k+1)
index_le_max (k : ℕ) : k ≤ maxBlocker k
two_mem_stage (k : ℕ) (hk : 1 ≤ k) : 2 ∈ stage k
```

### 3. Prove exactness for a cut, then specialize — correspondence layer

First the window arithmetic:

```lean
hi_le_sq (n y : ℕ) (hy : 1 ≤ y) (hn : n ≤ window y) :
  twinHi n ≤ y^2
```

Then:

```lean
cut_exact (y n : ℕ) (hn : 1 ≤ n) (hw : n ≤ window y) :
  n ∈ twinSieve (primeCut y) y ↔
    y < twinLo n ∧ Nat.Prime (twinLo n) ∧
    y < twinHi n ∧ Nat.Prime (twinHi n)

search_exact (k n : ℕ) (hn : 1 ≤ n) (hw : n ≤ stageWindow k) :
  n ∈ searchSet k ↔
    maxBlocker k < twinLo n ∧ Nat.Prime (twinLo n) ∧
    maxBlocker k < twinHi n ∧ Nat.Prime (twinHi n)
```

For `cut_exact`, `y = 0` is vacuous. Forward: both numbers are at least two and at most `y²`; a composite in that interval has a prime divisor `≤ y`. A prime `≤ y` blocks itself. Reverse: a prime above `y` cannot be divisible by any cut member. **Forward needs coverage of small primes; reverse needs only that the blockers lie in `[2,y]`**, not their primality or coverage. Reverse also needs the stated window hypothesis. `search_exact` is simply rewriting by `canonical_prefix`.

Before using exactness on an arbitrary search witness, prove:

```lean
search_pos (k n : ℕ) (hk : 1 ≤ k) (hn : n ∈ searchSet k) : 1 ≤ n
```

At zero, `twinLo 0 = 0` in `ℕ` and `2 ∣ 0`. Do not silently identify a sieve with its restriction to positive indices at the empty stage.

### 4. Prove the positive bridge — Bertrand only on the entry direction

Use these definitions (or prove equivalence with your existing `UnboundedTwins`):

```lean
def OftenSearch : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ (searchSet k).Nonempty

def UnboundedTwins : Prop :=
  ∀ Y : ℕ, ∃ n : ℕ, 1 ≤ n ∧ Y < twinLo n ∧
    Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)
```

The useful intermediate statements are:

```lean
locate_before (K p : ℕ) (hp : maxBlocker K < p) :
  ∃ k : ℕ, K ≤ k ∧ maxBlocker k < p ∧ p ≤ maxBlocker (k+1)

next_lt_double (k : ℕ) (hy : 3 ≤ maxBlocker k) :
  maxBlocker (k+1) < 2 * maxBlocker k

oftenSearch_iff : OftenSearch ↔ UnboundedTwins
```

* `locate_before`: bounded search for the first maximum `≥ p` after `K`; index `p` suffices by `index_le_max`. Take its predecessor. No prime hypothesis on `p`.
* `next_lt_double`: Bertrand gives a prime strictly between `y` and `2*y`; the next maximum is the least prime above `y` by step 2.
* `OftenSearch → UnboundedTwins`: request a stage `k ≥ max 1 Y`; apply `search_pos`, the window projection, `search_exact`, and `index_le_max`. No Bertrand.
* `UnboundedTwins → OftenSearch`: start at `J = max K 3`; request twins with low member `p > maxBlocker J`. Apply `locate_before J p`. At its stage `k`, both primes exceed all blockers, hence are admissible, **before** you know window membership. Now `p ≤ maxBlocker (k+1) < 2 * maxBlocker k`. Apply your `twinSieve_of_lt_two_mul`. This order avoids circular use of `search_exact`.

If desired, add the following **classical corollary**, not a prerequisite:

```lean
eventual_empty_iff :
  (∃ K : ℕ, ∀ k : ℕ, K ≤ k → searchSet k = ∅) ↔ ¬ UnboundedTwins
```

Eventual emptiness implies `¬ UnboundedTwins` constructively. Extracting an eventual cutoff from the negation of positive cofinality is not in general constructive; decidability of each finite search does not justify that quantifier exchange.

### 5. Exact count — independent finite branch, no `Nat.Prime` required

This can start **before step 2**. Count indices in `[1,W]`, not `[0,W]`. Use moduli `≥ 5`, pairwise coprime, each coprime to `6`. On a canonical stage, **remove `2` and `3` first**: they never hit positive twins, but the asserted local two-choice count is false for them.

Suggested definitions:

```lean
def GoodMods (A : Finset ℕ) : Prop :=
  (∀ b ∈ A, 5 ≤ b ∧ Nat.Coprime 6 b) ∧
  (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)

def hit (b n : ℕ) : Prop :=
  (6*n) % b = 1 ∨ (6*n) % b = b-1

def d (S : Finset ℕ) : ℕ := ∏ b ∈ S, b

def T (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (d S)).filter (fun r => ∀ b ∈ S, hit b r)

def C (W : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ r ∈ T S, (W + d S - r) / d S

def G (A : Finset ℕ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter (fun n => ∀ b ∈ A, ¬ hit b n)
```

Give `hit` a decidable instance by unfolding it for the filters. Prove in this order:

**5a. Local congruence and CRT.**

```lean
unique_mul_residue (b t : ℕ) (hb : 5 ≤ b) (hc : Nat.Coprime 6 b)
    (ht : t < b) :
  ∃! r : ℕ, r < b ∧ (6*r) % b = t

T_card (S : Finset ℕ) (hS : GoodMods S) :
  (T S).card = 2 ^ S.card
```

Use the first lemma at `1` and `b-1` (distinct). CRT identifies tuples of local choices with residues modulo `d S`; use the positive representative `d S` for residue zero. The empty product matters: `T ∅ = {1}`.

**5b. One progression, then one intersection.**

```lean
progression_card (W D r : ℕ) (hr : 1 ≤ r) (hrD : r ≤ D) :
  ((Finset.Icc 1 W).filter (fun n => n % D = r % D)).card =
    (W + D - r) / D

intersection_card (W : ℕ) (S : Finset ℕ) (hS : GoodMods S) :
  ((Finset.Icc 1 W).filter (fun n => ∀ b ∈ S, hit b n)).card = C W S
```

The first counts `r, r+D, …`, including the `W < r` case. The second partitions by the unique representative in `[1,d S]`; every `b ∈ S` divides `d S`, so hits are constant on each class. It does **not** depend on `T_card`.

**5c. Natural-number inclusion–exclusion.**

```lean
exact_count (A : Finset ℕ) (W : ℕ) (hA : GoodMods A) :
  (G A W).card +
    (∑ S ∈ A.powerset.filter (fun S => S.card % 2 = 1), C W S) =
    ∑ S ∈ A.powerset.filter (fun S => S.card % 2 = 0), C W S
```

Use `intersection_card` on each subset. Swap the finite counts and fix `n`: the contributing subsets are the powerset of its hit blockers. If none hit, the empty even subset balances the one survivor. Otherwise toggling one hit blocker pairs even and odd subsets. This proves the identity in `ℕ` without truncated alternating subtraction; `C W ∅ = W` is already on the even side.

**5d. Attach the count to the run last.** With `active k := (stage k).filter (fun b => 5 ≤ b)`, prove:

```lean
active_good (k : ℕ) : GoodMods (active k)

search_eq_good (k : ℕ) (hk : 1 ≤ k) :
  searchSet k = ↑(G (active k) (stageWindow k))
```

Here the coercion on the right is to `Set ℕ` if `searchSet` is set-valued. `active_good` is correspondence-layer work. For `search_eq_good`, use `search_pos`, discard `2,3`, and for positive `n` translate divisibility of `6*n-1` or `6*n+1` into `hit`. Thus the exact count applies to the **actual search witnesses** without putting a prime test in any gate or claiming that the count is positive.