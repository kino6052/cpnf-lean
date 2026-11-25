**Attack the stages where the least positive admissible index dies.** Those stages are cofinal unconditionally. At each of them, the new blocker either equals a member of the pair or is a proper divisor. The exact residual is that the equality case occurs cofinally. This test needs neither a window count nor a primality test.

**False stronger claim:** equality need not hold at a death. At `maxBlocker = 3`, the least positive admissible index is `1`, and the next blocker `5` kills it by equality. But at `maxBlocker = 23`, the least positive admissible index is `5` (pair `29,31`), so that example is *also* equality. A genuine proper-divisor example should not be inferred just from a gap in the twin primes. The simple claim that *is* immediately false is “every stage has nonempty search”: at `maxBlocker = 2` the window is zero and `2 ∣ twinLo 0`. I do not claim `OftenSearch` is false.

Here is the proposed Lean decomposition (signatures and proof arguments, not compiler-tested). Work in `namespace CPNF`. Define `head k` by `Nat.find` on
```lean
∃ n : ℕ, 1 ≤ n ∧ Admissible (stage k) n
```
**without** a window constraint. The existence witness is `n := (maxBlocker k).factorial`: every blocker divides `6*n`, hence cannot divide either neighbor. For the lower neighbor use `1 ≤ n` before doing subtraction.

```lean
def Dies (k : ℕ) : Prop := head k < head (k+1)

def Direct (k : ℕ) : Prop :=
  certify k = twinLo (head k) ∨ certify k = twinHi (head k)
```

### Unconditional lemmas

1. `head_mono : Monotone head`. Use `Nat.find_min'` and `admissible_of_stage_le`.
2. `certify_strict : StrictMono certify`. For adjacent stages, the next survivor survives the old stage, so is at least the old minimum. Equality is impossible since the old minimum now divides itself. In particular `m < certify (m+1)`.
3. `head_escapes (K : ℕ) : head K < head (max K (twinLo (head K) + 1))`. Write `m := twinLo (head K)` and `j := max K (m+1)`. If the heads were equal, then `m ≥ 5` would survive stage `j`, giving `certify j ≤ m` by `next_le`, contrary to step 2. Monotonicity excludes the other direction.
4. `next_death (K : ℕ) : ∃ k, K ≤ k ∧ Dies k ∧ head k = head K`. Bounded scan: take the first stage after `K` with head greater than `head K`, using step 3, and return its predecessor.
5. `dies_iff (k : ℕ) : Dies k ↔ certify k ∣ twinLo (head k) ∨ certify k ∣ twinHi (head k)`. By `stage_succ`, the old head remains admissible iff neither divisibility holds. If it remains admissible it remains least, by step 1. All tests here are decidable.

The useful strengthening is **transport to death**:
```lean
theorem transport_to_death {K n : ℕ} (hn : 1 ≤ n) (hs : n ∈ searchSet K) :
    ∃ k, K ≤ k ∧ Dies k ∧ head k = head K ∧ head k ∈ searchSet k
```
Indeed `head K ≤ n` by minimality, so `head K ≤ stageWindow K`. Take step 4's death stage. Its head is still the same, is admissible there by definition, and the window has only grown (`stage_subset_of_le`, monotonicity of `sup`, `window_mono`). Thus this reduction loses **no** successful positive search, even if the original witness was not least.

### Exact one-line residual

```lean
∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ Direct k
```

No separate `Dies k` conjunct is needed: equality implies divisibility in step 5. Here is why the residual is **equivalent**, not just sufficient:

* **`OftenSearch → residual`.** Start the search at `max K 1`, so index zero cannot witness it (the stage contains a blocker dividing zero). Transport to death. By the agreed window exactness, both members of the dying head are prime. Step 5 gives divisibility of one of them by `certify k ≥ 2`; hence equality.
* **`residual → OftenSearch`.** At a direct stage put `q := certify k` and `n := head k`. Both members are at least `5`, survive stage `k`, and are at most `q+2`. **Every** number `a ≥ 2` surviving this stage with `a ≤ q+2` is prime when `q ≥ 5`: otherwise write `a = u*v` with `2 ≤ u ≤ v`. Any blocker dividing `u` would divide `a`, so `u` survives, whence `q ≤ u` by `next_le`. Then `q*q ≤ a ≤ q+2`, impossible. Thus direct stages give actual twins with lower member at least `certify k - 2`. Step 2 makes these unbounded; apply the stipulated unbounded-twins-to-`OftenSearch` bridge. This argument does **not** assume a direct head is inside its own stage's window.

**Input ledger:** steps 1–5, transport, and the factor argument use only finite arithmetic and leastness. The last implication reuses the bridge in the question; if rebuilding its stage-selection argument using `twinSieve_of_lt_two_mul`, the consecutive-prime gap bound (Bertrand) is a separate input, not a consequence of that Lean lemma. The only new open input is the displayed `Direct` residual. Step 4 supplies arbitrarily late *divisibilities* with an explicit finite scan bound; it gives no bound forcing their quotients to be `1`.