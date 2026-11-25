**Keep all four declarations.** The correction is to the interpretation: strict records partition **stage indices by their head value**, not because strictness alone guarantees a run, but because every positive row’s score is a prime and `certify` attains every prime. For the scan itself, the cleanest interface is pointwise.

**1. Add the pointwise scan theorem first.** In `namespace CPNF`, after `isRecord_of_twin`:

```lean
theorem passing_record_iff_twin {n : ℕ} (hn : 1 ≤ n) :
    (IsRecord n ∧ twinHi n < score n * score n) ↔
    (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) := by
  constructor
  · intro h
    exact (twin_iff_sq_test hn).mpr h.2
  · intro h
    exact ⟨isRecord_of_twin hn h.1 h.2, (twin_iff_sq_test hn).mp h⟩
```

This shows exactly where the record condition matters: it is unused for soundness and must be proved for completeness. Your `no_passing_record_iff_no_twin` is correct, including for `N = 0`. The proposed `Finset` equality follows by extensionality: outside `Icc 1 N` both membership tests fail; inside, apply the pointwise theorem. It is useful, not stronger: it lets clients rewrite a **list of hits as a finset**, its cardinality, or its nonemptiness without losing the indices.

One implementation distinction matters. A declarative filter under `classical` suffices for the equality, but is not a verified executable scan. For that, carry the maximum of scores already seen (initially `0`), emit a record only on strict increase, and prove that the returned hits equal the prime-pair filter. A null output then certifies absence; a log from an unconnected program does not. The running maximum avoids rescanning the prefix, not computing each new row’s score.

**2. Keep `score_le_lo` and the strict bound in `isRecord_of_twin`.** The entire comparison is
\[
\operatorname{score}(m)\le\operatorname{twinLo}(m)
 <\operatorname{twinLo}(n)=\operatorname{score}(n)
 \qquad(1\le m<n).
\]
No `minFac` calculation needs to be repeated in the record proof. In fact, the cleaner reusable statement is **a positive row is twin iff its score attains its upper bound**:

```lean
theorem twin_iff_score_eq_lo {n : ℕ} (hn : 1 ≤ n) :
    (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) ↔
    score n = twinLo n := by
  rw [twin_iff_sq_test hn, sq_test_iff hn]
  exact ⟨score_eq_lo_of_row hn, fun h => h.ge⟩
```

That gives the final equality in the comparison directly, and gives an executable scan the option of testing equality instead of squaring. Keep positivity in `score_le_lo`: `twinLo 0 = 0` is not a positive argument to `Nat.minFac_le`. Also fix the docstring of `score_sq_le_hi_of_gt`: at a shortfall the score squared **does not exceed** the upper member; the theorem has the correct sign.

**3. Yes, add the plateau lemma now.** It justifies the run-length claim already made in the `IsRecord` docstring. The most useful statement does not assume `IsRecord`:

```lean
theorem head_eq_iff_first_crossing {k n : ℕ} (hn : 1 ≤ n) :
    head k = n ↔
      certify k ≤ score n ∧
      ∀ m, 1 ≤ m → m < n → score m < certify k := by
  constructor
  · intro he
    subst n
    refine ⟨(admissible_iff_score hn).mp (head_admissible k), ?_⟩
    intro m hm hlt
    by_contra! h
    exact (not_le_of_gt hlt) (head_le hm ((admissible_iff_score hm).mpr h))
  · rintro ⟨hc, hearlier⟩
    apply le_antisymm (head_le hn ((admissible_iff_score hn).mpr hc))
    by_contra! h
    exact (not_lt_of_ge
      ((admissible_iff_score (one_le_head k)).mp (head_admissible k)))
      (hearlier (head k) (one_le_head k) h)
```

Explicitly, let \(M_n\) be the maximum score on \(1\le m<n\), with empty maximum \(0\). For \(n\ge1\) the lemma reads
\[
\boxed{\quad \mathrm{head}(k)=n
       \iff M_n<\mathrm{certify}(k)\le\mathrm{score}(n).\quad}
\]
The **left endpoint is open, the right closed**: a tie is owned by the earlier index; the blocker equal to the current score is not inserted until the transition to `stage (k+1)`.

This gives the full partition. A non-record has an empty interval. For a strict record, `score n` is the `minFac` of one of two numbers at least `2`, hence prime. It is attained by `certify`: for any prime `p`, take stage `p+1`, use `certify_ge_idx` to put `p` strictly below its killer, then use `stage_eq_primes_lt` and `mem_stage_iff`. Thus the interval contains at least its right endpoint. Strict increase of `certify` makes the stages in it one consecutive run, whose length is the **number of primes** in \((M_n,\mathrm{score}(n)]\), not the numerical difference of the scores. At a stage with `head k = n`, `Dies k` holds exactly when `certify k = score n`: below that endpoint the next killer is still at most the endpoint, and at equality the next killer exceeds it. This is about the window-free `head`, not a claim of `TwinCertifiedAt` throughout the run.

**Bottom line:** records compress the stage description exactly, but forcing a *passing* record beyond every bound is the twin prime conjecture, not a weaker remaining obstacle.
