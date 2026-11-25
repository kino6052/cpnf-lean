**The mass threshold requires a cluster, not an outlier.** In fact, for \(t\ge2\), a block meeting the threshold must contain **more than \(t/24\) twin indices**. I would replace the first moment by an uncentered second moment: there is a block statistic for which *one* twin suffices, *no* twins cannot suffice, and both implications hold on the very same block.

### 1. What a block with no passes contributes

Write \(L=t^2+1\) for the block length and \(P\) for its number of passes. On a failure, your `score_sq_le_hi_of_gt` gives
\[
s_n^2\le 6n+1\le12t^2+1.
\]
Thus for \(t\ge2\), \(2s_n\le7t\), since \(4(12t^2+1)\le49t^2\). On a pass, \(s_n=6n-1<12t^2\). Consequently
\[
2\,\mathrm{scoreMass}(t)\ \le\ 7t(L-P)+24t^2P.
\]
With no passes this gives at most \(7tL/2\), against a threshold of \(4tL\). This is an **upper bound**, not an actual common value for such blocks. If an exact computation in sieve-count terms is wanted, the no-pass mass is
\[
\sum_{j=1}^{\lfloor\sqrt{12t^2+1}\rfloor}
\#\{n\in [t^2,2t^2]:s_n\ge j\}.
\]
Each row is counted exactly \(s_n\) times; knowing \(P=0\) truncates this sum but does not supply its individual counts.

In particular, \(4tL<\mathrm{scoreMass}(t)\) implies \(8tL<7tL+24t^2P\), hence \(L<24tP\). **Even a guaranteed pass in every sufficiently large block would not, by the one-pass budget argument, give the mass hypothesis.** Bare cofinality gives still less information about clustering.

The forward direction of (3) is therefore valid, but I have neither a proof nor a refutation of its arithmetic converse. Ruling out a *budget argument* for the converse is not ruling out a theorem about these particular primes.

### 2. A second moment with an exact one-pass threshold

Use the blocks \([N,2N]\) with integer left endpoint, so that a twin at \(N\) can witness its own block. The first lemma is the finite test below: **compare the sum of squared scores to the sum of upper members**. On a null block each term is at most its corresponding upper member. But even the *smallest* passing score squared exceeds the *entire* upper-member budget when \(N\ge2\):
\[
 (6N-1)^2>(N+1)(12N+1)\ \ge\ \sum_{n=N}^{2N}(6n+1).
\]
This is why the second moment works where the first does not. No estimate for the distribution of the failing scores is needed in either direction.

Here is code to append inside `namespace CPNF` in `Correspondence.lean`, with no new imports. I have not run Lean here.

```lean
theorem energy_block_iff {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc N (2*N), twinHi n) <
        (∑ n ∈ Finset.Icc N (2*N), score n * score n) ↔
      ∃ n ∈ Finset.Icc N (2*N), score n = twinLo n := by
  constructor
  · intro he
    by_contra h
    apply (not_lt_of_ge ?_) he
    apply Finset.sum_le_sum
    intro n hn
    have hlo := (Finset.mem_Icc.mp hn).1
    have hn1 : 1 ≤ n := by omega
    have hf : score n ≠ twinLo n := fun hp => h ⟨n, hn, hp⟩
    exact score_sq_le_hi_of_gt hn1 (lt_of_le_of_ne (score_le_lo n hn1) hf)
  · rintro ⟨n, hn, hp⟩
    have hb := Finset.mem_Icc.mp hn
    have hc : (Finset.Icc N (2*N)).card = N+1 := by
      rw [Nat.card_Icc]
      omega
    have budget :
        (∑ m ∈ Finset.Icc N (2*N), twinHi m) ≤ (N+1)*(12*N+1) := by
      calc
        _ ≤ ∑ m ∈ Finset.Icc N (2*N), (12*N+1) := by
          apply Finset.sum_le_sum
          intro m hm
          have hu := (Finset.mem_Icc.mp hm).2
          unfold twinHi
          omega
        _ = _ := by simp [hc, Nat.nsmul_eq_mul]
    have single :
        score n * score n ≤ ∑ m ∈ Finset.Icc N (2*N), score m * score m :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (score i * score i)) hn
    have hlow : 6*N-1 ≤ score n := by
      rw [hp, twinLo]
      omega
    have gap : (N+1)*(12*N+1) < (6*N-1)*(6*N-1) := by
      obtain ⟨k, rfl⟩ : ∃ k, N = k+2 := ⟨N-2, by omega⟩
      rw [show 6*(k+2)-1 = 6*k+11 by omega]
      nlinarith
    exact lt_of_le_of_lt budget
      (lt_of_lt_of_le gap ((Nat.mul_le_mul hlow hlow).trans single))

def CofinalScoreEnergy : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ 2 ≤ N ∧
    (∑ n ∈ Finset.Icc N (2*N), twinHi n) <
      (∑ n ∈ Finset.Icc N (2*N), score n * score n)

theorem energy_iff_cofinal_pass :
    CofinalScoreEnergy ↔ ∀ K : ℕ, ∃ n, K ≤ n ∧ score n = twinLo n := by
  constructor
  · intro H K
    obtain ⟨N, hKN, hN, he⟩ := H K
    obtain ⟨n, hn, hp⟩ := (energy_block_iff hN).mp he
    exact ⟨n, hKN.trans (Finset.mem_Icc.mp hn).1, hp⟩
  · intro H K
    obtain ⟨n, hn, hp⟩ := H (K+2)
    refine ⟨n, by omega, by omega, (energy_block_iff (by omega : 2 ≤ n)).mpr ?_⟩
    exact ⟨n, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hp⟩

theorem twins_of_scoreEnergy (H : CofinalScoreEnergy) :
    ∀ K : ℕ, ∃ n, K ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  intro K
  obtain ⟨n, hn, hp⟩ := energy_iff_cofinal_pass.mp H (K+1)
  exact ⟨n, by omega, (twin_iff_score_eq_lo (by omega)).mpr hp⟩

theorem cofinal_pass_of_mass (H : CofinalScoreMass) :
    ∀ K : ℕ, ∃ n, K ≤ n ∧ score n = twinLo n := by
  intro K
  obtain ⟨n, hn, _, hp⟩ := passing_beyond_of_scoreMass H K
  exact ⟨n, hn, hp⟩

theorem energy_of_mass (H : CofinalScoreMass) : CofinalScoreEnergy :=
  energy_iff_cofinal_pass.mpr (cofinal_pass_of_mass H)
```

### 3. What is actually weaker?

No condition can be **logically strictly weaker than twins and sufficient for twins**: sufficiency is the implication in the opposite direction. Energy attains the weakest possible strength, namely equivalence. Relative to the original mass condition, the proved implication is `energy_of_mass`; I would not label it *strict* at the cofinal arithmetic level. What is removed, provably, is the need to extract a growing number of twins from each successful test.

Of the other candidates, a maximum should cross the **failure envelope** \(\sqrt{6N+1}\), not outgrow the absolute ceiling \(6N-1\). Tail counting at that envelope also works, but the needed estimate is a **lower** bound of one survivor, not an upper sieve bound. Plain strict records need no twin hypothesis at all: the scores are unbounded by `admissible_iff_score` at `head k` and `certify_ge_idx`, and first crossings of new heights give records. Their existence contains no estimate of their height relative to their index.

The practical distinction is the target for a future proof: **mass asks for clusters of order \(t\); energy asks for one uncompensated squared score, and a single twin is guaranteed to supply it.**
