# Frontier call: clean Lean proof of the single-progression count

I am stuck on one finite counting lemma and want a complete proof route, not a
review. The statement is yours from the build plan; the proof is pure `ℕ` floor
arithmetic and should be a one-liner with the right library lemma.

## The exact statement (Lean 4 + Mathlib, `import Mathlib`)

```lean
theorem progression_card (W D r : ℕ) (hD : 0 < D) (hr : 1 ≤ r) (hrD : r ≤ D) :
    ((Finset.Icc 1 W).filter (fun n => n % D = r % D)).card = (W + D - r) / D := by
  ...
```

In words: the indices `n ∈ [1, W]` with `n ≡ r (mod D)` number `⌊(W + D − r)/D⌋`.
Here `1 ≤ r ≤ D`, so `r % D = r` unless `r = D` (zero class). The answer is `0`
when `W < r`, and `⌊(W − r)/D⌋ + 1` when `r ≤ W` — both equal `(W + D − r)/D`.

## What I tried and where it fails

1. `Nat.count_modEq_card` counts in `[0, b)`: gives `b/D + [v%D < b%D]`. I
   rewrote the `[1,W]` window to `range (W+1)` with `0` removed, but the trailing
   `omega` on the arithmetic did not close.
2. A direct bijection `k ↦ r + k·D` from `range ((W+D-r)/D)` to the filtered set.
   Both directions reduce to facts about `n − r` and `n % D` that `omega` will
   not prove, because it treats `n % D` and `n − r` as unrelated atoms.
3. I did prove the isolated identity
   `(W + D - r) / D = (W - r) / D + 1` for `r ≤ W` using
   `Nat.add_div_right` after rewriting `W + D - r = (W - r) + D`.

The wall is always the same: `omega`/`linarith` cannot reason about `n % D` or
`n - r` in `ℕ`, so any proof must explicitly invoke the division/decomposition
lemmas (`Nat.div_add_mod`, `Nat.mod_eq_of_lt`, `Nat.mod_lt`) before `omega` sees
a clean linear goal.

## What I want

1. A complete, compilable Lean proof of `progression_card`, using the library
   (`Nat.div_add_mod`, `Nat.mod_eq_of_lt`, `Nat.mod_lt`, `Nat.add_div_right`, or
   `Int.Ioc_filter_modEq_card` / `Nat.Ioc_filter_modEq_card` with floors/ceils on
   `ℚ`). Name the exact lemma and the exact rewrite order.
2. If the cleanest route is `Nat.Ioc_filter_modEq_card` over `ℚ`, give the
   statement of that theorem and the `norm_num`/`linarith`/`gcongr` chain that
   turns `⌊(W−r)/D⌋ − ⌊(0−r)/D⌋` into `(W+D−r)/D`.
3. Explicitly state any helper lemma you rely on, fully quantified, so I can add
   it if it is not in Mathlib.

Prefer a short correct proof over an approximate one. If the natural proof
genuinely needs a separate helper lemma about `⌊(W−r)/D⌋ = (W−r)/D`, state it.


---

# Full Lean sources of the repo (attach-everything policy)

## lakefile.toml

```lean
name = "cpnf-lean"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["CpnfLean"]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.36.0"

[[lean_lib]]
name = "CpnfLean"

```

## CpnfLean.lean

```lean
import CpnfLean.Stage
import CpnfLean.Twin
import CpnfLean.TwinProcess
import CpnfLean.TwinStage
import CpnfLean.Chase

```

## CpnfLean/Sieve.lean

```lean
import Mathlib

/-!
# CPNF — the sieve operator

The only primitive of the framework: a number survives a set of blockers when none of
them divides it. No primality is assumed here.

Blockers are kept as a `Finset`: the process only ever certifies into a finite set, and a
finite set is exactly what decides "survives" stage by stage.
-/

namespace CPNF

/-- `Survives B n`: `n` is not divisible by any blocker in `B`. -/
def Survives (B : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ B, ¬ p ∣ n

instance (B : Finset ℕ) (n : ℕ) : Decidable (Survives B n) :=
  inferInstanceAs (Decidable (∀ p ∈ B, ¬ p ∣ n))

/-- The sieve operator of the paper: survivors of `B` among the candidates `≥ 2`. -/
def sieve (B : Finset ℕ) : Set ℕ := { n | 2 ≤ n ∧ Survives B n }

instance (B : Finset ℕ) (n : ℕ) : Decidable (n ∈ sieve B) :=
  inferInstanceAs (Decidable (2 ≤ n ∧ Survives B n))

theorem survives_empty (_n : ℕ) : Survives ∅ _n := by
  intro p hp
  exact absurd hp (Finset.notMem_empty p)

/-- Membership in the sieve, spelled as a plain conjunction: this is the shape every
    later proof uses, so it never has to be rebuilt inline. -/
theorem mem_sieve_iff {B : Finset ℕ} {n : ℕ} : n ∈ sieve B ↔ 2 ≤ n ∧ Survives B n := Iff.rfl

/-- A divisor of a number is at most it, once the number is positive. Surviving a blocker
    therefore survives at least that blocker — not the other way round, which is false
    (`2 < 4` yet `2 ∣ 4`). -/
theorem le_of_dvd_pos {p n : ℕ} (hp : 0 < n) (h : p ∣ n) : p ≤ n := Nat.le_of_dvd hp h

/-- Adding blockers can only remove survivors. -/
theorem sieve_insert_subset (B : Finset ℕ) (c : ℕ) : sieve (insert c B) ⊆ sieve B := by
  rintro n ⟨h2, hs⟩
  exact ⟨h2, fun p hp => hs p (Finset.mem_insert_of_mem hp)⟩

theorem survives_insert_of_survives {B : Finset ℕ} {c n : ℕ} (hs : Survives B n)
    (hcn : ¬ c ∣ n) : Survives (insert c B) n := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact hcn
  · exact hs p hp

end CPNF

```

## CpnfLean/Process.lean

```lean
import Mathlib
import CpnfLean.Sieve

/-!
# CPNF — the certification process

At each stage the process certifies the least survivor and adds it to the blockers.
`stage k` is the blocker set after `k` stages; `certify k` is the number stage `k` certifies.
Nothing here assumes what a prime is: only survival and minimality.

The paper works with sets; we keep blockers in a `Finset`, because every stage only ever
*certifies one more number* and a finite blocker set is exactly what decides survival.
-/

namespace CPNF

/-! ## Existence of a survivor -/

/-- Every blocker set made of numbers `≥ 2` has a survivor: take `(max + 1)! + 1`.
    It is `≥ 2`, and no blocker divides it, since every blocker divides `(max + 1)!`. -/
theorem sieve_nonempty {B : Finset ℕ} (h2 : ∀ p ∈ B, 2 ≤ p) : (sieve B).Nonempty := by
  -- The candidate: one more than the factorial of the largest blocker plus one.
  refine ⟨(B.sup id + 1).factorial + 1, ?_, ?_⟩
  -- It is `≥ 2`, because the factorial is positive.
  · have hpos : 0 < (B.sup id + 1).factorial := Nat.factorial_pos _
    omega
  -- No blocker divides it: `p ∣ F` and `p ∣ F + 1` would force `p ∣ 1`, hence `p ≤ 1`.
  · intro p hp hdiv
    -- Every blocker divides the factorial: it is positive and at most `max + 1`.
    have hdvd : p ∣ (B.sup id + 1).factorial :=
      Nat.dvd_factorial (by have := h2 p hp; lia)
        (by have := Finset.le_sup (f := id) hp; exact Nat.le_succ_of_le this)
    -- Unfold both divisibilities into equations.
    obtain ⟨b, hb⟩ := hdiv
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hb
    -- `p * c + 1 = p * b`, so the difference `p * (b - c)` is `1`.
    have hp1 : p ∣ 1 := ⟨b - c, by rw [Nat.mul_sub]; omega⟩
    -- A divisor of `1` is at most `1`, contradicting `2 ≤ p`.
    have hp2 : p ≤ 1 := Nat.le_of_dvd (show 0 < 1 by norm_num) hp1
    have := h2 p hp
    omega

/-! ## One stage -/

/-- A number is certified at the next stage exactly when it is the least survivor. -/
def Step (B : Finset ℕ) (n : ℕ) : Prop := IsLeast (sieve B) n

/-- The number one stage certifies: the least survivor of `B`. -/
noncomputable def certifyOf (B : Finset ℕ) (h2 : ∀ p ∈ B, 2 ≤ p) : ℕ :=
  Nat.find (sieve_nonempty h2)

/-- One stage: certify the least survivor, and add it to the blockers. -/
noncomputable def advance (B : Finset ℕ) (c : ℕ) : Finset ℕ := insert c B

/-- The certified number at this stage is the least survivor. -/
theorem step_advance (B : Finset ℕ) (h2 : ∀ p ∈ B, 2 ≤ p) :
    Step B (certifyOf B h2) :=
  -- `Nat.find` gives a survivor, and it is minimal among survivors.
  ⟨Nat.find_spec (sieve_nonempty h2), fun _ hm => Nat.find_min' (sieve_nonempty h2) hm⟩

/-! ## The hypotheses carry to the next stage -/

/-- Every certified number is `≥ 2`, so the next stage's hypothesis holds by construction. -/
theorem above_one_advance {B : Finset ℕ} {c : ℕ} (h2 : ∀ p ∈ B, 2 ≤ p) (hc : 2 ≤ c) :
    ∀ p ∈ advance B c, 2 ≤ p := by
  intro p hp
  -- Either `p` is the new certified number, or it was already a blocker.
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact hc
  · exact h2 p hp

end CPNF

```

## CpnfLean/Stage.lean

```lean
import Mathlib
import CpnfLean.Sieve
import CpnfLean.Process

/-!
# CPNF — the ordinary process, stage by stage

`stage k` is the blocker set after `k` stages; `certify k` is the number stage `k` certifies.
Since `stage k` is the result of `k` applications of `advance`, it is built recursively.

What is proved here is what CPNF itself can state — one step at a time, no completed
totality of primes:

* **Determinism** — each stage has exactly one next number, and no choice is left open.
* **Monotonicity** — certified numbers stay certified.
* **Non-termination** — every stage has a survivor to certify next, so the process never
  reaches a last stage. This is the paper's Theorem 4 (Euclid), re-stated as a behaviour of
  the process rather than a claim about a set of all primes.
-/

namespace CPNF

/-! ## The stage sequence -/

/-- `stage k` is the blocker set after `k` stages, starting from no blockers.
    The guarded `if` carries the well-formedness (`≥ 2`) of the blockers forward: the
    recursion is ordinary `Nat.rec`, and the condition is established at each step. -/
noncomputable def stage : ℕ → Finset ℕ
  | 0 => ∅
  -- Stage `k + 1`: add the least survivor, provided every blocker so far is `≥ 2`.
  | k + 1 => if h : ∀ p ∈ stage k, 2 ≤ p then insert (certifyOf (stage k) h) (stage k) else stage k

/-- The process starts from no blockers. -/
theorem stage_zero_empty : stage 0 = ∅ := rfl

/-- Every blocker set the process reaches is made of numbers `≥ 2`: at each step the
    guarded `if` is taken, and `above_one_advance` keeps the property. -/
theorem above_one_stage (k : ℕ) : ∀ p ∈ stage k, 2 ≤ p := by
  induction k with
  | zero =>
    -- The empty blocker set has no blockers at all.
    intro p hp
    exact absurd hp (Finset.notMem_empty p)
  | succ k ih =>
    -- At the step, the guard holds (by `ih`), so `stage (k+1)` inserts a certified number.
    simp only [stage, dif_pos ih]
    exact above_one_advance ih (step_advance (stage k) ih).1.1

/-- The number stage `k + 1` certifies: the least survivor of `stage k`. -/
noncomputable def certify (k : ℕ) : ℕ := certifyOf (stage k) (above_one_stage k)

/-- One stage unfolds to the old blockers plus the certified number. -/
theorem stage_succ (k : ℕ) : stage (k + 1) = insert (certify k) (stage k) := by
  -- The guard is established by `above_one_stage`, and `certify` is its `Nat.find`.
  simp only [stage, dif_pos (above_one_stage k)]
  rfl

/-! ## Determinism -/

/-- Each stage's verdict is the least survivor: not one option among several, but a
    unique number, fixed by the blockers alone. -/
theorem step_stage (k : ℕ) : Step (stage k) (certify k) :=
  step_advance (stage k) (above_one_stage k)

/-! ## Monotonicity -/

/-- One more stage only adds a blocker. -/
theorem stage_subset_succ (k : ℕ) : stage k ⊆ stage (k + 1) := by
  rw [stage_succ]
  exact Finset.subset_insert _ _

/-- Across any number of stages, earlier blockers remain blockers. -/
theorem stage_subset_of_le {j k : ℕ} (h : j ≤ k) : stage j ⊆ stage k := by
  induction k, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k _ ih => exact Finset.Subset.trans ih (stage_subset_succ k)

/-! ## Non-termination -/

/-- Every stage has a survivor to certify next, so no stage is the last: the blocker set
    above 1 always leaves at least one number undivided, namely `(max + 1)! + 1`. -/
theorem always_a_next_step (k : ℕ) : (sieve (stage k)).Nonempty :=
  sieve_nonempty (above_one_stage k)

/-- Unfolding of the previous fact: the certified number is really a survivor of the
    current stage, so the process does not stop after `k` stages. -/
theorem certify_survives (k : ℕ) : certify k ∈ sieve (stage k) :=
  (step_stage k).1

/-- The certified number is the *least* survivor: every other survivor is at least it. -/
theorem next_le (k m : ℕ) (hm : m ∈ sieve (stage k)) : certify k ≤ m :=
  -- `step_stage` gives `certify k ∈ lowerBounds (sieve (stage k))`, whose bound is implicit.
  (step_stage k).2 hm

end CPNF

```

## CpnfLean/Twin.lean

```lean
import Mathlib
import CpnfLean.Sieve

/-!
# CPNF — twin indices

A twin index `n` stands for the pair `(6n - 1, 6n + 1)`. An index is admissible for a
blocker set when both numbers survive every blocker. Nothing here assumes that either
number is "prime": admissibility is survival, exactly as in the ordinary process.

Two repairs to the paper's definitions, both forced by Lean:

* the certification window bounds the index against `y²`, not against `y`: the paper's
  `6n + 1 ≤ y` combined with `n ≤ ⌊(y² - 1)/6⌋` is a typo, and only the square form is
  consistent with the window it defines;
* the pair is not `6n ± 1` reduced, but `6n - 1` in `ℕ`, i.e. `0` at `n = 0`. Facts that
  are true only for `n ≥ 1` say so.
-/

namespace CPNF

/-- The left member of the pair at twin index `n`. -/
def twinLo (n : ℕ) : ℕ := 6 * n - 1

/-- The right member of the pair at twin index `n`. -/
def twinHi (n : ℕ) : ℕ := 6 * n + 1

/-- An index is admissible for `B` when both members survive every blocker in `B`. -/
def Admissible (B : Finset ℕ) (n : ℕ) : Prop := Survives B (twinLo n) ∧ Survives B (twinHi n)

instance (B : Finset ℕ) (n : ℕ) : Decidable (Admissible B n) :=
  inferInstanceAs (Decidable (Survives B (twinLo n) ∧ Survives B (twinHi n)))

/-- The certification window `W(y) = ⌊(y² - 1) / 6⌋` for the largest blocker `y`. -/
def window (y : ℕ) : ℕ := (y ^ 2 - 1) / 6

/-- The twin sieve: indices that survive the blockers and lie inside the window. -/
def twinSieve (B : Finset ℕ) (y : ℕ) : Set ℕ := { n | Admissible B n ∧ n ≤ window y }

/-! ## Facts about the pair -/

/-- The second member is never divisible by two. -/
theorem not_two_dvd_twinHi (n : ℕ) : ¬ (2 : ℕ) ∣ twinHi n := by
  simp only [twinHi]
  omega

/-- For `n ≥ 1` the first member is `6m + 5`, and never divisible by two. -/
theorem not_two_dvd_twinLo {n : ℕ} (hn : 1 ≤ n) : ¬ (2 : ℕ) ∣ twinLo n := by
  -- Write `n = m + 1`, so the member is `6m + 5`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h : twinLo (m + 1) = 6 * m + 5 := by simp only [twinLo]; omega
  rw [h]
  omega

/-! ## The window -/

/-- The window really bounds the pair: `6n + 1 ≤ y²` for every eligible index. -/
theorem window_bound {n y : ℕ} (h : n ≤ window y) (hy : 0 < y ^ 2) : 6 * n + 1 ≤ y ^ 2 := by
  -- The window times six is at most `y² - 1`.
  have hw : window y * 6 ≤ y ^ 2 - 1 := by
    simp only [window]
    omega
  -- Hence `6n + 1 ≤ 6W + 1 ≤ y²`.
  have : 6 * n ≤ 6 * window y := by omega
  omega

/-- For a largest blocker `y ≥ 7` the window holds at least `y` indices, so the window is
    never shorter than the largest blocker itself. This is the honest direction of growth:
    the window rises quadratically, an index bound rises linearly. -/
theorem window_ge (y : ℕ) (hy : 7 ≤ y) : y ≤ window y := by
  -- Turn the claim into a multiplication: `y ≤ (y² - 1)/6` iff `y * 6 ≤ y² - 1`.
  rw [window, Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 6)]
  -- Enough to show `6y + 1 ≤ y²`, i.e. `y * (y - 6) ≥ 1`.
  rw [pow_two]
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 7 := ⟨y - 7, by omega⟩
  ring_nf
  omega

/-! ## Blockers that kill every index -/

/-- A pair has no divisibility by two in either member. -/
theorem two_nor {n : ℕ} (hn : 1 ≤ n) :
    ¬ (2 : ℕ) ∣ twinLo n ∧ ¬ (2 : ℕ) ∣ twinHi n :=
  ⟨not_two_dvd_twinLo hn, not_two_dvd_twinHi n⟩

/-- The twin process starts after `2` and `3`: its blockers are only numbers above `3`.
    This is the paper's `B ← {2, 3}` read correctly — `2` and `3` never block a pair
    (`6n ± 1` is coprime to `6`), so they are dropped rather than carried as blockers. -/
def TwinBlockers (B : Finset ℕ) : Prop := ∀ p ∈ B, 3 < p

end CPNF

```

## CpnfLean/TwinProcess.lean

```lean
import Mathlib
import CpnfLean.Sieve
import CpnfLean.Twin

/-!
# CPNF — the twin process

The twin process grows a blocker set of numbers above `3` and certifies twin indices whose
pair is admissible inside the certification window. Nothing here presupposes that the pair
is prime; an index is certified because the blockers leave it alone, not because it is.

The certification window follows the paper's consistent form: an index `n` may be
certified when `6n + 1 ≤ y²`, i.e. `n ≤ ⌊(y² - 1)/6⌋`, where `y` is the largest blocker.
-/

namespace CPNF

/-! ## Extending twin blockers -/

/-- Adding a blocker above `3` keeps the twin-blocker property. -/
theorem twinBlockers_insert {B : Finset ℕ} (c : ℕ) (hc : 3 < c) (h : TwinBlockers B) :
    TwinBlockers (insert c B) := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact hc
  · exact h p hp

/-- Dropping a blocker can only enlarge the twin sieve. -/
theorem twinSieve_subset_of_subset {B B' : Finset ℕ} (h : B ⊆ B') (y : ℕ) :
    twinSieve B' y ⊆ twinSieve B y := by
  rintro n ⟨⟨hlo, hhi⟩, hwin⟩
  -- Each member survives more blockers, so it survives `B`.
  refine ⟨⟨fun p hp => hlo p (h hp), fun p hp => hhi p (h hp)⟩, hwin⟩

end CPNF

```

## CpnfLean/TwinStage.lean

```lean
import Mathlib
import CpnfLean.Sieve
import CpnfLean.Twin
import CpnfLean.TwinProcess
import CpnfLean.Stage

/-!
# CPNF — the twin process, stage by stage

The paper's Algorithm 2 carries two growing objects, the blockers `B` and the set `T` of
certified twin indices, and alternates a completion phase with a search phase. Read as a
behaviour of the ordinary process, it is simpler than that: the blockers at stage `k` are
exactly `stage k`, and the twin search at stage `k` looks for an admissible index inside
the window belonging to that stage. So the twin process is a *readout* of the ordinary
process — it adds nothing to the blockers, it only observes them.

What that buys, honestly:

* **Irreversibility** (the paper's Lemma 9) is not an extra argument here. Blockers only
  accumulate, so admissibility at an earlier stage is admissibility forever; an index that
  was ever certifiable stays certified.
* **Certification is stage-relative**: "certified" means "admissible for the blockers of
  stage `k`", never "prime". Nothing in this file decides what a prime is.
* **The search is decidable at each stage**, because the window is finite.

What is deliberately *not* here: any claim that a certified index is always found. Whether
every stage's window contains an admissible index is the endless-chase question, and it is
open. This file proves the structure the chase needs, not the chase.
-/

namespace CPNF

/-! ## The largest blocker of a stage, and the window it sizes -/

/-- The largest blocker at stage `k`, i.e. the `y` that sizes the window.
    `stage 0` is empty, so the fallback value `0` is used only there. -/
noncomputable def maxBlocker (k : ℕ) : ℕ := (stage k).sup id

/-- The window at stage `k`: the paper's `W_k = ⌊(y_k² - 1)/6⌋`. -/
noncomputable def stageWindow (k : ℕ) : ℕ := window (maxBlocker k)

/-! ## The twin search at one stage -/

/-- The indices the twin search at stage `k` may certify: admissible for the blockers of
    stage `k`, and inside that stage's window. -/
noncomputable def searchSet (k : ℕ) : Set ℕ := twinSieve (stage k) (maxBlocker k)

/-- An index is certified at stage `k` when it is the least index the search at `k` offers.
    This is the paper's `min(candidates)`, with minimality standing in for "found". -/
noncomputable def TwinCertifiedAt (k : ℕ) (n : ℕ) : Prop := IsLeast (searchSet k) n

/-- An index is certified when some stage certifies it. -/
noncomputable def TwinCertified (n : ℕ) : Prop := ∃ k, TwinCertifiedAt k n

/-! ## What the search offers -/

/-- A certified index at stage `k` satisfies the two conditions the paper asks of
    `min(candidates)`: it is admissible for that stage's blockers, and inside its window. -/
theorem certifiedAt_spec {k n : ℕ} (h : TwinCertifiedAt k n) :
    Admissible (stage k) n ∧ n ≤ stageWindow k := by
  -- `IsLeast` gives membership; the search set is a set-builder, so unfold it.
  have hm : n ∈ searchSet k := h.1
  simp only [searchSet, twinSieve, Set.mem_ofPred_eq] at hm
  -- `twinSieve` bounds by `window (maxBlocker k)`, which is `stageWindow k`.
  exact ⟨hm.1, by simpa only [stageWindow] using hm.2⟩

/-- A certified index at stage `k` is admissible for the blockers of stage `k`. -/
theorem certifiedAt_admissible {k n : ℕ} (h : TwinCertifiedAt k n) :
    Admissible (stage k) n := (certifiedAt_spec h).1

/-- A certified index at stage `k` lies inside that stage's window. -/
theorem certifiedAt_in_window {k n : ℕ} (h : TwinCertifiedAt k n) : n ≤ stageWindow k :=
  (certifiedAt_spec h).2

/-- The search at `k` is minimal: no smaller index is both admissible and inside the
    window. This is the "least" half of `min(candidates)`. -/
theorem certifiedAt_least {k n m : ℕ} (h : TwinCertifiedAt k n)
    (hm : Admissible (stage k) m) (hwin : m ≤ stageWindow k) : n ≤ m := by
  -- `m` is in the search set, so minimality of `n` applies to it.
  exact h.2 (by
    simp only [searchSet, twinSieve, Set.mem_ofPred_eq]
    exact ⟨hm, by simpa only [stageWindow] using hwin⟩)

/-! ## Irreversibility (the paper's Lemma 9) -/

/-- Blockers only accumulate, so surviving the blockers of a later stage implies surviving
    those of an earlier one: adding blockers can only remove survivors. -/
theorem admissible_of_stage_le {j k n : ℕ} (hjk : j ≤ k) (h : Admissible (stage k) n) :
    Admissible (stage j) n := by
  -- The earlier blocker set is contained in the later one.
  have hsub : stage j ⊆ stage k := stage_subset_of_le hjk
  -- Each member survives the smaller set because it survived the larger one.
  exact ⟨fun p hp => h.1 p (hsub hp), fun p hp => h.2 p (hsub hp)⟩

/-- An index certified at stage `j` is admissible for stage `j` — the only stage it was
    certified for. It need **not** stay admissible later: a new blocker may divide it.
    So "irreversibility" holds for the *record* of certification, not for admissibility. -/
theorem certified_admissible_at_its_stage {j n : ℕ} (h : TwinCertifiedAt j n) :
    Admissible (stage j) n := certifiedAt_admissible h

/-! ## Window sizes -/

/-- Once the largest blocker is at least `7`, the window holds at least that many indices. -/
theorem stageWindow_ge {k y : ℕ} (h : maxBlocker k = y) (hy : 7 ≤ y) : y ≤ stageWindow k := by
  -- Rewrite the window to the largest blocker and use the numeric bound.
  simp only [stageWindow, h]
  exact window_ge y hy

/-! ## The crossing step

The reverse half of the bridge needs one prime-free fact: an admissible index whose lower
member sits below `2y` is already inside the window. We keep it separate from the bridge so
that the bridge only has to pick the stage and supply the gap bound. -/

/-- **Crossing step.** If the largest blocker is `y ≥ 3` and the lower member `6n - 1` is
    below `2y`, then an admissible index `n ≥ 1` already lies in the twin sieve of its own
    stage. Unconditional: the window bound is pure arithmetic, so this needs no prime input
    at all — exactly the part of the bridge that we *can* prove today. -/
theorem twinSieve_of_lt_two_mul {k n y : ℕ} (hmax : maxBlocker k = y) (hn : 1 ≤ n)
    (hy : 3 ≤ y) (hlt : twinLo n < 2 * y) (h : Admissible (stage k) n) :
    n ∈ twinSieve (stage k) y := by
  -- Membership in the sieve is admissibility plus the window bound.
  rw [twinSieve, Set.mem_ofPred_eq]
  refine ⟨h, ?_⟩
  -- The window bound needs `6n + 1 ≤ y * y`, then peeling one off.
  have hle : 6 * n + 1 ≤ y * y := by
    -- `hlt` is `6n - 1 < 2y`, so `6n ≤ 2y`; then `6n + 1 ≤ 2y + 1 ≤ y * y` since `y ≥ 3`.
    have h2 : 6 * n ≤ 2 * y := by
      have hlo : twinLo n = 6 * n - 1 := rfl
      omega
    nlinarith [hy, h2]
  -- Unfold the window to an explicit product so the division lemma applies.
  have hwin : window y = (y * y - 1) / 6 := by
    rw [window, pow_two]
  rw [hwin, Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 6)]
  -- Now `n * 6 ≤ y * y - 1`, which follows from `6n + 1 ≤ y * y`.
  omega

end CPNF

```

## CpnfLean/Count.lean

```lean
import Mathlib

/-!
# CPNF — the exact finite count

The density-free count of CPNF's twin sieve over a finite window. Everything here is
finite `ℕ` arithmetic: no logarithms, no Mertens, no analytic input.

A blocker `b` kills an index `n` when `b ∣ 6n-1` or `b ∣ 6n+1`. Since `6` is invertible mod
`b`, killing happens in exactly **two** residue classes mod `b`. That is the whole content of
the count: inclusion–exclusion over the finite blocker set, with the progression count done
in `ℕ` so no truncated subtraction can bite.

Moduli below are always `≥ 5` and coprime to `6`. The blockers `2` and `3` are excluded on
purpose: `2` hits nothing (`6n∓1` are odd) and `3` hits nothing (`6n∓1` are `≠ 0` mod 3), but
the "two residue classes" claim is **false** for them, so they must not enter the count.
-/

namespace CPNF

open scoped BigOperators

/-! ## Definitions -/

/-- Blocker `b` **hits** index `n` when it divides one of the twin members `6n-1`, `6n+1`.
    Written in residue form, because divisibility is what the sieve tests but residue
    classes are what can be counted. -/
def hit (b n : ℕ) : Prop := 6 * n % b = 1 ∨ 6 * n % b = b - 1

instance (b n : ℕ) : Decidable (hit b n) := by
  unfold hit
  infer_instance

/-- The product of a finite set of moduli — the modulus of one residue class after
    combining the blockers in `S` by CRT. -/
def d (S : Finset ℕ) : ℕ := ∏ b ∈ S, b

/-- The residues `r ∈ [1, d S]` that are hit by **every** blocker in `S`. Using the positive
    representative `d S` for the zero class keeps this inside `ℕ`. -/
def T (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (d S)).filter (fun r => ∀ b ∈ S, hit b r)

/-- The number of indices in `[1, W]` hit by every blocker of `S`. Inclusion–exclusion adds
    these with alternating signs. -/
def C (W : ℕ) (S : Finset ℕ) : ℕ := ∑ r ∈ T S, (W + d S - r) / d S

/-- The un-hit indices: the set the twin sieve actually keeps. -/
def G (A : Finset ℕ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter (fun n => ∀ b ∈ A, ¬ hit b n)

/-- The moduli the count is allowed to use: each at least `5`, each coprime to `6`, and
    pairwise coprime. -/
def GoodMods (A : Finset ℕ) : Prop :=
  (∀ b ∈ A, 5 ≤ b ∧ Nat.Coprime 6 b) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)

/-! ## 5b. One progression

The count of a single residue class in `[1, W]`. This is the only place arithmetic on the
window enters; everything after is inclusion–exclusion over finite sets. -/

/-- **One progression.** The indices `n ∈ [1, W]` congruent to `r` mod `D` number
    `(W + D - r) / D`. Written so that `W < r` also works: the window is simply too short. -/
theorem progression_card (W D r : ℕ) (hD : 0 < D) (hr : 1 ≤ r) (hrD : r ≤ D) :
    ((Finset.Icc 1 W).filter (fun n => n % D = r % D)).card = (W + D - r) / D := by
  -- `r % D = r` because `1 ≤ r ≤ D`.
  have hrmod : r % D = r := Nat.mod_eq_of_lt (lt_of_le_of_ne hrD (Ne.symm (by omega)))
  rw [hrmod]
  -- The window `[1, W]` is the range `[0, W]` without `0`, and `0` is not in the class.
  have hz : (0 : ℕ) % D ≠ r := by
    rw [Nat.zero_mod]; omega
  have hIcc : Finset.Icc 1 W = (Finset.range (W + 1)).erase 0 := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [hIcc]
  -- Erasing a non-member leaves the filtered count unchanged.
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp [hz])]
  -- Now count a residue class in `[0, W]`.
  rw [← Finset.card_filter, ← Nat.count_eq_card_filter_range]
  -- `Nat.count_modEq_card` gives `(W+1)/D + [r < (W+1) % D]`; show that is `(W+D-r)/D`.
  rw [Nat.count_modEq_card (W + 1) hD r]
  -- Both sides are `⌊(W + D - r)/D⌋`; split on whether a last copy of `r` fits in `[0,W]`.
  rcases le_or_gt r (W + 1) with hW | hW
  · -- A copy sits at `W + 1 - r`; it is `≤ W` exactly when `r ≤ W`.
    rcases le_or_gt r W with hWr | hWr
    · -- `r ≤ W`: the extra term appears and `(W+1)/D` is one more than `(W+D-r)/D`.
      have hlt : r % D < (W + 1) % D := by
        rw [hrmod]
        omega
      rw [if_pos hlt]
      have : (W + D - r) / D = (W + 1) / D := by
        omega
      omega
    · -- `r = W + 1`: no index in `[1, W]` is in the class.
      have hr1 : r = W + 1 := by omega
      have hlt : ¬ (r % D < (W + 1) % D) := by
        rw [hrmod, hr1]; omega
      rw [if_neg hlt]
      rw [hr1]
      omega
  · -- `r > W + 1`: the class misses `[0, W]` entirely, and `W + D - r < D`.
    have hlt : ¬ (r % D < (W + 1) % D) := by
      rw [hrmod]; omega
    rw [if_neg hlt]
    omega

end CPNF

```
