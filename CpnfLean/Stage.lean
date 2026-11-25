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
