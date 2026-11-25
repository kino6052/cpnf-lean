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

end CPNF
