import Mathlib
import CpnfLean.Head
import CpnfLean.Coverage

/-!
# CPNF — the local endpoint (rung 4 of the unconditional ladder)

The block `(X, 2X]` cut by a roughness threshold `z` splits into exactly three parts:

* `midP` — passing rows, `score n = twinLo n` (these *are* twin indices);
* `midB` — rows whose score is already below the block scale, `score² ≤ X`;
* `midT` — rows between the block scale and the failing bound, `X < score² ≤ twinHi n`.

`local_slack_iff` says the strict slack of this count is **exactly** the existence of a twin
index in the block. Lossless, unconditional, finite: no sieve estimate enters.

What is *not* proved, and is exactly the boxed target, is that the strict inequality holds
cofinally often. The frontier's ladder puts that as the first genuinely analytic rung.
-/

namespace CPNF


theorem fail_sq_le {n : ℕ} (hn : 1 ≤ n) (hf : score n ≠ twinLo n) :
    score n * score n ≤ twinHi n := by
  have hlt : score n < twinLo n := lt_of_le_of_ne (score_le_lo n hn) hf
  exact score_sq_le_hi_of_gt hn hlt

def blk (X : ℕ) : Finset ℕ := Finset.Ioc X (2 * X)
def rough (X z : ℕ) : Finset ℕ := (blk X).filter (fun n => z < score n)
def midB (X z : ℕ) : Finset ℕ :=
  (rough X z).filter (fun n => score n * score n ≤ X)
def midT (X z : ℕ) : Finset ℕ :=
  (rough X z).filter (fun n => ¬ score n * score n ≤ X ∧ score n * score n ≤ twinHi n)
def midP (X z : ℕ) : Finset ℕ := (rough X z).filter (fun n => score n = twinLo n)

/-- **Every row of `R` is passing, below-scale, or in the band.** -/
theorem rough_split (X z : ℕ) (n : ℕ) (hn : n ∈ rough X z) :
    n ∈ midP X z ∨ n ∈ midB X z ∨ n ∈ midT X z := by
  have hr : z < score n := (Finset.mem_filter.mp hn).2
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_filter.mp hn).1
    simp only [blk, Finset.mem_Ioc] at this
    omega
  by_cases hp : score n = twinLo n
  · exact Or.inl (Finset.mem_filter.mpr ⟨hn, hp⟩)
  · have hsq := fail_sq_le hn1 hp
    by_cases hb : score n * score n ≤ X
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hn, hb⟩))
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hn, ⟨hb, hsq⟩⟩))

/-- `midP ∪ midB ∪ midT = rough`. -/
theorem rough_union (X z : ℕ) :
    rough X z = midP X z ∪ midB X z ∪ midT X z := by
  apply Finset.Subset.antisymm
  · intro n hn
    rcases rough_split X z n hn with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  · intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1

/-- A passing row in the block has `score² > X`. -/
theorem hpass_sq_le (X z n : ℕ) (hp : n ∈ midP X z) : ¬ (score n * score n ≤ X) := by
  have hpn : score n = twinLo n := (Finset.mem_filter.mp hp).2
  have hblk := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  simp only [blk, Finset.mem_Ioc] at hblk
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hX : X < k + 1 := hblk.1
  have hlo : twinLo (k + 1) = 6 * k + 5 := by unfold twinLo; omega
  have hsq : X < (6 * k + 5) * (6 * k + 5) := by nlinarith
  intro hcon
  rw [hpn, hlo] at hcon
  nlinarith

/-- **The three parts are pairwise disjoint.** -/
theorem rough_disjoint (X z : ℕ) :
    Disjoint (midP X z ∪ midB X z) (midT X z) ∧
    Disjoint (midP X z) (midB X z) := by
  constructor
  · rw [Finset.disjoint_left]
    intro n hn ht
    have ht' := (Finset.mem_filter.mp ht).2
    rcases Finset.mem_union.mp hn with h | h
    · -- a passing row has `score² = twinLo² > twinHi`, so it cannot be in `midT`
      have hpn : score n = twinLo n := (Finset.mem_filter.mp h).2
      have hblk := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
      simp only [blk, Finset.mem_Ioc] at hblk
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hlo : twinLo (k + 1) = 6 * k + 5 := by unfold twinLo; omega
      have hhi : twinHi (k + 1) = 6 * k + 7 := by unfold twinHi; omega
      rw [hpn, hlo, hhi] at ht'
      nlinarith [ht'.2]
    · exact ht'.1 (Finset.mem_filter.mp h).2
  · rw [Finset.disjoint_left]
    intro n hp hb
    have hp' : score n = twinLo n := (Finset.mem_filter.mp hp).2
    have hb' : score n * score n ≤ X := (Finset.mem_filter.mp hb).2
    exact hpass_sq_le X z n hp hb'


/-- **The partition identity.** -/
theorem rough_card (X z : ℕ) :
    (rough X z).card = (midP X z).card + ((midB X z).card + (midT X z).card) := by
  have hunion : rough X z = midP X z ∪ midB X z ∪ midT X z := rough_union X z
  have hd1 : Disjoint (midP X z ∪ midB X z) (midT X z) := (rough_disjoint X z).1
  have hd2 : Disjoint (midP X z) (midB X z) := (rough_disjoint X z).2
  rw [hunion, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
  omega

/-- **Rung 4: the exact local endpoint.** On a block where the cutoff `z` is below every
    passing score, the strict slack is exactly equivalent to a twin index in the block.
    Lossless, unconditional, finite. -/
theorem local_slack_iff (X z : ℕ) (hz : z < 6 * X - 1) :
    (midB X z).card + (midT X z).card < (rough X z).card ↔
      ∃ n, n ∈ blk X ∧ score n = twinLo n := by
  have hcard := rough_card X z
  constructor
  · intro hlt
    have hpos : 0 < (midP X z).card := by omega
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
    exact ⟨n, (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1,
      (Finset.mem_filter.mp hn).2⟩
  · rintro ⟨n, hnblk, hpass⟩
    have hnonempty : (midP X z).Nonempty := by
      refine ⟨n, ?_⟩
      have hmem : n ∈ blk X := hnblk
      have hnX : X < n := by
        simp only [blk, Finset.mem_Ioc] at hmem
        exact hmem.1
      have hz' : z < score n := by
        rw [hpass]
        unfold twinLo
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hz'⟩, hpass⟩
    have hpos : 0 < (midP X z).card := Finset.card_pos.mpr hnonempty
    omega

end CPNF
