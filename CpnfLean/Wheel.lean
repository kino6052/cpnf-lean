import Mathlib
import CpnfLean.Overload

/-!
# CPNF — the wheel: free capacity, proved

The frontier's concrete search direction, made unconditional. A row is *killed* when it
fails **both** columns by small-prime divisor certificates:

  `wheelKilled n := (5 ∣ 6n−1 ∧ 7 ∣ 6n+1) ∨ (7 ∣ 6n−1 ∧ 5 ∣ 6n+1)`

Exactly two classes modulo 35 satisfy this: `n ≡ 1` and `n ≡ 34`. So every 35-row stretch
loses two units of capacity, at no cost to the marks.

`loMarks_subset_wheelCap` and `hiMarks_subset_wheelCap`: the wheel never throws away a row
that carries a mark — so `forced` applies with `U = wheelCap N` unchanged.

This is the provable half. The unproved half remains the frontier's: whether the two prime
counts strictly exceed this reduced capacity on cofinally many nodes. The saving itself must
not be extrapolated into a twin lower bound.

No `sorry`, no `axiom`.
-/

namespace CPNF


def wheelKilled (n : ℕ) : Prop :=
  (5 ∣ twinLo n ∧ 7 ∣ twinHi n) ∨ (7 ∣ twinLo n ∧ 5 ∣ twinHi n)

instance (n : ℕ) : Decidable (wheelKilled n) := by
  unfold wheelKilled; infer_instance

def wheelCap (N : ℕ) : Finset ℕ := (blk N).filter (fun n => ¬ wheelKilled n)

theorem no_loMark_of_five {N n : ℕ} (h16 : 16 ≤ N)
    (hN : n ∈ loMarks N) (h5 : 5 ∣ twinLo n) : False := by
  unfold loMarks at hN
  obtain ⟨-, hNlt⟩ := Finset.mem_filter.mp hN
  have hmin : (twinLo n).minFac ≤ 5 := Nat.minFac_le_of_dvd (by norm_num) h5
  omega

theorem no_loMark_of_seven_lo {N n : ℕ} (h16 : 16 ≤ N)
    (hN : n ∈ loMarks N) (h7 : 7 ∣ twinLo n) : False := by
  unfold loMarks at hN
  obtain ⟨-, hNlt⟩ := Finset.mem_filter.mp hN
  have hmin : (twinLo n).minFac ≤ 7 := Nat.minFac_le_of_dvd (by norm_num) h7
  omega

theorem no_hiMark_of_five_hi {N n : ℕ} (h16 : 16 ≤ N)
    (hN : n ∈ hiMarks N) (h5 : 5 ∣ twinHi n) : False := by
  unfold hiMarks at hN
  obtain ⟨-, hNlt⟩ := Finset.mem_filter.mp hN
  have hmin : (twinHi n).minFac ≤ 5 := Nat.minFac_le_of_dvd (by norm_num) h5
  omega

theorem no_hiMark_of_seven {N n : ℕ} (h16 : 16 ≤ N)
    (hN : n ∈ hiMarks N) (h7 : 7 ∣ twinHi n) : False := by
  unfold hiMarks at hN
  obtain ⟨-, hNlt⟩ := Finset.mem_filter.mp hN
  have hmin : (twinHi n).minFac ≤ 7 := Nat.minFac_le_of_dvd (by norm_num) h7
  omega

/-- Every marked row survives the wheel: marks are in the block, and a row that carries a mark
cannot be killed by the wheel's divisor certificates. -/
theorem loMarks_subset_wheelCap {N : ℕ} (h16 : 16 ≤ N) :
    loMarks N ⊆ wheelCap N := by
  intro n hn
  unfold wheelCap
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold loMarks at hn
    exact Finset.mem_filter.mp hn |>.1
  · intro hk
    rcases hk with ⟨h5, -⟩ | ⟨h7, -⟩
    · exact no_loMark_of_five h16 hn h5
    · exact no_loMark_of_seven_lo h16 hn h7

theorem hiMarks_subset_wheelCap {N : ℕ} (h16 : 16 ≤ N) :
    hiMarks N ⊆ wheelCap N := by
  intro n hn
  unfold wheelCap
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold hiMarks at hn
    exact Finset.mem_filter.mp hn |>.1
  · intro hk
    rcases hk with ⟨_, h7⟩ | ⟨_, h5⟩
    · exact no_hiMark_of_seven h16 hn h7
    · exact no_hiMark_of_five_hi h16 hn h5

theorem five_dvd_lo_of_mod {n : ℕ} (h : n % 35 = 1) : 5 ∣ twinLo n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 35*k + 1 := ⟨n / 35, by omega⟩
  unfold twinLo
  rw [hk]
  have e : 6*(35*k+1) - 1 = 210*k + 5 := by omega
  rw [e]
  exact ⟨42*k + 1, by ring⟩

theorem seven_dvd_hi_of_mod {n : ℕ} (h : n % 35 = 1) : 7 ∣ twinHi n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 35*k + 1 := ⟨n / 35, by omega⟩
  unfold twinHi
  rw [hk]
  have e : 6*(35*k+1) + 1 = 210*k + 7 := by omega
  rw [e]
  exact ⟨30*k + 1, by ring⟩

theorem wheelKilled_of_mod_one {n : ℕ} (h : n % 35 = 1) : wheelKilled n :=
  Or.inl ⟨five_dvd_lo_of_mod h, seven_dvd_hi_of_mod h⟩

theorem seven_dvd_lo_of_mod {n : ℕ} (h : n % 35 = 34) : 7 ∣ twinLo n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 35*k + 34 := ⟨n / 35, by omega⟩
  unfold twinLo
  rw [hk]
  have e : 6*(35*k+34) - 1 = 210*k + 203 := by omega
  rw [e]
  exact ⟨30*k + 29, by ring⟩

theorem five_dvd_hi_of_mod {n : ℕ} (h : n % 35 = 34) : 5 ∣ twinHi n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 35*k + 34 := ⟨n / 35, by omega⟩
  unfold twinHi
  rw [hk]
  have e : 6*(35*k+34) + 1 = 210*k + 205 := by omega
  rw [e]
  exact ⟨42*k + 41, by ring⟩

theorem wheelKilled_of_mod_thirtyfour {n : ℕ} (h : n % 35 = 34) : wheelKilled n :=
  Or.inr ⟨seven_dvd_lo_of_mod h, five_dvd_hi_of_mod h⟩

end CPNF
