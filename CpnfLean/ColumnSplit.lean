import Mathlib
import CpnfLean.Ladder

/-!
# CPNF — the column split: a multiscale identity for common marks

The frontier's plan for the finish. On the block `(N, 2N]` with `N = 2^t`, mark two
**single-member** columns: `loMarks N` (where `N < (6n-1).minFac`) and `hiMarks N`
(where `N < (6n+1).minFac`). Each mark is exactly a prime, since both members lie in
`(N, N^2]`. A common mark is already inside `window N`.

`windowWitness_of_commonMarks` is the end of the proof written first: a nonempty
intersection forces `WindowWitness K`, with no proper-power budget at all.

`column_split` is the exact two-column identity at one node. Iterating it gives the
multiscale telescope, which is the Phase A deliverable.
-/

namespace CPNF


def loMarks (N : ℕ) : Finset ℕ :=
  (blk N).filter (fun n => N < (twinLo n).minFac)

def hiMarks (N : ℕ) : Finset ℕ :=
  (blk N).filter (fun n => N < (twinHi n).minFac)

theorem commonMarks_eq (N : ℕ) :
    loMarks N ∩ hiMarks N =
      (blk N).filter (fun n => N < score n) := by
  ext n
  simp only [loMarks, hiMarks, Finset.mem_inter, Finset.mem_filter,
    score, lt_min_iff]
  tauto

theorem windowWitness_of_commonMarks {K N : ℕ}
    (hK : K ≤ N) (hN : 16 ≤ N)
    (hm : (loMarks N ∩ hiMarks N).Nonempty) :
    WindowWitness K := by
  obtain ⟨n, hn⟩ := hm
  rw [commonMarks_eq] at hn
  obtain ⟨hb, hs⟩ := Finset.mem_filter.mp hn
  obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp
    (show n ∈ Finset.Ioc N (2 * N) from hb)
  have hsq : 16 * N ≤ N * N := Nat.mul_le_mul_right N hN
  have hw : n ≤ window N := by
    apply (le_window_iff (by omega : 1 ≤ N)).mpr
    omega
  exact ⟨N, n, by omega, by omega, by omega, hw, hs⟩

theorem column_split (aL aR bL bR : ℤ) :
    2 * (aL * bL + aR * bR) =
      (aL + aR) * (bL + bR) + (aL - aR) * (bL - bR) := by
  ring



def node (t d j : ℕ) : Finset ℕ :=
  let N := 2^t
  let s := 2^(t-d)
  Finset.Ioc (N + j*s) (N + (j+1)*s)

def colCount (S : Finset ℕ) (t d j : ℕ) : ℤ :=
  ((S ∩ node t d j).card : ℤ)

def contrast (S : Finset ℕ) (t d j : ℕ) : ℤ :=
  colCount S t (d+1) (2*j) - colCount S t (d+1) (2*j+1)

def levelTerm (t d : ℕ) : ℤ :=
  (2 : ℤ)^d * ∑ j ∈ Finset.range (2^d),
    contrast (loMarks (2^t)) t d j *
    contrast (hiMarks (2^t)) t d j

def rootProduct (t : ℕ) : ℤ :=
  ((loMarks (2^t)).card : ℤ) * ((hiMarks (2^t)).card : ℤ)

def levelDebt (t : ℕ) : ℤ :=
  ∑ d ∈ Finset.range t, max 0 (-levelTerm t d)


end CPNF
