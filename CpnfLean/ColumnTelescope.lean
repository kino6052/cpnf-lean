import Mathlib
import CpnfLean.ColumnSplit

/-!
# CPNF — Phase A: the multiscale column identity

The frontier's plan, Phase A delivered and proved. Iterating the two-column split over the
binary decomposition of the block `(N, 2N]` (`N = 2^t`) gives the exact telescope

  `levelSum 0 = 2^t · levelSum t − Σ_{d<t} 2^d · levelTermG d`

where `levelTermG` collects the signed node contrasts `(A_L − A_R)(B_L − B_R)` at depth `d`.
The deepest level's products are exactly the common-mark indicators, so this identifies the
common-mark count with the root product plus a signed correction — the object the frontier
proposed for Phase C.

Everything here is unconditional and proved for **two arbitrary subsets** `S T`, then
specialized: `column_split` at one node (`product_split`), `level_step` for one depth,
`telesc` for the recurrence, and `column_telescope` for the whole descent.

No `sorry`, no `axiom`.
-/

namespace CPNF


theorem node_split (t d j : ℕ) (hd : d < t) :
    node t d j = node t (d+1) (2*j) ∪ node t (d+1) (2*j+1) := by
  unfold node
  have hpow : 2 ^ (t - (d+1)) = 2^(t-d-1) := by
    rw [show t - (d+1) = t - d - 1 by omega]
  simp only [hpow]
  set N := 2^t
  set s := 2^(t-d)
  set s' := 2^(t-d-1)
  have hspos : 0 < s' := by unfold s'; exact Nat.two_pow_pos _
  have hs : s = 2 * s' := by
    unfold s s'
    rw [← pow_succ']
    congr 1
    omega
  have h1 : N + 2*j*s' = N + j*s := by rw [hs]; ring
  have h2 : N + (2*j+1)*s' = N + j*s + s' := by rw [hs]; ring
  have h3 : N + (2*j+1+1)*s' = N + (j+1)*s := by rw [hs]; ring
  rw [h1, h2, h3]
  ext x
  simp only [Finset.mem_union, Finset.mem_Ioc]
  constructor
  · rintro ⟨l, u⟩
    rcases le_or_gt x (N + j*s + s') with k | k
    · exact Or.inl ⟨l, k⟩
    · exact Or.inr ⟨k, u⟩
  · rintro (⟨l, k⟩ | ⟨k, u⟩)
    · refine ⟨l, ?_⟩
      have : (j + 1) * s = j * s + s := by ring
      rw [this]; omega
    · refine ⟨?_, u⟩
      have hj : j * s ≤ j * s + s' := Nat.le_add_right _ _
      omega

theorem node_disjoint (t d j : ℕ) :
    Disjoint (node t (d+1) (2*j)) (node t (d+1) (2*j+1)) := by
  unfold node
  rw [Finset.disjoint_left]
  intro x h1 h2
  simp only [Finset.mem_Ioc] at h1 h2
  have : 0 < 2^(t-(d+1)) := Nat.two_pow_pos _
  omega

theorem colCount_split (S : Finset ℕ) (t d j : ℕ) (hd : d < t) :
    colCount S t d j = colCount S t (d+1) (2*j) + colCount S t (d+1) (2*j+1) := by
  unfold colCount
  rw [node_split t d j hd, Finset.inter_union_distrib_left]
  rw [Finset.card_union_of_disjoint]
  · push_cast; ring
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
            (Finset.disjoint_of_subset_right Finset.inter_subset_right (node_disjoint t d j))

def levelSum (S T : Finset ℕ) (t d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2^d), colCount S t d j * colCount T t d j

def levelTermG (S T : Finset ℕ) (t d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2^d), contrast S t d j * contrast T t d j

theorem product_split (S T : Finset ℕ) (t d j : ℕ) (hd : d < t) :
    colCount S t d j * colCount T t d j =
      2 * (colCount S t (d+1) (2*j) * colCount T t (d+1) (2*j)
           + colCount S t (d+1) (2*j+1) * colCount T t (d+1) (2*j+1))
      - contrast S t d j * contrast T t d j := by
  rw [colCount_split S t d j hd, colCount_split T t d j hd]
  unfold contrast
  ring_nf

/-- Reindex a sum over `range (2^(d+1))` as pairs `(2j, 2j+1)`. -/
theorem sum_range_two (d : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2^(d+1)), f i =
      ∑ j ∈ Finset.range (2^d), (f (2*j) + f (2*j+1)) := by
  rw [show 2^(d+1) = 2^d * 2 by rw [pow_succ]]
  induction (2^d) with
  | zero => simp
  | succ n ih =>
    have hn : (n + 1) * 2 = n * 2 + 2 := by ring
    rw [hn, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
    ring_nf

/-- Reindex a sum over `range (2^(d+1))` as pairs `(2j, 2j+1)`. -/
theorem level_step (S T : Finset ℕ) (t d : ℕ) (hd : d < t) :
    levelSum S T t d =
      2 * levelSum S T t (d+1) - levelTermG S T t d := by
  unfold levelSum levelTermG
  simp only [Finset.mul_sum]
  rw [sum_range_two d (fun i => 2 * (colCount S t (d+1) i * colCount T t (d+1) i))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have := product_split S T t d j hd
  linarith

theorem telesc (Ls E : ℕ → ℤ) (T : ℕ)
    (h : ∀ d, d < T → Ls d = 2 * Ls (d+1) - E d) :
    Ls 0 = 2^T * Ls T - ∑ d ∈ Finset.range T, 2^d * E d := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hT : ∀ d, d < T → Ls d = 2 * Ls (d+1) - E d := fun d hd => h d (by omega)
    have hih := ih hT
    have hlast : Ls T = 2 * Ls (T+1) - E T := h T (by omega)
    calc Ls 0 = 2^T * Ls T - ∑ d ∈ Finset.range T, 2^d * E d := hih
      _ = 2^T * (2 * Ls (T+1) - E T) - ∑ d ∈ Finset.range T, 2^d * E d := by rw [hlast]
      _ = 2^(T+1) * Ls (T+1) - ((∑ d ∈ Finset.range T, 2^d * E d) + 2^T * E T) := by
          rw [show (2:ℤ)^(T+1) = 2^T * 2 by rw [pow_succ]]; ring
      _ = 2^(T+1) * Ls (T+1) - ∑ d ∈ Finset.range (T+1), 2^d * E d := by
          rw [Finset.sum_range_succ]

/-- **Phase A**: the multiscale identity, from level `0` down to level `t`. -/
theorem column_telescope (S T : Finset ℕ) (t : ℕ) :
    levelSum S T t 0 =
      2^t * levelSum S T t t - ∑ d ∈ Finset.range t, (2:ℤ)^d * levelTermG S T t d :=
  telesc (fun d => levelSum S T t d) (fun d => levelTermG S T t d) t
    (fun d hd => level_step S T t d hd)

end CPNF
