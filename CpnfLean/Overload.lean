import Mathlib
import CpnfLean.ColumnTelescope
import CpnfLean.ColumnMarks
import CpnfLean.Coverage

/-!
# CPNF — Phase C: the local overlap certificate

The frontier dropped half-debt for a monotone object. At each node `I` with capacity `U`,
propagate a lower bound on overlap rather than a product of counts:

  `forced S T U t d j = max 0 (|S∩I| + |T∩I| − |U∩I|)`

`forced_le_children`: a positive lower bound can never be lost to a finer scale
(`L(I) ≤ L(I_L) + L(I_R)`) — nonnegative corrections, no weights, no sign juggling.

`common_of_forced_pos`: one overloaded node at any depth already forces a common mark.
No depth or index hypothesis is needed.

`boxed_of_cofinalNodeOverload`: a cofinal overload finishes the whole problem, straight
through `windowWitness_of_commonMarks`.

The interface `CofinalNodeOverload` is, by the frontier's own note, equivalent to unbounded
twins — so this is a sharp conditional finish, not a proof of the conjecture. Its advantage
over half-debt is that the certificate is *local and permanent*: prove it once at any scale
and it survives every refinement.

No `sorry`, no `axiom`.
-/

namespace CPNF


def forced (S T U : Finset ℕ) (t d j : ℕ) : ℤ :=
  max 0 (colCount S t d j + colCount T t d j - colCount U t d j)

theorem forced_le_children (S T U : Finset ℕ) (t d j : ℕ) (hd : d < t) :
    forced S T U t d j ≤
      forced S T U t (d+1) (2*j) + forced S T U t (d+1) (2*j+1) := by
  unfold forced
  rw [colCount_split S t d j hd, colCount_split T t d j hd,
      colCount_split U t d j hd]
  omega

/-- A strictly overloaded node already forces a common mark. -/
theorem common_of_forced_pos {S T U : Finset ℕ} {t d j : ℕ}
    (hS : S ⊆ U) (hT : T ⊆ U) (h : 0 < forced S T U t d j) :
    (S ∩ T).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hdisj : Disjoint (S ∩ node t d j) (T ∩ node t d j) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1⟩
    rw [hempty] at this
    simp at this
  have hunion : (S ∩ node t d j) ∪ (T ∩ node t d j) ⊆ U ∩ node t d j := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_inter.mpr ⟨hS (Finset.mem_inter.mp h).1, (Finset.mem_inter.mp h).2⟩
    · exact Finset.mem_inter.mpr ⟨hT (Finset.mem_inter.mp h).1, (Finset.mem_inter.mp h).2⟩
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  unfold forced colCount at h
  omega

def CofinalNodeOverload : Prop :=
  ∀ T₀ : ℕ, ∃ t d j : ℕ,
    T₀ ≤ t ∧ d ≤ t ∧ j < 2^d ∧
    0 < forced (loMarks (2^t)) (hiMarks (2^t)) (blk (2^t)) t d j

theorem boxed_of_cofinalNodeOverload (H : CofinalNodeOverload) :
    ∀ K : ℕ, WindowWitness K := by
  intro K
  obtain ⟨t, d, j, hKt, hdt, hj, hpos⟩ := H (max K 16)
  have hKK : K ≤ 2^t := by
    have h1 : K ≤ max K 16 := le_max_left _ _
    have h2 : max K 16 ≤ 2^t := by
      have : max K 16 ≤ t := hKt
      have : t ≤ 2^t := Nat.lt_two_pow_self.le
      omega
    omega
  have h16 : 16 ≤ 2^t := by
    have h1 : 16 ≤ max K 16 := le_max_right _ _
    have : max K 16 ≤ t := hKt
    have : t ≤ 2^t := Nat.lt_two_pow_self.le
    omega
  apply windowWitness_of_commonMarks hKK h16
  apply common_of_forced_pos (t := t) (d := d) (j := j)
  · intro x hx; exact Finset.mem_filter.mp hx |>.1
  · intro x hx; exact Finset.mem_filter.mp hx |>.1
  · exact hpos

end CPNF
