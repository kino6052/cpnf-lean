**Idea.** Raise the budget exponent from \(1/5\) to \(1/7\) without selecting another single residue class. A fifth power must pass a fifth-power residue test modulo **both** 11 and 31, on the **same** side of the pair. Discard a row only if one side passes both tests. Modulo \(341=11\cdot31\), at least 299 of the 341 index classes survive; since \(14\) is coprime to \(341\), this retains at least \(299/341\) of the old thin progression in each full period. On retained rows the old lemmas exclude exponents 2 through 4, the new test excludes 5, and the square obstruction excludes 6. The existing base injection then gives a seventh-root budget. The retention bound is for **candidate rows**, not signal rows; I do not have the cofinal signal lower bound.

Here is a proposed `CpnfLean/SeventhMask.lean`. I have not run Lean here. The first two lemmas are independent checks worth compiling first: one certifies the size of the mask, and the other certifies that the mask cannot discard a fifth-power obstruction by mistake (i.e., no fifth power can occur on a **retained** row).

```lean
import CpnfLean.ThinInjection

namespace CPNF

/-- A small table, constructed rather than postulated. -/
def fifthTable (q : ℕ) : Finset ℕ :=
  (Finset.range q).image (fun a : ℕ => a^5 % q)

/-- The same integer must pass both tests. -/
def maybeFifth (m : ℕ) : Bool :=
  decide (m % 11 ∈ fifthTable 11 ∧ m % 31 ∈ fifthTable 31)

/-- At residue r use 6*r+340 for the lower side:
    it represents 6*r-1 even at r=0. -/
def seventhMask : Finset ℕ :=
  (Finset.range 341).filter (fun r =>
    maybeFifth (6*r + 340) = false ∧
    maybeFifth (6*r + 1) = false)

-- First lemma: a certificate about the whole mask, not a sample of rows.
theorem seventhMask_size : 299 ≤ seventhMask.card := by
  decide

private theorem fifth_mem_table (a q : ℕ) (hq : 0 < q) :
    a^5 % q ∈ fifthTable q := by
  apply Finset.mem_image.mpr
  exact ⟨a % q, Finset.mem_range.mpr (Nat.mod_lt _ hq),
    (Nat.pow_mod a 5 q).symm⟩

private theorem maybeFifth_of_residues {a m : ℕ}
    (h11 : a^5 % 11 = m % 11) (h31 : a^5 % 31 = m % 31) :
    maybeFifth m = true := by
  have u := fifth_mem_table a 11 (by decide)
  have v := fifth_mem_table a 31 (by decide)
  rw [h11] at u
  rw [h31] at v
  simp [maybeFifth, u, v]

-- Second lemma: the periodic table is sound on unbounded natural inputs.
theorem seventhMask_no_fifth {n : ℕ} (hn : 1 ≤ n)
    (hr : n % 341 ∈ seventhMask) (a : ℕ) :
    a^5 ≠ twinLo n ∧ a^5 ≠ twinHi n := by
  obtain ⟨hl, hu⟩ := (Finset.mem_filter.mp hr).2
  constructor
  · intro he
    have h := maybeFifth_of_residues (a := a) (m := 6*(n%341)+340)
      (by rw [he, twinLo]; omega) (by rw [he, twinLo]; omega)
    simp_all
  · intro he
    have h := maybeFifth_of_residues (a := a) (m := 6*(n%341)+1)
      (by rw [he, twinHi]; omega) (by rw [he, twinHi]; omega)
    simp_all

def seventhSignal (X : ℕ) : Finset ℕ :=
  (thinSignal X).filter (fun n => n % 341 ∈ seventhMask)

def seventhBad (X : ℕ) : Finset ℕ :=
  (thinBad X).filter (fun n => n % 341 ∈ seventhMask)

theorem seventh_exp {n p e : ℕ} (ht : n % 14 = 11)
    (hr : n % 341 ∈ seventhMask) (he : 2 ≤ e)
    (hm : p^e = twinLo n ∨ p^e = twinHi n) : 7 ≤ e := by
  have h5 := thin_exponent_ge_five ht he hm
  have nf := seventhMask_no_fifth (n := n) (by omega) hr p
  have ns := thin_no_square ht (p^3)
  rw [show (p^3)^2 = p^6 by ring] at ns
  by_contra! h
  interval_cases e <;> tauto

theorem seventhBad_le_baseBudget {X B : ℕ} (hB : 12*X+1 < B^7) :
    (seventhBad X).card ≤ (baseBudget B).card := by
  apply Finset.card_le_card_of_injOn thinBase
  · intro n hn
    change n ∈ seventhBad X at hn
    obtain ⟨hb, hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨m, h, side, eqb⟩ := thinBase_spec hb
    have hs : n ∈ thinSignal X := (Finset.mem_filter.mp hb).1
    have ht : n ∈ thinBlock X := (Finset.mem_filter.mp hs).1
    have hp := hppBase_prime h
    have he : 7 ≤ hppExp h :=
      seventh_exp (Finset.mem_filter.mp ht).2 hr (hppExp_ge_two h)
        (p := hppBase h) (by rw [hppBase_pow h]; exact side)
    have hu := (thinBlock_bounds ht).2
    have horder : twinLo n ≤ twinHi n := by unfold twinLo twinHi; omega
    have hm : m ≤ 12*X+1 := by rcases side with h' | h' <;> omega
    have hlt : (hppBase h)^7 < B^7 := calc
      (hppBase h)^7 ≤ (hppBase h)^(hppExp h) :=
        Nat.pow_le_pow_right hp.pos he
      _ = m := hppBase_pow h
      _ < B^7 := hm.trans_lt hB
    rw [eqb]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Nat.pow_lt_pow_iff_left (by decide : 7 ≠ 0)).mp hlt), hp⟩
  · intro i hi j hj hij
    change i ∈ seventhBad X at hi
    change j ∈ seventhBad X at hj
    have bi : i ∈ thinBad X := (Finset.mem_filter.mp hi).1
    have bj : j ∈ thinBad X := (Finset.mem_filter.mp hj).1
    have si : i ∈ thinSignal X := (Finset.mem_filter.mp bi).1
    have sj : j ∈ thinSignal X := (Finset.mem_filter.mp bj).1
    obtain ⟨mi, ci, di, ei⟩ := thinBase_spec bi
    obtain ⟨mj, cj, dj, ej⟩ := thinBase_spec bj
    by_contra hne
    exact base_inj hne (Finset.mem_filter.mp si).1
      (Finset.mem_filter.mp sj).1 di dj ci cj
      (ei.symm.trans (hij.trans ej))

theorem boxed_of_seventh_signal {K X B : ℕ} (hK : K ≤ X)
    (hB : 12*X+1 < B^7)
    (hs : (baseBudget B).card < (seventhSignal X).card) :
    WindowWitness K := by
  have gap := lt_of_le_of_lt (seventhBad_le_baseBudget hB) hs
  by_contra hw
  apply (not_lt_of_ge (Finset.card_le_card
    (show seventhSignal X ⊆ seventhBad X from by
      intro n hn
      obtain ⟨hsig, hr⟩ := Finset.mem_filter.mp hn
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hsig, ?_⟩, hr⟩
      by_contra hc
      have pair := (Finset.mem_filter.mp hsig).2
      have ht : n ∈ thinBlock X := (Finset.mem_filter.mp hsig).1
      have hb : n ∈ blk X := (Finset.mem_filter.mp ht).1
      have hXn := (Finset.mem_Ioc.mp hb).1
      have hn1 : 1 ≤ n := by omega
      obtain ⟨y, hy, hwin, hscore⟩ := window_witness_of_twin hn1
        (pair.1.resolve_right (fun h => hc (Or.inl h)))
        (pair.2.resolve_right (fun h => hc (Or.inr h)))
      exact hw ⟨y, n, hy, hn1, by omega, hwin, hscore⟩))) gap

end CPNF
```

**Where the new step enters.** It is the order of the modular tests: *intersect the possible obstructions before removing any rows*. For one side, only \(3\cdot7=21\) of the 341 residue pairs can pass both fifth-power tests, since the fifth-power images, including zero, have sizes 3 and 7. Removing both sides costs at most 42 classes. In particular a lower-side hit modulo 11 and an upper-side hit modulo 31 do **not** justify removing the row. This gives a reusable design rule: another coprime test for the *same exponent* can only **enlarge** the retained mask while preserving the exponent bound.

The remaining target for this branch is precisely
\[
\forall K,\ \exists X,B,\quad K\le X,\quad 12X+1<B^7,\quad
|\mathrm{baseBudget}(B)|<|\mathrm{seventhSignal}(X)|.
\]
This is a sufficient condition, not a known consequence of the \(299/341\) bound or of RH. The gain is a smaller comparison threshold with an explicit bound on the price paid in candidate classes.
