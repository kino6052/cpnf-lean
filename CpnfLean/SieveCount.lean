import Mathlib
import CpnfLean.Sieve
import CpnfLean.ObstructionStructure
open CPNF

/-!
# CPNF — the sieve count behind the scale obstruction

The last unproved piece of `Obstruction.lean`: a column of marks, whose rows avoid all nine
primes `{5,7,11,13,17,19,23,29,31}`, is at most a density `ρ` of its rows plus a bounded error.

**The discrepancy theorem.** For any finite set `P` of primes and any interval `(u,v]`,

  `| live(P) − ρ(P)·(v−u) | ≤ 2^|P| − 1`,   `ρ(P) = ∏ (1 − 1/p)`.

This is inclusion–exclusion in recursive form: inserting a prime `p` splits the survivors into
those avoiding `p` and those equal to `p` times a survivor on the shrunk interval `(u/p, v/p]`.
The rounding error is **two-sided** (`div_width_err`), so each insertion costs exactly one unit,
and nine primes cost `2^9 − 1 = 511`.

**The shift.** A mark's condition is `¬ p ∣ 6n ± 1`, not `¬ p ∣ n`. Shifting the column by
`loShift` (resp. `hiShift`) turns the first into the second, because `6·loShift + 1 = 5·∏p` and
`6·hiShift − 1 = ∏p` are divisible by every one of the nine primes. So the bound applies to
the actual marks, and the inclusion–exclusion counting is not merely legitimate — it is exactly
what the marks satisfy.

No `sorry`, no `axiom`.
-/

namespace CPNF

-- ============ the inclusion-exclusion bound ============

def sieveRho (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P, (1 - 1 / (p : ℚ))

/-- The rows of `(u, v]` that survive the blockers `P` — the paper's sieve on a column. -/
def liveIoc (P : Finset ℕ) (u v : ℕ) : Finset ℕ :=
  (Finset.Ioc u v).filter (Survives P)

@[simp] lemma mem_liveIoc {P : Finset ℕ} {u v n : ℕ} :
    n ∈ liveIoc P u v ↔ (u < n ∧ n ≤ v) ∧ Survives P n := by
  simp [liveIoc, Finset.mem_Ioc, Survives]

lemma factor_nonneg (p : ℕ) (hp : 1 ≤ p) : 0 ≤ (1:ℚ) - 1/(p:ℚ) := by
  have hpos : (0:ℚ) < p := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hp)
  have hd : 1/(p:ℚ) ≤ 1 := by
    rw [div_le_iff₀ hpos]
    have hp' : (1:ℚ) ≤ p := by exact_mod_cast hp
    linarith
  linarith

lemma factor_le_one (p : ℕ) (hp : 1 ≤ p) : (1:ℚ) - 1/(p:ℚ) ≤ 1 := by
  have hpos : (0:ℚ) < p := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hp)
  have : (0:ℚ) ≤ 1/(p:ℚ) := by positivity
  linarith

lemma sieveRho_nonneg (P : Finset ℕ) (hp : ∀ p ∈ P, 1 ≤ p) : 0 ≤ sieveRho P := by
  unfold sieveRho
  induction P using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
      rw [Finset.prod_insert hps]
      exact mul_nonneg (factor_nonneg p (hp p (Finset.mem_insert_self p s)))
        (ih (fun q hq => hp q (Finset.mem_insert_of_mem hq)))

lemma sieveRho_le_one (P : Finset ℕ) (hp : ∀ p ∈ P, 1 ≤ p) : sieveRho P ≤ 1 := by
  unfold sieveRho
  induction P using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
      rw [Finset.prod_insert hps]
      have ha : (1:ℚ) - 1/(p:ℚ) ≤ 1 := factor_le_one p (hp p (Finset.mem_insert_self p s))
      have hb : (∏ x ∈ s, (1 - 1/(x:ℚ))) ≤ 1 := ih (fun q hq => hp q (Finset.mem_insert_of_mem hq))
      have h0a : 0 ≤ (1:ℚ) - 1/(p:ℚ) := factor_nonneg p (hp p (Finset.mem_insert_self p s))
      have h0b : 0 ≤ (∏ x ∈ s, (1 - 1/(x:ℚ))) := by
        have hh := sieveRho_nonneg s (fun q hq => hp q (Finset.mem_insert_of_mem hq))
        simpa [sieveRho] using hh
      nlinarith

lemma sieveRho_insert {p : ℕ} {P : Finset ℕ} (hpP : p ∉ P) :
    sieveRho (insert p P) = (1 - 1/(p:ℚ)) * sieveRho P := by
  simp only [sieveRho, Finset.prod_insert hpP]

lemma liveIoc_byp_card {p : ℕ} {P : Finset ℕ}
    (hp : Nat.Prime p) (hpP : p ∉ P)
    (hP : ∀ q ∈ P, Nat.Prime q) (u v : ℕ) :
    ((liveIoc P u v).filter (fun n => p ∣ n)).card =
      (liveIoc P (u / p) (v / p)).card := by
  have transport (k q : ℕ) (hq : q ∈ P) : q ∣ k * p ↔ q ∣ k := by
    constructor
    · intro hd
      apply ((hP q hq).dvd_mul.mp hd).resolve_right
      intro hqp
      rcases hp.eq_one_or_self_of_dvd q hqp with h1 | he
      · exact (hP q hq).ne_one h1
      · exact hpP (he ▸ hq)
    · intro hd; exact hd.trans (dvd_mul_right k p)
  have mem_mul (k : ℕ) :
      k * p ∈ liveIoc P u v ↔ k ∈ liveIoc P (u / p) (v / p) := by
    simp only [liveIoc, Finset.mem_filter, Finset.mem_Ioc, Survives,
      lt_iff_not_ge, Nat.le_div_iff_mul_le hp.pos]
    constructor
    · rintro ⟨hi, hs⟩
      exact ⟨hi, fun q hq hd => hs q hq ((transport k q hq).mpr hd)⟩
    · rintro ⟨hi, hs⟩
      exact ⟨hi, fun q hq hd => hs q hq ((transport k q hq).mp hd)⟩
  symm
  apply Finset.card_bij (fun k _ => k * p)
  · intro k hk
    exact Finset.mem_filter.mpr ⟨(mem_mul k).mpr hk, dvd_mul_left p k⟩
  · intro a ha b hb he
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    simpa only [Nat.mul_comm p] using (show a * p = b * p from he)
  · intro n hn
    obtain ⟨hnLive, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨k, hk⟩ := hd
    have he : k * p = n := (Nat.mul_comm k p).trans hk.symm
    exact ⟨k, (mem_mul k).mp (he.symm ▸ hnLive), he⟩

lemma liveIoc_insert_card {p : ℕ} {P : Finset ℕ}
    (hp : Nat.Prime p) (hpP : p ∉ P) (hP : ∀ q ∈ P, Nat.Prime q) (u v : ℕ) :
    (liveIoc (insert p P) u v).card + (liveIoc P (u/p) (v/p)).card =
      (liveIoc P u v).card := by
  set S := liveIoc P u v with hS
  have hnotpeq : S.filter (fun n => ¬ p ∣ n) = liveIoc (insert p P) u v := by
    ext n
    rw [Finset.mem_filter, hS, mem_liveIoc, mem_liveIoc]
    simp only [Survives, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hI, hAll⟩, hnp⟩
      refine ⟨hI, ?_⟩
      intro q hq
      rcases hq with rfl | hqP
      · exact hnp
      · exact hAll q hqP
    · rintro ⟨hI, hall⟩
      exact ⟨⟨hI, fun q hq => hall q (Or.inr hq)⟩, hall p (Or.inl rfl)⟩
  have hpart : S.filter (fun n => ¬ p ∣ n) ∪ S.filter (fun n => p ∣ n) = S := by
    ext n; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hn
      by_cases hpd : p ∣ n
      · exact Or.inr ⟨hn, hpd⟩
      · exact Or.inl ⟨hn, hpd⟩
  have hdisj : Disjoint (S.filter (fun n => ¬ p ∣ n)) (S.filter (fun n => p ∣ n)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hsplit : (S.filter (fun n => ¬ p ∣ n)).card + (S.filter (fun n => p ∣ n)).card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hpart]
  have hbyp := liveIoc_byp_card hp hpP hP u v
  rw [← hnotpeq, ← hbyp]
  omega

private lemma div_width_err (u v p : ℕ) (hp : 0 < p) :
    |((v : ℚ) - (u : ℚ)) / (p : ℚ) -
      ((↑(v / p) : ℚ) - (↑(u / p) : ℚ))| ≤ 1 := by
  have decomp (w : ℕ) :
      (p : ℚ) * (↑(w / p) : ℚ) + (↑(w % p) : ℚ) = (w : ℚ) := by
    exact_mod_cast Nat.div_add_mod w p
  have small (w : ℕ) : (↑(w % p) : ℚ) < (p : ℚ) := by
    exact_mod_cast Nat.mod_lt w hp
  have pos : (0 : ℚ) < p := by exact_mod_cast hp
  have eqn :
      ((v : ℚ) - (u : ℚ)) / p -
        ((↑(v / p) : ℚ) - (↑(u / p) : ℚ)) =
      ((↑(v % p) : ℚ) - (↑(u % p) : ℚ)) / p := by
    field_simp [ne_of_gt pos]
    nlinarith only [decomp v, decomp u]
  rw [eqn, abs_le]
  constructor
  · apply (le_div_iff₀ pos).2
    linarith [small u, (show (0 : ℚ) ≤ ↑(v % p) by positivity)]
  · apply (div_le_iff₀ pos).2
    linarith [small v, (show (0 : ℚ) ≤ ↑(u % p) by positivity)]

private lemma err_step {e e' r z B : ℚ}
    (he : |e| ≤ B) (he' : |e'| ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hz : |z| ≤ 1) :
    |e - e' + r*z| ≤ 2*B + 1 := by
  have hm : |r*z| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hr0]
    calc
      r * |z| ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr0
      _ ≤ 1 := by simpa using hr1
  rw [abs_le] at he he' hm ⊢
  constructor <;> linarith [he.1, he.2, he'.1, he'.2, hm.1, hm.2]

theorem sieve_discrepancy (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) :
    ∀ u v : ℕ, u ≤ v →
    |((liveIoc P u v).card : ℚ) - sieveRho P * ((v : ℚ) - (u : ℚ))|
      ≤ (2 : ℚ)^P.card - 1 := by
  induction P using Finset.induction_on with
  | empty =>
      intro u v huv
      have hcard : liveIoc ∅ u v = Finset.Ioc u v := by
        ext n; simp [liveIoc, Survives]
      rw [hcard, Nat.card_Ioc, Nat.cast_sub huv]
      simp [sieveRho]
  | insert p P hp_notin ih =>
      intro u v huv
      have hp : Nat.Prime p := hprime p (Finset.mem_insert_self p P)
      have hP : ∀ q ∈ P, Nat.Prime q :=
        fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      have hcount := liveIoc_insert_card hp hp_notin hP u v
      have ih1 := ih hP u v huv
      have hup : (u/p : ℕ) ≤ (v/p) := Nat.div_le_div_right huv
      have ih2 := ih hP (u/p) (v/p) hup
      have hrho := sieveRho_insert hp_notin
      let r : ℚ := sieveRho P
      let U : ℚ := (v:ℚ) - (u:ℚ)
      let W : ℚ := ((v/p:ℕ):ℚ) - ((u/p:ℕ):ℚ)
      let z : ℚ := U / (p:ℚ) - W
      let c1 : ℚ := ((liveIoc (insert p P) u v).card : ℚ)
      let c2 : ℚ := ((liveIoc P (u/p) (v/p)).card : ℚ)
      let c3 : ℚ := ((liveIoc P u v).card : ℚ)
      let B : ℚ := (2:ℚ)^P.card - 1
      have hsum : c1 + c2 = c3 := by
        dsimp [c1, c2, c3]; exact_mod_cast hcount
      have hr0 : 0 ≤ r := sieveRho_nonneg P (fun q hq => (hP q hq).one_le)
      have hr1 : r ≤ 1 := sieveRho_le_one P (fun q hq => (hP q hq).one_le)
      have hz1 : |z| ≤ 1 := by
        dsimp [z]; exact div_width_err u v p hp.pos
      have hid : c1 - sieveRho (insert p P) * U = (c3 - r * U) - (c2 - r * W) + r * z := by
        have hsum' : c3 = c1 + c2 := hsum.symm
        rw [hrho, hsum']
        dsimp [r, z]
        ring
      have herr := err_step ih1 ih2 hr0 hr1 hz1
      have hmain : |c1 - sieveRho (insert p P) * U| ≤ 2*B + 1 := by
        rw [hid]
        exact herr
      have hcard' : (insert p P).card = P.card + 1 := by
        rw [Finset.card_insert_of_notMem hp_notin]
      have hpow : (2:ℚ)^(P.card + 1) - 1 = 2*B + 1 := by
        dsimp [B]
        rw [pow_succ]
        ring
      have hfinal : |((liveIoc (insert p P) u v).card : ℚ) -
          sieveRho (insert p P) * ((v:ℚ) - (u:ℚ))| ≤ 2*B + 1 := by
        simpa [c1, U] using hmain
      rw [hcard', hpow]
      exact hfinal

-- shift infrastructure (from the frontier, compiled)
def nineProd : ℕ := 33426748355
def loShift : ℕ := 27855623629
def hiShift : ℕ := 5571124726

private theorem shift_sub_dvd {n p s c : ℕ}
    (h : p ∣ n + s) (hc : p ∣ c) :
    p ∣ (6 * n + 6 * s) - c := by
  have hm : p ∣ 6 * (n + s) := dvd_mul_of_dvd_right h 6
  rw [Nat.mul_add] at hm
  exact Nat.dvd_sub hm hc

private theorem lo_shift_aux {n p s : ℕ}
    (h : p ∣ n + s) (hc : p ∣ 6 * s + 1) : p ∣ twinLo n := by
  have he : (6 * n + 6 * s) - (6 * s + 1) = twinLo n := by
    unfold twinLo; omega
  exact he ▸ shift_sub_dvd h hc

private theorem hi_shift_aux {n p s : ℕ}
    (hs : 0 < s) (h : p ∣ n + s) (hc : p ∣ 6 * s - 1) : p ∣ twinHi n := by
  have he : (6 * n + 6 * s) - (6 * s - 1) = twinHi n := by
    unfold twinHi; omega
  exact he ▸ shift_sub_dvd h hc

private theorem nine_lo_offset : ∀ p ∈ ninePrimes, p ∣ 6 * loShift + 1 := by native_decide
private theorem nine_hi_offset : ∀ p ∈ ninePrimes, p ∣ 6 * hiShift - 1 := by native_decide

theorem twinLo_shift {n p : ℕ} (hp : p ∈ ninePrimes)
    (h : p ∣ n + loShift) : p ∣ twinLo n :=
  lo_shift_aux (s := loShift) h (nine_lo_offset p hp)

theorem twinHi_shift {n p : ℕ} (hp : p ∈ ninePrimes)
    (h : p ∣ n + hiShift) : p ∣ twinHi n :=
  hi_shift_aux (s := hiShift) (by native_decide) h (nine_hi_offset p hp)

end CPNF
