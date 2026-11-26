import Mathlib
import CpnfLean.ThinBlock

/-!
# CPNF — the injection: one prime base, at most one row (budget `X^(1/5)`)

The novel counting step behind the thin-block budget. Each row of `thinBad X` carries a
proper prime power `p^e` (with `e ≥ 5`, by `thin_exponent_ge_five`) on one of its two
members. Sending the row to its base `p` is injective: two distinct rows cannot share a base
(`base_inj`), because two powers of the same prime `p^a < p^b` satisfy `2·p^a ≤ p^b`, while
both member values lie in the interval `(6X, 12X+1]` where the ratio of any two is `< 2`.

Hence `thinBad_le_baseBudget`: `(thinBad X).card ≤ (baseBudget B).card` whenever
`12X+1 < B^5` — the proper-power budget is at `B ~ X^(1/5)` scale. The corollary
`boxed_of_fifth_root_signal` turns a thin-signal excess over that small budget into a
`WindowWitness`.

All unconditional, no `sorry`.
-/

namespace CPNF


noncomputable def hppBase {m : ℕ} (h : HigherPrimePower m) : ℕ :=
  Classical.choose h

noncomputable def hppExp {m : ℕ} (h : HigherPrimePower m) : ℕ :=
  Classical.choose (Classical.choose_spec h).2.2

lemma hppBase_prime {m : ℕ} (h : HigherPrimePower m) :
    Nat.Prime (hppBase h) := by
  exact (Classical.choose_spec h).2.1

lemma hppBase_pow {m : ℕ} (h : HigherPrimePower m) :
    (hppBase h) ^ (hppExp h) = m := by
  exact (Classical.choose_spec (Classical.choose_spec h).2.2).2

lemma hppExp_ge_two {m : ℕ} (h : HigherPrimePower m) :
    2 ≤ hppExp h := by
  exact (Finset.mem_Icc.mp (Classical.choose_spec (Classical.choose_spec h).2.2).1).1

lemma pow_double_le {p : ℕ} (hp : 2 ≤ p) {a b : ℕ} (hab : a < b) :
    2 * p ^ a ≤ p ^ b := by
  have h1 : p ^ a * p ≤ p ^ b := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : p ^ a * 2 ≤ p ^ a * p := Nat.mul_le_mul_left _ hp
  calc
    2 * p ^ a = p ^ a * 2 := by ring
    _ ≤ p ^ a * p := h2
    _ ≤ p ^ b := h1

lemma thinBlock_bounds {X n : ℕ} (hn : n ∈ thinBlock X) :
    6 * X < twinLo n ∧ twinHi n ≤ 12 * X + 1 := by
  have hb : n ∈ blk X := (Finset.mem_filter.mp hn).1
  have hXn : X < n := (Finset.mem_Ioc.mp hb).1
  have hn2 : n ≤ 2 * X := (Finset.mem_Ioc.mp hb).2
  constructor
  · unfold twinLo
    omega
  · unfold twinHi
    omega

private lemma thinMember_bounds {X n m : ℕ} (hn : n ∈ thinBlock X)
    (c : m = twinLo n ∨ m = twinHi n) :
    6 * X < m ∧ m ≤ 12 * X + 1 := by
  obtain ⟨hl, hu⟩ := thinBlock_bounds hn
  have ho : twinLo n ≤ twinHi n := by
    unfold twinLo twinHi
    omega
  rcases c with h | h
  · exact h ▸ ⟨hl, ho.trans hu⟩
  · exact h ▸ ⟨hl.trans_le ho, hu⟩

theorem base_inj {X n₁ n₂ m₁ m₂ : ℕ}
    (hne : n₁ ≠ n₂)
    (hb₁ : n₁ ∈ thinBlock X) (hb₂ : n₂ ∈ thinBlock X)
    (c₁ : m₁ = twinLo n₁ ∨ m₁ = twinHi n₁)
    (c₂ : m₂ = twinLo n₂ ∨ m₂ = twinHi n₂)
    (h₁ : HigherPrimePower m₁) (h₂ : HigherPrimePower m₂)
    (hbase : hppBase h₁ = hppBase h₂) : False := by
  obtain ⟨hl₁, hu₁⟩ := thinMember_bounds hb₁ c₁
  obtain ⟨hl₂, hu₂⟩ := thinMember_bounds hb₂ c₂
  have hp := (hppBase_prime h₁).two_le
  have v₁ := hppBase_pow h₁
  have v₂ := hppBase_pow h₂
  rw [← hbase] at v₂
  rcases lt_trichotomy (hppExp h₁) (hppExp h₂) with hlt | heq | hgt
  · have hd := pow_double_le hp hlt
    rw [v₁, v₂] at hd
    omega
  · rw [heq] at v₁
    have hm : m₁ = m₂ := v₁.symm.trans v₂
    rcases c₁ with a | a <;> rcases c₂ with b | b <;>
      rw [a, b] at hm <;> simp only [twinLo, twinHi] at hm <;> omega
  · have hd := pow_double_le hp hgt
    rw [v₂, v₁] at hd
    omega

/-- Prefer the lower member. The value `0` is used only when neither
member admits a higher-prime-power certificate. -/
noncomputable def thinBase (n : ℕ) : ℕ :=
  if hl : HigherPrimePower (twinLo n) then hppBase hl
  else if hu : HigherPrimePower (twinHi n) then hppBase hu
  else 0

private lemma thinBad_mem_block {X n : ℕ} (hn : n ∈ thinBad X) :
    n ∈ thinBlock X := by
  have hs : n ∈ thinSignal X := (Finset.mem_filter.mp hn).1
  exact (Finset.mem_filter.mp hs).1

/-- Keep the chosen certificate and its side together, so the budget
bound and the injection refer to the same base. -/
theorem thinBase_spec {X n : ℕ} (hn : n ∈ thinBad X) :
    ∃ (m : ℕ) (h : HigherPrimePower m),
      (m = twinLo n ∨ m = twinHi n) ∧ thinBase n = hppBase h := by
  by_cases hl : HigherPrimePower (twinLo n)
  · exact ⟨twinLo n, hl, Or.inl rfl, by simp [thinBase, hl]⟩
  · have hc : HigherPrimePower (twinLo n) ∨ HigherPrimePower (twinHi n) :=
      (Finset.mem_filter.mp hn).2
    have hu := hc.resolve_left hl
    exact ⟨twinHi n, hu, Or.inr rfl, by simp [thinBase, hl, hu]⟩

theorem thinBase_mem_baseBudget {X B n : ℕ} (hB : 12 * X + 1 < B ^ 5)
    (hn : n ∈ thinBad X) : thinBase n ∈ baseBudget B := by
  obtain ⟨m, h, c, hb⟩ := thinBase_spec hn
  have ht := thinBad_mem_block hn
  have hr : n % 14 = 11 := (Finset.mem_filter.mp ht).2
  have hp := hppBase_prime h
  have he : 5 ≤ hppExp h := by
    apply thin_exponent_ge_five hr (hppExp_ge_two h) (p := hppBase h)
    rw [hppBase_pow h]
    exact c
  have hlt : (hppBase h) ^ 5 < B ^ 5 := calc
    (hppBase h) ^ 5 ≤ (hppBase h) ^ (hppExp h) :=
      Nat.pow_le_pow_right hp.pos he
    _ = m := hppBase_pow h
    _ ≤ 12 * X + 1 := (thinMember_bounds ht c).2
    _ < B ^ 5 := hB
  have hsmall : hppBase h < B :=
    (Nat.pow_lt_pow_iff_left (by decide : 5 ≠ 0)).mp hlt
  rw [hb]
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, hp⟩

theorem thinBad_le_baseBudget {X B : ℕ} (hB : 12 * X + 1 < B ^ 5) :
    (thinBad X).card ≤ (baseBudget B).card := by
  apply Finset.card_le_card_of_injOn thinBase
  · intro n hn
    exact thinBase_mem_baseBudget hB hn
  · intro n₁ hn₁ n₂ hn₂ he
    change n₁ ∈ thinBad X at hn₁
    change n₂ ∈ thinBad X at hn₂
    obtain ⟨m₁, h₁, c₁, e₁⟩ := thinBase_spec hn₁
    obtain ⟨m₂, h₂, c₂, e₂⟩ := thinBase_spec hn₂
    have hb₁ := thinBad_mem_block hn₁
    have hb₂ := thinBad_mem_block hn₂
    have hrow : n₁ ∈ blk X := (Finset.mem_filter.mp hb₁).1
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp
      (show n₁ ∈ Finset.Ioc X (2 * X) from hrow)
    have hX : 0 < X := by omega
    by_contra hne
    exact base_inj hne hb₁ hb₂ c₁ c₂ h₁ h₂
      (e₁.symm.trans (he.trans e₂))

theorem boxed_of_fifth_root_signal {X B : ℕ} (hB : 12 * X + 1 < B ^ 5)
    (hs : (baseBudget B).card < (thinSignal X).card) :
    WindowWitness X := by
  exact boxed_of_thin_slack (le_refl X)
    (lt_of_le_of_lt (thinBad_le_baseBudget hB) hs)


end CPNF
