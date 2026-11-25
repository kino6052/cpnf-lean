import Mathlib
import CpnfLean.Head

/-!
# CPNF — the correspondence layer

This file is the **only** place in the project that talks about `Nat.Prime`.

Everything before it is pure CPNF: a number survives a finite set of blockers, or it does
not. That gate needs no primality notion at all. Here we finally line the CPNF process up
against ordinary primes, and the result is the honest one: the framework's own residual —
"cofinally often the killer *is* a member of the pair" — is *equivalent* to unbounded
twin primes.

The engine is a single observation: **divisors of survivors survive.** If `m` survives a
stage and `d ≥ 2` divides `m`, then `d` survives too, because any blocker dividing `d`
would divide `m`. Since `certify k` is the least survivor, that gives `certify k ≤ d` for
every such divisor — the key bound that turns a direct kill into a twin pair.
-/

namespace CPNF

/-! ## Divisors of survivors survive -/

/-- **The transfer lemma.** A divisor `≥ 2` of a survivor survives the same blockers.
    A blocker dividing `d` would divide `m`, contradicting that `m` survives. -/
theorem survives_of_dvd {B : Finset ℕ} {m d : ℕ} (hd : d ∣ m) (h2 : 2 ≤ d)
    (hs : Survives B m) : Survives B d := by
  intro p hp hpd
  -- `p ∣ d` and `d ∣ m` give `p ∣ m`, which `hs` forbids.
  exact hs p hp (hpd.trans hd)

/-- **The killer bounds every cofactor.** If a number `m` survives stage `k` and
    `d ≥ 2` divides it, then `certify k ≤ d`: the cofactor is a survivor, and `certify k`
    is the least one. This is what makes a non-direct death carry a cofactor at least as
    big as the killer itself. -/
theorem certify_le_of_dvd {k m d : ℕ} (hm : m ∈ sieve (stage k)) (hd : d ∣ m) (h2 : 2 ≤ d) :
    certify k ≤ d := by
  obtain ⟨_hm2, hs⟩ := hm
  -- The cofactor survives, so it is a sieve member and leastness applies.
  exact next_le k d ⟨h2, survives_of_dvd hd h2 hs⟩

/-! ## The size obstruction -/

/-- **No room for a cofactor.** If `c ≥ 3`, a divisor `d ≥ c` that properly divides `m`
    with `m ≤ c + 2` cannot exist: a proper divisor is at most half its multiple.

    This is the whole content of "a direct death is a twin pair". -/
theorem no_cofactor {c m d : ℕ} (hc : 3 ≤ c) (hcd : c ≤ d) (hm : m ≤ c + 2)
    (hdvd : d ∣ m) (hlt : d < m) : False := by
  obtain ⟨t, ht⟩ := hdvd
  rcases t with _ | t
  · -- `m = 0`, but `d ≤ m` and `d ≥ 3`.
    rw [Nat.mul_zero] at ht
    omega
  rcases t with _ | t
  · -- `m = d`, contradicting the strict divisibility.
    rw [Nat.mul_one] at ht
    omega
  · -- `m = d * (t + 2) ≥ 2 * d ≥ 2 * c > c + 2` once `c ≥ 3`.
    have h2 : 2 * d ≤ m := by
      rw [ht]
      have h3 : 2 ≤ t + 2 := by omega
      calc 2 * d = d * 2 := by ring
        _ ≤ d * (t + 2) := Nat.mul_le_mul_left d h3
    omega

/-! ## Direct stages give twin pairs -/

/-- **A direct death is a real twin pair.** If the killer equals one of the members, both
    members are prime: each survives, so `certify k ≤` it, and no proper divisor `≥ 2` can
    exist by `no_cofactor`. -/
theorem prime_of_direct {k : ℕ}
    (h : certify k = twinLo (head k) ∨ certify k = twinHi (head k)) :
    Nat.Prime (twinLo (head k)) ∧ Nat.Prime (twinHi (head k)) := by
  have hpos : 1 ≤ head k := one_le_head k
  have hadm : Admissible (stage k) (head k) := head_admissible k
  -- `certify k` is the killer, i.e. one of `6n - 1`, `6n + 1`, so it is at least `5`.
  have hc3 : 3 ≤ certify k := by
    rcases h with h | h <;> simp only [twinLo, twinHi] at * <;> omega
  have hLo : twinLo (head k) ∈ sieve (stage k) :=
    ⟨by simp only [twinLo]; omega, hadm.1⟩
  have hHi : twinHi (head k) ∈ sieve (stage k) :=
    ⟨by simp only [twinHi]; omega, hadm.2⟩
  -- Both members are at most `certify k + 2`.
  have hbLo : twinLo (head k) ≤ certify k + 2 := by
    rcases h with h | h <;> simp only [twinLo, twinHi] at * <;> omega
  have hbHi : twinHi (head k) ≤ certify k + 2 := by
    rcases h with h | h <;> simp only [twinLo, twinHi] at * <;> omega
  have hLo2 : 2 ≤ twinLo (head k) := by simp only [twinLo]; omega
  have hHi2 : 2 ≤ twinHi (head k) := by simp only [twinHi]; omega
  refine ⟨Nat.prime_def_lt.mpr ⟨hLo2, ?_⟩, Nat.prime_def_lt.mpr ⟨hHi2, ?_⟩⟩
  · -- Every proper divisor of the lower member is `1`.
    intro d hdlt hdvd
    by_contra hne
    have hd2 : 2 ≤ d := by
      rcases Nat.lt_or_ge d 2 with h2 | h2
      · -- `d` is `0` or `1`; then a divisor of a member `≥ 2` is impossible.
        interval_cases d <;> omega
      · exact h2
    exact no_cofactor hc3 (certify_le_of_dvd hLo hdvd hd2) hbLo hdvd hdlt
  · -- The same for the upper member.
    intro d hdlt hdvd
    by_contra hne
    have hd2 : 2 ≤ d := by
      rcases Nat.lt_or_ge d 2 with h2 | h2
      · -- `d` is `0` or `1`; then a divisor of a member `≥ 2` is impossible.
        interval_cases d <;> omega
      · exact h2
    exact no_cofactor hc3 (certify_le_of_dvd hHi hdvd hd2) hbHi hdvd hdlt


/-! ## The process structure, made explicit -/

/-- `certify` is strictly increasing in the stage index. -/
theorem cert_mono_strict {i k : ℕ} (h : i < k) : certify i < certify k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = i + 1 + d := ⟨k - i - 1, by omega⟩
  clear h
  induction d with
  | zero => simpa using certify_strict i
  | succ d ih =>
    have h1 : certify i < certify (i + 1 + d) := ih
    have h2 : certify (i + 1 + d) < certify (i + 1 + d + 1) := certify_strict (i + 1 + d)
    have he : i + 1 + (d + 1) = i + 1 + d + 1 := by ring
    rw [he]; omega

/-- Every blocker at stage `k` is an earlier certified number. -/
theorem mem_stage_iff (k : ℕ) : ∀ p, p ∈ stage k ↔ ∃ i, i < k ∧ certify i = p := by
  induction k with
  | zero =>
    intro p
    rw [stage_zero_empty]
    constructor
    · intro h; exact absurd h (Finset.notMem_empty p)
    · rintro ⟨i, hi, _⟩; omega
  | succ k ih =>
    intro p
    rw [stage_succ]
    constructor
    · intro h
      rcases Finset.mem_insert.mp h with rfl | h
      · exact ⟨k, by omega, rfl⟩
      · obtain ⟨i, hi, hc⟩ := (ih p).mp h
        exact ⟨i, by omega, hc⟩
    · rintro ⟨i, hi, hc⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
      · exact Finset.mem_insert_of_mem ((ih p).mpr ⟨i, h, hc⟩)
      · subst h
        rw [← hc]
        exact Finset.mem_insert_self _ _

/-- Any blocker is strictly below the current certified number. -/
theorem blocker_lt_certify {k p : ℕ} (hp : p ∈ stage k) : p < certify k := by
  obtain ⟨i, hi, rfl⟩ := (mem_stage_iff k p).mp hp
  exact cert_mono_strict hi

/-! ## Twin pairs give direct stages -/

/-- **A twin pair gives a direct stage.** If `6n-1` and `6n+1` are both prime, then at the
    first stage whose killer reaches `6n-1`, the head is `n` and the killer is exactly
    `6n-1` — a direct death.

    The proof uses primality only through `Nat.prime_def_lt`: a blocker below a prime and
    dividing it would be `1`, which blockers never are. -/
theorem direct_of_twin {n : ℕ} (hn : 1 ≤ n) (hp : Nat.Prime (twinLo n))
    (hq : Nat.Prime (twinHi n)) : ∃ k, Direct k ∧ head k = n := by
  -- The first stage whose killer reaches the lower member.
  have hex : ∃ j, twinLo n ≤ certify j :=
    ⟨twinLo n, by have h := certify_ge_idx (twinLo n); omega⟩
  have hkmin : ∀ j, j < Nat.find hex → ¬ (twinLo n ≤ certify j) :=
    fun j hj => Nat.find_min hex hj
  -- So every blocker there is an earlier `certify`, hence below the lower member.
  have hbound : ∀ b ∈ stage (Nat.find hex), b < twinLo n := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := (mem_stage_iff _ b).mp hb
    by_contra hcon
    push Not at hcon
    exact absurd hcon (hkmin i hi)
  -- A blocker below a prime and dividing it would be `1`, but blockers are `≥ 2`.
  have keyLo : ∀ b, 2 ≤ b → b < twinLo n → ¬ b ∣ twinLo n := by
    intro b hb2 hblt hdvd
    have h1 : b = 1 := (Nat.prime_def_lt.mp hp).2 b hblt hdvd
    omega
  have keyHi : ∀ b, 2 ≤ b → b < twinHi n → ¬ b ∣ twinHi n := by
    intro b hb2 hblt hdvd
    have h1 : b = 1 := (Nat.prime_def_lt.mp hq).2 b hblt hdvd
    omega
  have hLo : Survives (stage (Nat.find hex)) (twinLo n) := by
    intro b hb hdvd
    exact keyLo b (above_one_stage _ b hb) (hbound b hb) hdvd
  have hHi : Survives (stage (Nat.find hex)) (twinHi n) := by
    intro b hb hdvd
    have hle : twinLo n ≤ twinHi n := by
      have ha : twinLo n = 6 * n - 1 := rfl
      have hb' : twinHi n = 6 * n + 1 := rfl
      omega
    exact keyHi b (above_one_stage _ b hb) (lt_of_lt_of_le (hbound b hb) hle) hdvd
  have hadm : Admissible (stage (Nat.find hex)) n := ⟨hLo, hHi⟩
  have hhead : head (Nat.find hex) ≤ n := head_le hn hadm
  have hadmh := head_admissible (Nat.find hex)
  have hcLo : certify (Nat.find hex) ≤ twinLo (head (Nat.find hex)) := by
    have h2 : 2 ≤ twinLo (head (Nat.find hex)) := by
      have ha : twinLo (head (Nat.find hex)) = 6 * head (Nat.find hex) - 1 := rfl
      have h1 : 1 ≤ head (Nat.find hex) := one_le_head _
      omega
    exact next_le _ _ ⟨h2, hadmh.1⟩
  have hmono : twinLo (head (Nat.find hex)) ≤ twinLo n := by
    have ha : twinLo (head (Nat.find hex)) = 6 * head (Nat.find hex) - 1 := rfl
    have hb : twinLo n = 6 * n - 1 := rfl
    have h1 : 1 ≤ head (Nat.find hex) := one_le_head _
    omega
  have hkP : twinLo n ≤ certify (Nat.find hex) := Nat.find_spec hex
  -- Squeeze: `certify ≤ twinLo (head) ≤ twinLo n ≤ certify`.
  have hfin : twinLo (head (Nat.find hex)) = certify (Nat.find hex) := by omega
  refine ⟨Nat.find hex, Or.inl hfin.symm, ?_⟩
  -- `twinLo` is injective below, so equal lower members give equal indices.
  have ha : twinLo (head (Nat.find hex)) = 6 * head (Nat.find hex) - 1 := rfl
  have hb : twinLo n = 6 * n - 1 := rfl
  have h1 : 1 ≤ head (Nat.find hex) := one_le_head _
  omega

/-! ## The residual, and its exact strength -/

/-- **The CPNF residual, stated on head values.** Cofinally often, the killer *is* one of
    the two members rather than a proper divisor of one. Writing cofinality on `head`
    rather than on the stage index is what makes the equivalence below go through: many
    stages share a head, so stage counts are not the right yardstick. -/
def OftenDirect : Prop := ∀ K, ∃ k, K ≤ head k ∧ Direct k

/-- **The head is unbounded.** If the head ever stalled below `K`, `head_escapes` would
    push it past `K` at some later stage. -/
theorem head_unbounded : ∀ K, ∃ k, K ≤ head k := by
  intro K
  induction K with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ K ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases h : K + 1 ≤ head k
    · exact ⟨k, h⟩
    · -- the head escapes its own value, so it goes past `K`
      have hex : ∃ j, head k < head j := ⟨max k (twinLo (head k) + 1), head_escapes k⟩
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, by omega⟩

/-- A direct stage is a genuine twin pair (`prime_of_direct`), and heads are cofinal. -/
theorem twins_of_oftenDirect (h : OftenDirect) :
    ∀ K, ∃ n, K ≤ n ∧ 1 ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  intro K
  obtain ⟨k, hk, hd⟩ := h K
  have hp := prime_of_direct hd
  exact ⟨head k, hk, one_le_head k, hp.1, hp.2⟩

/-- A twin pair produces a direct stage whose head is exactly its index. -/
theorem oftenDirect_of_twins
    (h : ∀ K, ∃ n, K ≤ n ∧ 1 ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) :
    OftenDirect := by
  intro K
  obtain ⟨n, hn, hn1, hp, hq⟩ := h K
  obtain ⟨k, hd, hhead⟩ := direct_of_twin hn1 hp hq
  exact ⟨k, by omega, hd⟩

/-- **The honest headline.** Within CPNF, "cofinally often the killer is a member of the
    pair" is *equivalent* to unbounded twin primes. The framing does not bypass the
    conjecture; it relocates it, and this file pins the relocation down exactly.

    Note this is an equivalence, not a route to a proof: neither side is known. -/
theorem oftenDirect_iff_unboundedTwins : OftenDirect ↔
    (∀ K, ∃ n, K ≤ n ∧ 1 ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) :=
  ⟨twins_of_oftenDirect, oftenDirect_of_twins⟩

end CPNF
