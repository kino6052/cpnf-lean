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

/-! ## The process enumerates the primes -/

/-- **Every certified number is prime.** A proper divisor `d ≥ 2` of `certify k` would
    itself survive (divisors of survivors survive), yet be strictly smaller than the least
    survivor — impossible. So CPNF is prime enumeration, not an approximation of it. -/
theorem certify_prime (k : ℕ) : Nat.Prime (certify k) := by
  have hm : certify k ∈ sieve (stage k) := certify_survives k
  refine Nat.prime_def_lt.mpr ⟨hm.1, ?_⟩
  -- every proper divisor is `1`
  intro d hdlt hdvd
  by_contra hne
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d <;> omega
    · exact h
  exact (not_lt_of_ge (certify_le_of_dvd hm hdvd hd2)) hdlt

/-- **No prime is ever skipped.** The stage `k` is exactly the set of primes below
    `certify k`: one direction is `certify_prime` plus `blocker_lt_certify`, the other
    says a prime below the killer that was not a blocker would have to survive, which
    contradicts the killer being least. -/
theorem stage_eq_primes_lt (k : ℕ) : stage k = (Finset.range (certify k)).filter Nat.Prime := by
  ext q
  constructor
  · -- every blocker is an earlier certified number, hence a prime below the killer
    intro hq
    obtain ⟨i, hi, rfl⟩ := (mem_stage_iff k q).mp hq
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨blocker_lt_certify hq, certify_prime i⟩
  · -- a prime below the killer must already be a blocker
    intro hq
    rw [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hlt, hprime⟩ := hq
    by_contra hnot
    -- otherwise it survives, so it is in the sieve, so it is at least the killer
    have hsurv : Survives (stage k) q := by
      intro p hp hpd
      -- a blocker dividing the prime `q` is `q` itself, so `q` would be a blocker
      rcases hprime.eq_one_or_self_of_dvd p hpd with h1 | h1
      · have := above_one_stage k p hp; omega
      · exact hnot (h1 ▸ hp)
    have hmem : q ∈ sieve (stage k) := ⟨hprime.two_le, hsurv⟩
    have := next_le k q hmem
    omega

/-! ## The score: one record computation instead of two scans -/

/-- The **score** of a twin index: the smaller of the least prime factors of the two
    members. Read it as "how much sieving this pair can take": the pair is admissible at
    stage `k` exactly when its score reaches the killer `certify k`. -/
def score (n : ℕ) : ℕ := min (twinLo n).minFac (twinHi n).minFac

/-- Surviving stage `k` pushes the score up to the killer: the least prime factor of a
    survivor is not a blocker, and the blockers are exactly the primes below `certify k`. -/
theorem minFac_le_cert_of_survives {k m : ℕ} (hm : 2 ≤ m) (hs : Survives (stage k) m) :
    certify k ≤ m.minFac := by
  by_contra hcon
  -- Otherwise the least prime factor is a prime below the killer, hence a blocker.
  push Not at hcon
  have hprime : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hmem : m.minFac ∈ stage k := by
    rw [stage_eq_primes_lt, Finset.mem_filter, Finset.mem_range]
    exact ⟨hcon, hprime⟩
  exact hs m.minFac hmem (Nat.minFac_dvd m)

/-- Conversely, a member whose least prime factor is at least the killer survives. -/
theorem survives_of_cert_le_minFac {k m : ℕ} (h : certify k ≤ m.minFac) :
    Survives (stage k) m := by
  intro p hp hpd
  rw [stage_eq_primes_lt, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hlt, hprime⟩ := hp
  -- any prime dividing `m` is at least its least prime factor
  have := Nat.minFac_le_of_dvd hprime.two_le hpd
  omega

/-- **The bridge to the score.** A pair is admissible at stage `k` exactly when its score
    reaches `certify k`. This replaces "test both members against every blocker" by one
    arithmetic comparison. -/
theorem admissible_iff_score {k n : ℕ} (hn : 1 ≤ n) :
    Admissible (stage k) n ↔ certify k ≤ score n := by
  have hlo : 2 ≤ twinLo n := by
    have ha : twinLo n = 6 * n - 1 := rfl; omega
  have hhi : 2 ≤ twinHi n := by
    have ha : twinHi n = 6 * n + 1 := rfl; omega
  constructor
  · intro h
    exact le_min (minFac_le_cert_of_survives hlo h.1) (minFac_le_cert_of_survives hhi h.2)
  · intro h
    exact ⟨survives_of_cert_le_minFac (le_trans h (min_le_left _ _)),
           survives_of_cert_le_minFac (le_trans h (min_le_right _ _))⟩

/-- **The head is a first crossing of the score.** This is the finite, computable form of
    the head: no leastness scan over stages is needed, only the least `n ≤ N` whose score
    reaches the killer. -/
theorem head_le_iff (k N : ℕ) :
    head k ≤ N ↔ ∃ n, 1 ≤ n ∧ n ≤ N ∧ certify k ≤ score n := by
  constructor
  · -- the head itself is such an `n`
    intro h
    exact ⟨head k, one_le_head k, h, (admissible_iff_score (one_le_head k)).mp (head_admissible k)⟩
  · -- any such `n` bounds the least one
    rintro ⟨n, hn, hnN, hsc⟩
    exact le_trans (head_le hn ((admissible_iff_score hn).mpr hsc)) hnN

/-! ## The record-scan payoff: a passing row is a twin pair -/

/-- For a composite `m`, the least prime factor squared is at most `m`: the least prime
    factor is at most the remaining cofactor. -/
theorem minFac_sq_le {m : ℕ} (hm : 2 ≤ m) (hlt : m.minFac < m) :
    m.minFac * m.minFac ≤ m := by
  obtain ⟨t, ht⟩ := Nat.minFac_dvd m
  have htm : t ∣ m := by rw [ht]; exact dvd_mul_left t m.minFac
  have ht2 : 2 ≤ t := by rcases t with _ | _ | t <;> omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : t ≠ 1)
  have hqm : q ∣ m := hqd.trans htm
  have hqge : m.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqm
  have hqt : q ≤ t := Nat.le_of_dvd (by omega) hqd
  calc m.minFac * m.minFac ≤ m.minFac * t := Nat.mul_le_mul_left _ (le_trans hqge hqt)
    _ = m := ht.symm

/-- **A primality test by size.** If `m ≤ B^2` and `m` has no prime factor at most `B`
    (strictly below `m.minFac`), then `m` is prime: a composite `m` would have
    `m.minFac^2 ≤ m ≤ B^2`, forcing `m.minFac ≤ B`. -/
theorem prime_of_minFac_gt {m B : ℕ} (hm : 2 ≤ m) (hB : m ≤ B * B) (h : B < m.minFac) :
    Nat.Prime m := by
  rcases Nat.lt_or_ge m.minFac m with hlt | hge
  · exfalso
    have hsq := minFac_sq_le hm hlt
    exact (not_le_of_gt h) (Nat.mul_self_le_mul_self_iff.mp (hsq.trans hB))
  · have heq : m.minFac = m :=
      le_antisymm (Nat.minFac_le (by omega : 0 < m)) hge
    have hp := Nat.minFac_prime (by omega : m ≠ 1)
    simpa only [heq] using hp

/-- **A passing row is a twin pair.** If the score reaches the lower member, then no
    prime factor below the lower member divides either member; the cutoff `B = 3n` is
    strictly below the lower member yet already has `B^2` covering the upper member, so
    `prime_of_minFac_gt` applies to both. No `n = 1` case is special. -/
theorem twin_of_score_row {n : ℕ} (hn : 1 ≤ n) (h : twinLo n ≤ score n) :
    Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  have hlo : twinLo n ≤ (twinLo n).minFac := h.trans (min_le_left _ _)
  have hhi : twinLo n ≤ (twinHi n).minFac := h.trans (min_le_right _ _)
  have hcut : 3 * n < twinLo n := by unfold twinLo; omega
  have h3 : 3 ≤ 3 * n := by omega
  have hmul : 3 * (3 * n) ≤ (3 * n) * (3 * n) := Nat.mul_le_mul_right (3 * n) h3
  have hcover : twinHi n ≤ (3 * n) * (3 * n) := by unfold twinHi; omega
  have horder : twinLo n ≤ twinHi n := by unfold twinLo twinHi; omega
  exact ⟨prime_of_minFac_gt (by omega) (horder.trans hcover) (hcut.trans_le hlo),
         prime_of_minFac_gt (by omega) hcover (hcut.trans_le hhi)⟩

/-! ## The square test: one inequality decides the twin question -/

/-- The least prime factor of a prime is the prime itself. -/
theorem minFac_eq_self_of_prime {m : ℕ} (hm : Nat.Prime m) : m.minFac = m := by
  have hd : m.minFac ∣ m := Nat.minFac_dvd m
  rcases hm.eq_one_or_self_of_dvd m.minFac hd with h | h
  · exact absurd h (Nat.minFac_prime (Nat.Prime.ne_one hm)).ne_one
  · exact h

/-- At a row that passes, the score is exactly the lower member. -/
theorem score_eq_lo_of_row {n : ℕ} (hn : 1 ≤ n) (h : twinLo n ≤ score n) :
    score n = twinLo n := by
  have hle : twinLo n ≤ (twinLo n).minFac := h.trans (min_le_left _ _)
  have hmf : (twinLo n).minFac ≤ twinLo n :=
    Nat.minFac_le (by have ha : twinLo n = 6 * n - 1 := rfl; omega)
  have hsc : score n ≤ (twinLo n).minFac := min_le_left _ _
  omega

/-- `(6n-1)^2 > 6n+1` for every `n ≥ 1`. Substituting `n = k+1` removes the truncated
    subtraction so that `nlinarith` can see the quadratic. -/
theorem lo_sq_gt_hi (n : ℕ) (hn : 1 ≤ n) : 6 * n + 1 < (6 * n - 1) * (6 * n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h : 6 * (k + 1) - 1 = 6 * k + 5 := by omega
  rw [h]; nlinarith

/-- If the score falls short of the lower member, the score squared is at most the
    upper member: the shortfall means a member is composite at its least prime factor,
    which puts `score^2` below the member it strikes. -/
theorem score_sq_le_hi_of_gt {n : ℕ} (hn : 1 ≤ n) (hb : score n < twinLo n) :
    score n * score n ≤ twinHi n := by
  have hlo2 : 2 ≤ twinLo n := by have ha : twinLo n = 6 * n - 1 := rfl; omega
  have hhi2 : 2 ≤ twinHi n := by have ha : twinHi n = 6 * n + 1 := rfl; omega
  have horder : twinLo n < twinHi n := by
    have a : twinLo n = 6 * n - 1 := rfl
    have b : twinHi n = 6 * n + 1 := rfl
    omega
  -- the score is a least prime factor of one member, and lies below that member
  have hdiv : score n * score n ≤ twinLo n ∨ score n * score n ≤ twinHi n := by
    rcases le_total (twinLo n).minFac (twinHi n).minFac with hle | hle
    · left
      have hs : score n = (twinLo n).minFac := by
        have h : score n = min (twinLo n).minFac (twinHi n).minFac := rfl
        rw [h]; exact Nat.min_eq_left hle
      have hlt : (twinLo n).minFac < twinLo n := hs ▸ hb
      have hsq : (twinLo n).minFac * (twinLo n).minFac ≤ twinLo n := minFac_sq_le hlo2 hlt
      rw [hs]; exact hsq
    · right
      have hs : score n = (twinHi n).minFac := by
        have h : score n = min (twinLo n).minFac (twinHi n).minFac := rfl
        rw [h]; exact Nat.min_eq_right hle
      have hlt : (twinHi n).minFac < twinHi n := by omega
      have hsq : (twinHi n).minFac * (twinHi n).minFac ≤ twinHi n := minFac_sq_le hhi2 hlt
      rw [hs]; exact hsq
  rcases hdiv with h | h
  · omega
  · exact h

/-- **The square test.** `twinHi n < score n ^ 2` is equivalent to the score reaching the
    lower member — the two forms the record scan uses are the same condition. -/
theorem sq_test_iff {n : ℕ} (hn : 1 ≤ n) :
    twinHi n < score n * score n ↔ twinLo n ≤ score n := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have h1 := score_sq_le_hi_of_gt hn hcon
    omega
  · intro h
    have hle : twinLo n ≤ (twinLo n).minFac := h.trans (min_le_left _ _)
    have hmf : (twinLo n).minFac ≤ twinLo n :=
      Nat.minFac_le (by have ha : twinLo n = 6 * n - 1 := rfl; omega)
    have hsc : score n ≤ (twinLo n).minFac := min_le_left _ _
    have hb : score n = twinLo n := by omega
    have ha : twinLo n = 6 * n - 1 := rfl
    have hc : twinHi n = 6 * n + 1 := rfl
    rw [hb, ha, hc]
    exact lo_sq_gt_hi n hn

/-- **One inequality decides the twin question.** For every `n ≥ 1`, both members are
    prime exactly when `6n+1 < score n ^ 2`. -/
theorem twin_iff_sq_test {n : ℕ} (hn : 1 ≤ n) :
    (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) ↔ twinHi n < score n * score n := by
  constructor
  · intro h
    have hL : (twinLo n).minFac = twinLo n := minFac_eq_self_of_prime h.1
    have hH : (twinHi n).minFac = twinHi n := minFac_eq_self_of_prime h.2
    have hsc : score n = twinLo n := by
      have h' : score n = min (twinLo n).minFac (twinHi n).minFac := rfl
      rw [h', hL, hH]
      exact Nat.min_eq_left (by
        have a : twinLo n = 6 * n - 1 := rfl
        have b : twinHi n = 6 * n + 1 := rfl; omega)
    exact (sq_test_iff hn).mpr (le_of_eq hsc.symm)
  · intro h
    exact twin_of_score_row hn ((sq_test_iff hn).mp h)

/-! ## Records: the finite scan, and a null scan is a theorem -/

/-- `n` is a **strict record** if it is positive and its score exceeds every earlier
    score. The record list is a run-length encoding of the head sequence. -/
def IsRecord (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → score m < score n

/-- Every score is at most the lower member. -/
theorem score_le_lo (m : ℕ) (hm : 1 ≤ m) : score m ≤ twinLo m := by
  have hsc : score m ≤ (twinLo m).minFac := min_le_left _ _
  have hmf : (twinLo m).minFac ≤ twinLo m :=
    Nat.minFac_le (by have ha : twinLo m = 6 * m - 1 := rfl; omega)
  omega

/-- **Every twin index is a strict record.** A twin's score is its lower member, larger
    than any earlier score, so no twin pair can be a non-record that the scan misses. -/
theorem isRecord_of_twin {n : ℕ} (hn : 1 ≤ n)
    (hp : Nat.Prime (twinLo n)) (hq : Nat.Prime (twinHi n)) : IsRecord n := by
  refine ⟨hn, ?_⟩
  have hscn : score n = twinLo n := by
    have hdef : score n = min (twinLo n).minFac (twinHi n).minFac := rfl
    rw [hdef, minFac_eq_self_of_prime hp, minFac_eq_self_of_prime hq]
    exact Nat.min_eq_left (by
      have a : twinLo n = 6 * n - 1 := rfl
      have b : twinHi n = 6 * n + 1 := rfl; omega)
  intro m hm hmn
  have h1 : score m ≤ twinLo m := score_le_lo m hm
  have ha : twinLo m = 6 * m - 1 := rfl
  have hb : twinLo n = 6 * n - 1 := rfl
  omega

/-- **A null scan is a theorem.** Checking only the strict records: no record in `[1, N]`
    passes the square test exactly when there is no twin pair in `[1, N]`. A finished
    scan is a proof whether it finds anything or not. -/
theorem no_passing_record_iff_no_twin (N : ℕ) :
    (∀ n, 1 ≤ n → n ≤ N → IsRecord n → ¬ twinHi n < score n * score n) ↔
    (∀ n, 1 ≤ n → n ≤ N → ¬ (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n))) := by
  constructor
  · intro hscan n hn hnN htw
    -- a twin index is a record and passes the test, contradicting the null scan
    have hrec : IsRecord n := isRecord_of_twin hn htw.1 htw.2
    have hpass : twinHi n < score n * score n := (twin_iff_sq_test hn).mp htw
    exact hscan n hn hnN hrec hpass
  · intro htwins n hn hnN hrec hpass
    -- a passing record is a twin, contradicting the absence of twins
    exact htwins n hn hnN ((twin_iff_sq_test hn).mpr hpass)

/-! ## Finalised: pointwise scan, score-attainment, and the head crossing -/

/-- **A passing record is exactly a twin index.** Soundness uses only the square test;
    completeness uses that a twin index is always a record. -/
theorem passing_record_iff_twin {n : ℕ} (hn : 1 ≤ n) :
    (IsRecord n ∧ twinHi n < score n * score n) ↔
    (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) := by
  constructor
  · intro h
    exact (twin_iff_sq_test hn).mpr h.2
  · intro h
    exact ⟨isRecord_of_twin hn h.1 h.2, (twin_iff_sq_test hn).mp h⟩

/-- **A positive row is twin exactly when its score attains its upper bound.** This lets
    an executable scan test equality `score n = twinLo n` instead of squaring. -/
theorem twin_iff_score_eq_lo {n : ℕ} (hn : 1 ≤ n) :
    (Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n)) ↔ score n = twinLo n := by
  rw [twin_iff_sq_test hn, sq_test_iff hn]
  exact ⟨score_eq_lo_of_row hn, fun h => h.ge⟩

/-- **The head is a first crossing of the score.** `head k = n` exactly when the killer
    reaches the score at `n` and no earlier score does: the left endpoint of the interval
    is open, the right closed — a tie is owned by the earlier index. -/
theorem head_eq_iff_first_crossing {k n : ℕ} (hn : 1 ≤ n) :
    head k = n ↔
      certify k ≤ score n ∧
      ∀ m, 1 ≤ m → m < n → score m < certify k := by
  constructor
  · intro he
    subst n
    refine ⟨(admissible_iff_score hn).mp (head_admissible k), ?_⟩
    intro m hm hlt
    by_contra! h
    exact (not_le_of_gt hlt) (head_le hm ((admissible_iff_score hm).mpr h))
  · rintro ⟨hc, hearlier⟩
    apply le_antisymm (head_le hn ((admissible_iff_score hn).mpr hc))
    by_contra! h
    exact (not_lt_of_ge
      ((admissible_iff_score (one_le_head k)).mp (head_admissible k)))
      (hearlier (head k) (one_le_head k) h)

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

/-! ## The conditional: a moment estimate suffices for the gap -/

/-- A failing row (score short of the lower member) at index at most `2*t^2` contributes
    at most `4*t` to the score: the shortfall puts `score^2 ≤ 6n+1 ≤ 12t^2+1`, so the
    score itself is at most `4t` once `t ≥ 1`. -/
theorem failing_score_le_four_mul {t n : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hN : n ≤ 2 * t ^ 2) (hf : score n ≠ twinLo n) :
    score n ≤ 4 * t := by
  have hlt : score n < twinLo n := lt_of_le_of_ne (score_le_lo n hn) hf
  have hs := score_sq_le_hi_of_gt hn hlt
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [ht]
  apply Nat.mul_self_le_mul_self_iff.mp
  unfold twinHi at hs
  nlinarith only [hs, hN, ht2]

/-- A square-scale block of indices. -/
def momentBlock (t : ℕ) : Finset ℕ := Finset.Icc (t ^ 2) (2 * t ^ 2)

/-- The total score over a block — the first moment, an integer sum, no asymptotics. -/
def scoreMass (t : ℕ) : ℕ := ∑ n ∈ momentBlock t, score n

/-- The passing rows in a block: exactly the twin indices in that block. -/
def passingRows (t : ℕ) : Finset ℕ :=
  (momentBlock t).filter (fun n => score n = twinLo n)

/-- A budget: allow `4*t` per row plus `12*t^2` for each passing row. A block whose mass
    exceeds the budget must contain more than `r` passing rows. -/
theorem passingRows_gt_of_mass {t r : ℕ} (ht : 1 ≤ t)
    (hm : (momentBlock t).card * (4 * t) + r * (12 * t ^ 2) < scoreMass t) :
    r < (passingRows t).card := by
  have hrow (n : ℕ) (hn : n ∈ momentBlock t) :
      score n ≤ 4 * t + (if score n = twinLo n then 12 * t ^ 2 else 0) := by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp (show n ∈ Finset.Icc (t^2) (2*t^2) from hn)
    have ht2 : 1 ≤ t ^ 2 := by nlinarith [ht]
    have hn1 : 1 ≤ n := ht2.trans hl
    by_cases hp : score n = twinLo n
    · rw [if_pos hp, hp]
      unfold twinLo
      omega
    · rw [if_neg hp, Nat.add_zero]
      exact failing_score_le_four_mul ht hn1 hu hp
  have hbudget : scoreMass t ≤
      (momentBlock t).card * (4 * t) + (passingRows t).card * (12 * t ^ 2) := by
    calc
      scoreMass t ≤ ∑ n ∈ momentBlock t,
          (4 * t + (if score n = twinLo n then 12 * t ^ 2 else 0)) :=
        Finset.sum_le_sum hrow
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [passingRows, Nat.nsmul_eq_mul]
  by_contra! h
  exact (not_lt_of_ge (hbudget.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right (12 * t ^ 2) h) _))) hm

/-- **The new ingredient.** On cofinally many square-scale blocks the mean score exceeds
    `4*t`. This is a finite integer comparison for each proposed `t`; its cofinality is
    not certified by any finite scan, and no asymptotic formula is required. -/
def CofinalScoreMass : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧ (momentBlock t).card * (4 * t) < scoreMass t

/-- **The moment estimate suffices for the exact record target.** -/
theorem passing_beyond_of_scoreMass (H : CofinalScoreMass) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 1 ≤ n ∧ score n = twinLo n := by
  intro K
  obtain ⟨t, ht, hm⟩ := H (K + 1)
  have ht1 : 1 ≤ t := by omega
  have hc : 0 < (passingRows t).card :=
    passingRows_gt_of_mass (r := 0) ht1 (by simpa using hm)
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hc
  obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hn
  have hl : t ^ 2 ≤ n := (Finset.mem_Icc.mp hb).1
  have htsq : t ≤ t ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left t ht1
  have hn1 : 1 ≤ n := by omega
  exact ⟨n, by omega, hn1, hp⟩

/-- **The conditional, closed.** If the block score-mass is cofinally large, then there
    are twin primes beyond every bound — the conjecture follows from the moment estimate.
    This is a conditional, not a proof of `CofinalScoreMass`. -/
theorem twins_of_scoreMass (H : CofinalScoreMass) :
    ∀ K, ∃ n, K ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  intro K
  obtain ⟨n, hKn, hn1, hsc⟩ := passing_beyond_of_scoreMass H K
  exact ⟨n, hKn, (twin_iff_score_eq_lo hn1).mpr hsc⟩

/-! ## The second moment: one twin suffices -/

/-- **Energy test.** In a block `[N, 2N]`, the sum of squared scores beating the sum of
    upper members is equivalent to the block containing a passing row. One twin is enough:
    its squared score `(6N-1)^2` alone exceeds the entire upper-member budget. -/
theorem energy_block_iff {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc N (2*N), twinHi n) <
        (∑ n ∈ Finset.Icc N (2*N), score n * score n) ↔
      ∃ n ∈ Finset.Icc N (2*N), score n = twinLo n := by
  constructor
  · -- no passing row: every squared score sits under its upper member
    intro he
    by_contra h
    apply (not_lt_of_ge ?_) he
    apply Finset.sum_le_sum
    intro n hn
    have hlo := (Finset.mem_Icc.mp hn).1
    have hn1 : 1 ≤ n := by omega
    have hf : score n ≠ twinLo n := fun hp => h ⟨n, hn, hp⟩
    exact score_sq_le_hi_of_gt hn1 (lt_of_le_of_ne (score_le_lo n hn1) hf)
  · -- one passing row outweighs the whole block budget
    rintro ⟨n, hn, hp⟩
    have hb := Finset.mem_Icc.mp hn
    have hc : (Finset.Icc N (2*N)).card = N+1 := by
      rw [Nat.card_Icc]
      omega
    have budget :
        (∑ m ∈ Finset.Icc N (2*N), twinHi m) ≤ (N+1)*(12*N+1) := by
      calc
        _ ≤ ∑ m ∈ Finset.Icc N (2*N), (12*N+1) := by
          apply Finset.sum_le_sum
          intro m hm
          have hu := (Finset.mem_Icc.mp hm).2
          unfold twinHi
          omega
        _ = _ := by simp [hc, Nat.nsmul_eq_mul]
    have single :
        score n * score n ≤ ∑ m ∈ Finset.Icc N (2*N), score m * score m :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (score i * score i)) hn
    have hlow : 6*N-1 ≤ score n := by
      rw [hp, twinLo]
      omega
    have gap : (N+1)*(12*N+1) < (6*N-1)*(6*N-1) := by
      obtain ⟨k, rfl⟩ : ∃ k, N = k+2 := ⟨N-2, by omega⟩
      rw [show 6*(k+2)-1 = 6*k+11 by omega]
      nlinarith
    exact lt_of_le_of_lt budget
      (lt_of_lt_of_le gap ((Nat.mul_le_mul hlow hlow).trans single))

/-- **The energy hypothesis.** Cofinally many blocks `[N, 2N]` carry more squared-score
    mass than upper-member mass. -/
def CofinalScoreEnergy : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ 2 ≤ N ∧
    (∑ n ∈ Finset.Icc N (2*N), twinHi n) <
      (∑ n ∈ Finset.Icc N (2*N), score n * score n)

/-- **The energy hypothesis is exactly cofinal passing rows** — no clusters needed. -/
theorem energy_iff_cofinal_pass :
    CofinalScoreEnergy ↔ ∀ K : ℕ, ∃ n, K ≤ n ∧ score n = twinLo n := by
  constructor
  · intro H K
    obtain ⟨N, hKN, hN, he⟩ := H K
    obtain ⟨n, hn, hp⟩ := (energy_block_iff hN).mp he
    exact ⟨n, hKN.trans (Finset.mem_Icc.mp hn).1, hp⟩
  · intro H K
    obtain ⟨n, hn, hp⟩ := H (K+2)
    refine ⟨n, by omega, by omega, (energy_block_iff (by omega : 2 ≤ n)).mpr ?_⟩
    exact ⟨n, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hp⟩

/-- **Energy suffices.** -/
theorem twins_of_scoreEnergy (H : CofinalScoreEnergy) :
    ∀ K : ℕ, ∃ n, K ≤ n ∧ Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  intro K
  obtain ⟨n, hn, hp⟩ := energy_iff_cofinal_pass.mp H (K+1)
  exact ⟨n, by omega, (twin_iff_score_eq_lo (by omega)).mpr hp⟩

/-- The first-moment hypothesis gives cofinal passing rows. -/
theorem cofinal_pass_of_mass (H : CofinalScoreMass) :
    ∀ K : ℕ, ∃ n, K ≤ n ∧ score n = twinLo n := by
  intro K
  obtain ⟨n, hn, _, hp⟩ := passing_beyond_of_scoreMass H K
  exact ⟨n, hn, hp⟩

/-- The first moment implies the second: the earlier hypothesis is stronger than needed. -/
theorem energy_of_mass (H : CofinalScoreMass) : CofinalScoreEnergy :=
  energy_iff_cofinal_pass.mpr (cofinal_pass_of_mass H)

/-! ## Reduction to Dickson's conjecture -/

/-- The forms `6m+5, 6m+7` are locally admissible: for every prime `p` there is an input
    at which `p` divides neither. -/
lemma dickson_twin_admissible (p : ℕ) (hp : Nat.Prime p) :
    ∃ m : ℕ, ¬ p ∣ 6*m + 5 ∧ ¬ p ∣ 6*m + 7 := by
  by_cases h : p ≤ 7
  · -- the small primes are checked directly (the residues 5, 7 are coprime to them)
    refine ⟨1, ?_⟩
    have h2 := hp.two_le
    interval_cases p <;> norm_num
  · -- a prime above 7 cannot divide 5 or 7
    refine ⟨0, ?_⟩
    change (¬ p ∣ 5) ∧ (¬ p ∣ 7)
    constructor <;> intro hd
    · have := Nat.le_of_dvd (by decide : 0 < 5) hd
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 7) hd
      omega

/-- **Dickson's conjecture** for two positive-coefficient linear forms: if the pair is
    locally admissible (every prime divides neither value at some input), then there are
    arbitrarily large inputs at which both values are prime. -/
def DicksonTwoPositive : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
    (∀ p : ℕ, Nat.Prime p →
      ∃ m : ℕ, ¬ p ∣ a*m + b ∧ ¬ p ∣ c*m + d) →
    ∀ K : ℕ, ∃ m : ℕ, K ≤ m ∧
      Nat.Prime (a*m + b) ∧ Nat.Prime (c*m + d)

/-- **Dickson's conjecture implies the energy statement.** The forms `6m+5, 6m+7` are the
    twin pair at `n = m+1`, and Dickson supplies arbitrarily large `m`. -/
theorem energy_of_dickson_two (H : DicksonTwoPositive) :
    CofinalScoreEnergy := by
  apply energy_iff_cofinal_pass.mpr
  intro K
  obtain ⟨m, hm, h5, h7⟩ :=
    H 6 5 6 7 (by decide) (by decide) (by decide) (by decide)
      dickson_twin_admissible K
  refine ⟨m + 1, by omega, (twin_iff_score_eq_lo (by omega : 1 ≤ m + 1)).mp ?_⟩
  have hlo : twinLo (m + 1) = 6*m + 5 := by unfold twinLo; omega
  have hhi : twinHi (m + 1) = 6*m + 7 := by unfold twinHi; omega
  rw [hlo, hhi]
  exact ⟨h5, h7⟩

end CPNF
