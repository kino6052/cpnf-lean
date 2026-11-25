import Mathlib
import CpnfLean.TwinStage
import CpnfLean.Chase

/-!
# CPNF — the head, and where it dies

We drop the window. `head k` is the least *positive* index admissible for `stage k`,
with no upper bound. Unlike a window witness it always exists: `(maxBlocker k)!` is
admissible at stage `k`, since every blocker divides that factorial, hence `6 * n!`,
and so cannot divide either neighbour `6n - 1`, `6n + 1`.

`head` is monotone, and it can only move when the newly certified blocker divides one
of the two members — a *death*. The interesting case is when that killer is the member
itself rather than a proper divisor; that case is `Direct k`.

Nothing in this file uses `Nat.Prime`.
-/

namespace CPNF

/-! ## Existence -/

/-- Every blocker divides `(maxBlocker k)!`; since `2 ≤ p` it is a valid factorial
    factor, and it is at most the maximum. -/
theorem blocker_dvd_factorial {k p : ℕ} (hp : p ∈ stage k) :
    p ∣ (maxBlocker k).factorial :=
  Nat.dvd_factorial (by have := above_one_stage k p hp; omega)
    (Finset.le_sup (f := id) hp)

/-- **The factorial index is always admissible.** Every blocker divides `6 * (maxBlocker k)!`,
    so it cannot divide either neighbour. This is why the window is not needed for `head`
    to exist — CPNF always has *some* admissible index, it just is not always in the window. -/
theorem admissible_factorial (k : ℕ) : Admissible (stage k) ((maxBlocker k).factorial) := by
  constructor <;> intro p hp hdiv <;> simp only [twinLo, twinHi] at hdiv
  · -- Lower member: `p ∣ 6n` and `p ∣ 6n - 1` force `p ∣ 1`.
    have h6 : p ∣ 6 * (maxBlocker k).factorial := Dvd.dvd.mul_left (blocker_dvd_factorial hp) 6
    have hsub : p ∣ 6 * (maxBlocker k).factorial - (6 * (maxBlocker k).factorial - 1) :=
      Nat.dvd_sub h6 hdiv
    have hone : 6 * (maxBlocker k).factorial - (6 * (maxBlocker k).factorial - 1) = 1 := by
      have := Nat.factorial_pos (maxBlocker k)
      omega
    rw [hone] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hsub
    have := above_one_stage k p hp
    omega
  · -- Upper member: `p ∣ 6n` and `p ∣ 6n + 1` force `p ∣ 1`.
    have h6 : p ∣ 6 * (maxBlocker k).factorial := Dvd.dvd.mul_left (blocker_dvd_factorial hp) 6
    have hsub : p ∣ 6 * (maxBlocker k).factorial + 1 - 6 * (maxBlocker k).factorial :=
      Nat.dvd_sub hdiv h6
    have hone : 6 * (maxBlocker k).factorial + 1 - 6 * (maxBlocker k).factorial = 1 := by omega
    rw [hone] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hsub
    have := above_one_stage k p hp
    omega

/-- There is always a positive admissible index — no window hypothesis needed. -/
theorem exists_admissible (k : ℕ) : ∃ n : ℕ, 1 ≤ n ∧ Admissible (stage k) n :=
  ⟨(maxBlocker k).factorial, Nat.factorial_pos _, admissible_factorial k⟩

/-! ## The head -/

/-- `head k`: the least positive index admissible for `stage k`. This is the window-free
    witness; it exists at every stage (`exists_admissible`). -/
noncomputable def head (k : ℕ) : ℕ := Nat.find (exists_admissible k)

/-- The defining properties of `head`: it is positive and admissible. -/
theorem head_spec (k : ℕ) : 1 ≤ head k ∧ Admissible (stage k) (head k) :=
  Nat.find_spec (exists_admissible k)

/-- `head` is the *least* such index. -/
theorem head_le {k n : ℕ} (hn : 1 ≤ n) (h : Admissible (stage k) n) : head k ≤ n :=
  Nat.find_min' (exists_admissible k) ⟨hn, h⟩

/-- The head is positive. -/
theorem one_le_head (k : ℕ) : 1 ≤ head k := (head_spec k).1

/-- The head is admissible at its own stage. -/
theorem head_admissible (k : ℕ) : Admissible (stage k) (head k) := (head_spec k).2

/-! ## Monotonicity of the head -/

/-- The head never decreases: surviving more blockers is harder. -/
theorem head_mono {j k : ℕ} (hjk : j ≤ k) : head j ≤ head k := by
  apply head_le
  · exact one_le_head k
  · exact admissible_of_stage_le hjk (head_admissible k)

/-! ## The certified numbers strictly increase -/

/-- A survivor of the next stage other than the new blocker was already a survivor. -/
theorem survives_of_succ {k n : ℕ} (h : n ∈ sieve (stage (k + 1))) (hne : n ≠ certify k) :
    n ∈ sieve (stage k) := by
  obtain ⟨h2, hs⟩ := h
  refine ⟨h2, fun p hp => hs p ?_⟩
  rw [stage_succ]
  exact Finset.mem_insert_of_mem hp

/-- Each certified number is strictly bigger than the last: the old one is now a blocker. -/
theorem certify_strict (k : ℕ) : certify k < certify (k + 1) := by
  -- The new survivor is at least the old one, and cannot be equal.
  have hne : certify (k + 1) ≠ certify k := by
    intro he
    have hsurv := certify_survives (k + 1)
    rw [he] at hsurv
    exact hsurv.2 (certify k) (by rw [stage_succ]; exact Finset.mem_insert_self _ _) (dvd_refl _)
  have hge : certify k ≤ certify (k + 1) :=
    next_le k (certify (k + 1)) (survives_of_succ (certify_survives (k + 1)) hne)
  omega

/-- The stage index is at most the certified number. -/
theorem certify_ge_idx (k : ℕ) : k ≤ certify k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => have := certify_strict k; omega

/-! ## The head escapes every bound -/

/-- **Escape.** At some stage after `K`, the head is strictly bigger than `head K`.
    The witness stage is `max K (twinLo (head K) + 1)`: by then the lower member of the
    old head is at most `certify j`, so it can no longer be the least survivor. -/
theorem head_escapes (K : ℕ) : head K < head (max K (twinLo (head K) + 1)) := by
  set m := twinLo (head K) with hm
  set j := max K (m + 1) with hj
  have hKj : K ≤ j := le_max_left _ _
  have hle : head K ≤ head j := head_mono hKj
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · -- If they were equal, `m` would survive stage `j`, forcing `certify j ≤ m < j ≤ certify j`.
    exfalso
    have hadm : Admissible (stage j) (head j) := head_admissible j
    rw [← heq] at hadm
    have hsurv : Survives (stage j) m := by rw [hm]; exact hadm.1
    have hm2 : 2 ≤ m := by
      rw [hm]; simp only [twinLo]; have := one_le_head K; omega
    have hmem : m ∈ sieve (stage j) := ⟨hm2, hsurv⟩
    have hcle := next_le j m hmem
    have := certify_ge_idx j
    omega

/-! ## Death -/

/-- The head **dies** at stage `k` when it stops being admissible: the new blocker has
    killed it. This is the only way the head can move. -/
def Dies (k : ℕ) : Prop := head k < head (k + 1)

/-- The head dies **directly** when the killing blocker is one of the two members itself,
    rather than a proper divisor of one. This is the residual case. -/
def Direct (k : ℕ) : Prop :=
  certify k = twinLo (head k) ∨ certify k = twinHi (head k)

/-- **Deaths happen arbitrarily late.** After any `K` there is a stage whose head is still
    `head K` and dies there — the predecessor of the first stage whose head has escaped. -/
theorem next_death (K : ℕ) : ∃ k, K ≤ k ∧ Dies k ∧ head k = head K := by
  -- The first stage after `K` whose head has strictly escaped.
  have hex : ∃ j, head K < head j := ⟨max K (twinLo (head K) + 1), head_escapes K⟩
  set j₀ := Nat.find hex with hj₀def
  have hj₀P : head K < head j₀ := Nat.find_spec hex
  have hj₀min : ∀ j, j < j₀ → ¬ (head K < head j) := fun j hj => Nat.find_min hex hj
  -- `j₀` is at least `K`.
  have hj₀ge : K ≤ j₀ := by
    rcases Nat.lt_or_ge j₀ K with h | h
    · exact absurd (head_mono (le_of_lt h)) (not_le.mpr hj₀P)
    · exact h
  -- `j₀` is nonzero: otherwise `head K < head 0 ≤ head K`.
  have hj₀ne : j₀ ≠ 0 := by
    intro h0
    rw [h0] at hj₀P
    have hle : head 0 ≤ head K := head_mono (Nat.zero_le K)
    omega
  obtain ⟨k, hk⟩ : ∃ k, j₀ = k + 1 := ⟨j₀ - 1, by omega⟩
  have hklt : k < j₀ := by omega
  -- `K` is strictly below `j₀`, since equality would give `head K < head K`.
  have hKlt : K < j₀ := by
    rcases lt_or_eq_of_le hj₀ge with h | h
    · exact h
    · exact absurd (h ▸ hj₀P) (lt_irrefl _)
  have hKk : K ≤ k := by omega
  -- The head at `k` is still the old one, because `k < j₀`.
  have hhead : head k = head K := by
    have h1 : head K ≤ head k := head_mono hKk
    have h2 : ¬ (head K < head k) := hj₀min k hklt
    omega
  refine ⟨k, hKk, ?_, hhead⟩
  -- Rewrite the death into `head K < head j₀`.
  rw [Dies, hhead, ← hk]
  exact hj₀P

/-- **What a death means.** The head dies exactly when the newly certified blocker divides
    one of the two members of the old head. -/
theorem dies_iff (k : ℕ) : Dies k ↔ certify k ∣ twinLo (head k) ∨ certify k ∣ twinHi (head k) := by
  constructor
  · -- A death means the old head is no longer admissible; only the new blocker is new.
    intro hd
    by_contra hcon
    push Not at hcon
    have hstill : Admissible (stage (k + 1)) (head k) := by
      constructor
      · intro p hp hdiv
        rw [stage_succ] at hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hcon.1 hdiv
        · exact (head_admissible k).1 p hp hdiv
      · intro p hp hdiv
        rw [stage_succ] at hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hcon.2 hdiv
        · exact (head_admissible k).2 p hp hdiv
    -- Then the new head is at most the old one, contradicting the death.
    have := head_le (one_le_head k) hstill
    simp only [Dies] at hd
    omega
  · -- A divisor of a member kills the old head, so the head must move up.
    intro hdiv
    simp only [Dies]
    have hnot : ¬ Admissible (stage (k + 1)) (head k) := by
      intro hadm
      rcases hdiv with h | h
      · exact hadm.1 (certify k) (by rw [stage_succ]; exact Finset.mem_insert_self _ _) h
      · exact hadm.2 (certify k) (by rw [stage_succ]; exact Finset.mem_insert_self _ _) h
    -- The new head is admissible at the old stage too, so it is at least the old head.
    have hle : head k ≤ head (k + 1) :=
      head_le (one_le_head (k + 1))
        (admissible_of_stage_le (Nat.le_succ k) (head_admissible (k + 1)))
    have hne : head k ≠ head (k + 1) := by
      intro he
      exact hnot (he ▸ head_admissible (k + 1))
    omega


/-- **Transport to a death.** A positive witness in the search at stage `K` is not lost by
    looking only at death stages: there is a later stage `k` where the head is still `head K`,
    it dies at `k`, and it is admissible for `stage k` — so it lies in the search there too.

    The window is what makes this work: the old witness bound `head K` by `stageWindow K`,
    and the window only grows, so the same head still fits the later window. -/
theorem transport_to_death {K n : ℕ} (hn : 1 ≤ n) (hs : n ∈ searchSet K) :
    ∃ k, K ≤ k ∧ Dies k ∧ head k = head K ∧ head k ∈ searchSet k := by
  obtain ⟨hadm, hwin⟩ := hs
  -- The head is no bigger than this witness.
  have hheadle : head K ≤ n := head_le hn hadm
  -- The window grows with the blocker set.
  obtain ⟨k, hKk, hdies, hheq⟩ := next_death K
  have hstep : stage K ⊆ stage k := stage_subset_of_le hKk
  have hmax : maxBlocker K ≤ maxBlocker k := by
    simp only [maxBlocker]
    exact Finset.sup_le (fun a ha => Finset.le_sup (f := id) (hstep ha))
  have hw : stageWindow K ≤ stageWindow k := by
    simp only [stageWindow]
    exact window_mono hmax
  -- Write every remaining fact at the later head `head k`.
  have hw2 : head K ≤ stageWindow k := le_trans (le_trans hheadle hwin) hw
  have hWk : head k ≤ stageWindow k := hheq ▸ hw2
  have hAk : Admissible (stage k) (head k) := head_admissible k
  exact ⟨k, hKk, hdies, hheq, hAk, hWk⟩

end CPNF
