import Mathlib
import CpnfLean.Head
import CpnfLean.Correspondence

/-!
# CPNF — the coverage layer

We attack the twin conjecture through a **coverage** argument rather than parity: an
"endless chase" would be an infinite supply of head deaths whose killers are all *proper
factors*, never themselves members. Two things are established here, both without any
density argument and without any asymptotic estimate:

* **The score is unbounded** (`score_unbounded`), by an explicit factorial witness: at
  `n = (h+1)!`, every `d ≤ h` divides `6n`, so both members `6n ± 1` evade all of them at
  once, and the least prime factor of each exceeds `h`. This is the elementary "the process
  never gets stuck in *endurance*" theorem. It does **not** produce a twin pair.

* **The wall** (`head_le_of_factor`): a head with a factor `q` at or below a cutoff `t`
  is itself at most `t`. Contrapositive: a head that escapes `t` has *no* factor `≤ t`,
  which for `t ≥ √(6n+1)` leaves nothing but the members themselves. That is exactly the
  point where coverage reasoning stops and twindom begins.

Neither theorem decides the conjecture, and none is claimed to. The first is the strongest
density-free progress available; the second localises precisely what remains.
-/

namespace CPNF

/-! ## Divisibility of `m + 1` and `m - 1` -/

/-- If `d ≥ 2` divides `m`, it does not divide `m + 1`. -/
theorem not_dvd_succ_of_dvd {m d : ℕ} (hd2 : 2 ≤ d) (hd : d ∣ m) : ¬ d ∣ m + 1 := by
  intro h
  have h1 : d ∣ m + 1 - m := Nat.dvd_sub h hd
  rw [Nat.add_sub_cancel_left] at h1
  have := Nat.dvd_one.mp h1
  omega

/-- If `d ≥ 2` divides positive `m`, it does not divide `m - 1`. -/
theorem not_dvd_pred_of_dvd {m d : ℕ} (hd2 : 2 ≤ d) (hd : d ∣ m) (hm : 1 ≤ m) :
    ¬ d ∣ m - 1 := by
  intro h
  have h1 : d ∣ m - (m - 1) := Nat.dvd_sub hd h
  rw [show m - (m - 1) = 1 by omega] at h1
  have := Nat.dvd_one.mp h1
  omega

/-- If `d ≥ 2` divides `m`, it does not divide `m + c` for `0 < c < d`. -/
theorem not_dvd_add_of_dvd {m d c : ℕ} (hd : d ∣ m) (hc0 : 0 < c) (hcd : c < d) :
    ¬ d ∣ m + c := by
  intro h
  have hc : d ∣ c := by
    have := Nat.dvd_sub h hd
    rwa [Nat.add_sub_cancel_left] at this
  have := Nat.le_of_dvd hc0 hc
  omega

/-! ## The factorial witness -/

/-- **Both members at `n = (h+1)!` evade every `d` with `2 ≤ d ≤ h`.** Every such `d`
    divides `(h+1)!`, hence divides `6n`, so `6n ∓ 1` differ from a multiple of `d` by one
    and are not divisible by `d`. -/
theorem evades {h d : ℕ} (hd2 : 2 ≤ d) (hdh : d ≤ h) :
    ¬ d ∣ twinLo (h + 1).factorial ∧ ¬ d ∣ twinHi (h + 1).factorial := by
  have hdvd : d ∣ 6 * (h + 1).factorial :=
    dvd_mul_of_dvd_right (Nat.dvd_factorial (by omega) (by omega)) 6
  have hhi : twinHi (h + 1).factorial = 6 * (h + 1).factorial + 1 := rfl
  have hlo : twinLo (h + 1).factorial = 6 * (h + 1).factorial - 1 := rfl
  have hpos : 1 ≤ 6 * (h + 1).factorial := by
    have := Nat.factorial_pos (h + 1)
    nlinarith
  exact ⟨by rw [hlo]; exact not_dvd_pred_of_dvd hd2 hdvd hpos,
         by rw [hhi]; exact not_dvd_succ_of_dvd hd2 hdvd⟩

/-- **A number with no divisor in `[2, h]` has least prime factor above `h`.** -/
theorem minFac_gt_of_no_small_dvd {m h : ℕ} (hm : 2 ≤ m)
    (hdiv_le : ∀ d, 2 ≤ d → d ≤ h → ¬ d ∣ m) : h < Nat.minFac m := by
  by_contra hcon
  push Not at hcon
  have hdvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have h2 : 2 ≤ Nat.minFac m := (Nat.minFac_prime (by omega)).two_le
  exact hdiv_le (Nat.minFac m) h2 hcon hdvd

/-- **The least prime factor is unbounded** — no density, no asymptotics, one witness. -/
theorem minFac_unbounded (h : ℕ) : ∃ m, h < Nat.minFac m := by
  refine ⟨twinLo (h + 1).factorial, ?_⟩
  apply minFac_gt_of_no_small_dvd
  · unfold twinLo
    have := Nat.factorial_pos (h + 1)
    omega
  · intro d hd2 hdh hdiv
    exact (evades hd2 hdh).1 hdiv

/-- **The score is unbounded.** For any `h` there is an index `n` whose score exceeds `h`. -/
theorem score_unbounded (h : ℕ) : ∃ n, h < score n := by
  refine ⟨(h + 1).factorial, ?_⟩
  have hlo : h < Nat.minFac (twinLo (h + 1).factorial) := by
    apply minFac_gt_of_no_small_dvd
    · unfold twinLo
      have := Nat.factorial_pos (h + 1)
      omega
    · intro d hd2 hdh hdiv
      exact (evades hd2 hdh).1 hdiv
  have hhi : h < Nat.minFac (twinHi (h + 1).factorial) := by
    apply minFac_gt_of_no_small_dvd
    · unfold twinHi
      have := Nat.factorial_pos (h + 1)
      omega
    · intro d hd2 hdh hdiv
      exact (evades hd2 hdh).2 hdiv
  have hsc : score ((h + 1).factorial) = min (Nat.minFac (twinLo (h + 1).factorial)) (Nat.minFac (twinHi (h + 1).factorial)) := rfl
  rw [hsc]
  exact lt_min hlo hhi

/-! ## The wall -/

/-- **A factor of a member below the cutoff puts the score below the cutoff.** -/
theorem minFac_le_of_tail {n t q : ℕ} (hq2 : 2 ≤ q) (htq : q ≤ t) (hdiv : q ∣ twinLo n) :
    score n ≤ t := by
  have h : score n ≤ (twinLo n).minFac := min_le_left _ _
  have h3 : (twinLo n).minFac ≤ q := Nat.minFac_le_of_dvd hq2 hdiv
  exact le_trans h (le_trans h3 htq)

/-- **The wall.** A head whose lower member has a factor `q ≤ t` is itself at most `t`.
    Contrapositive: a head escaping `t` has *no* factor `≤ t` — for `t ≥ √(6n+1)` that
    leaves only the members themselves. Coverage reasoning stops exactly here. -/
theorem head_le_of_factor {k t q : ℕ} (hlo : twinLo (head k) ≤ score (head k))
    (hq2 : 2 ≤ q) (hqt : q ≤ t) (hdiv : q ∣ twinLo (head k)) : head k ≤ t := by
  have h1 : score (head k) = twinLo (head k) := score_eq_lo_of_row (one_le_head k) hlo
  have h2 : twinLo (head k) ≤ t := h1 ▸ minFac_le_of_tail hq2 hqt hdiv
  unfold twinLo at h2
  omega


/-! ## The window characterisation: the exact interval-hitting instance needed -/

/-- `n` lies inside the certification window at `h` exactly when `6n + 1 ≤ h²`. -/
theorem le_window_iff {n h : ℕ} (hh : 1 ≤ h) : n ≤ window h ↔ 6 * n + 1 ≤ h * h := by
  unfold window
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 6)]
  have e : h ^ 2 = h * h := by ring
  rw [e]
  have c : n * 6 = 6 * n := by ring
  rw [c]
  have hpos : 1 ≤ h * h := Nat.one_le_iff_ne_zero.mpr (by positivity)
  constructor <;> intro h1 <;> omega

/-- **A score-witness inside the window is a twin pair.** This is the forward half of the
    equivalence: the square test fires as soon as `score` clears `h` while the index is
    still under `W(h)`. -/
theorem twin_of_window_witness {n h : ℕ} (hn1 : 1 ≤ n) (hh : 1 ≤ h)
    (hnw : n ≤ window h) (hsc : h < score n) :
    Nat.Prime (twinLo n) ∧ Nat.Prime (twinHi n) := by
  apply (twin_iff_sq_test hn1).mpr
  unfold twinHi
  have h1 : 6 * n + 1 ≤ h * h := (le_window_iff hh).mp hnw
  have h2 : h * h < score n * score n := Nat.mul_lt_mul'' hsc hsc
  omega

/-- **Every twin pair sits inside the window at `h = 6n - 2`**, with score `6n - 1 > h`.
    This is the reverse half: twins are exactly the window witnesses. -/
theorem window_witness_of_twin {n : ℕ} (hn : 1 ≤ n) (hp : Nat.Prime (twinLo n))
    (hq : Nat.Prime (twinHi n)) :
    ∃ h, 1 ≤ h ∧ n ≤ window h ∧ h < score n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hge : 1 ≤ 6 * (k + 1) - 2 := by omega
  refine ⟨6 * (k + 1) - 2, hge, ?_, ?_⟩
  · rw [le_window_iff hge]
    have h : 6 * (k + 1) - 2 = 6 * k + 4 := by omega
    rw [h]
    have e : (6 * k + 4) * (6 * k + 4) = 36 * k * k + 48 * k + 16 := by ring
    rw [e]; omega
  · have hsc : score (k + 1) = twinLo (k + 1) :=
      (twin_iff_score_eq_lo (by omega)).mp ⟨hp, hq⟩
    rw [hsc]
    unfold twinLo
    omega

/-- A score-witness in the window beyond `K`.  The frontier's **boxed** condition: it is
    the exact instance of interval hitting that CPNF needs, and no stronger one. -/
def WindowWitness (K : ℕ) : Prop :=
  ∃ h n, 1 ≤ h ∧ 1 ≤ n ∧ K ≤ n ∧ n ≤ window h ∧ h < score n

/-- **The boxed equivalence.** A window witness beyond every bound is *equivalent* to
    cofinally many direct deaths — hence to unbounded twin primes, via
    `oftenDirect_iff_unboundedTwins`.

    This is the sharpest honest statement we have: it says exactly which interval must
    contain a score-witness (bounded by `W(h) = (h²-1)/6`, beyond `K`), and nothing more.
    It is *not* progress on the conjecture — both sides remain open. -/
theorem windowWitness_iff_oftenDirect : (∀ K, WindowWitness K) ↔ OftenDirect := by
  constructor
  · intro H K
    obtain ⟨h, n, hh, hn1, hKn, hnw, hsc⟩ := H K
    obtain ⟨hp, hq⟩ := twin_of_window_witness hn1 hh hnw hsc
    obtain ⟨k, hd, hk⟩ := direct_of_twin hn1 hp hq
    exact ⟨k, hKn.trans (le_of_eq hk.symm), hd⟩
  · intro H K
    obtain ⟨k, hk, hd⟩ := H K
    have hn1 : 1 ≤ head k := one_le_head k
    have hp := prime_of_direct hd
    obtain ⟨h, hh, hnw, hsc⟩ := window_witness_of_twin hn1 hp.1 hp.2
    exact ⟨h, head k, hh, hn1, hk, hnw, hsc⟩

end CPNF
