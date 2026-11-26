import Mathlib
import CpnfLean.ColumnSplit

/-!
# CPNF — Phase B (weak form): a column mark is a genuine prime

On the block `(N, 2N]` with `N ≥ 16` both members lie in `(N, N²]`, so a mark
`N < (6n±1).minFac` forces the member to be prime: any composite `m ≤ N²` has a factor
`≤ N`, hence `m.minFac ≤ N`.

This is the weak Phase B the plan needs — it converts column marks into primality with
**no** prime number theorem in arithmetic progressions (which Mathlib does not have).
`prime_of_minFac_ge_sqrt` is the arithmetic core, proved from the minimality of `Nat.minFac`.

No `sorry`, no `axiom`.
-/

namespace CPNF
theorem prime_of_minFac_ge_sqrt {m N : ℕ} (hm2 : 2 ≤ m) (h : N < m.minFac) (hN : m ≤ N * N) :
    Nat.Prime m := by
  have hm1 : m ≠ 1 := by omega
  have hp := Nat.minFac_prime hm1
  have hdvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hpos : 0 < m.minFac := hp.pos
  obtain ⟨k, hk⟩ := hdvd
  -- hk : m = m.minFac * k
  -- Step: m <= N*N < m.minFac * m.minFac, while m = m.minFac * k, so k < m.minFac.
  have hNsq : N * N < m.minFac * m.minFac := by
    nlinarith
  have hklt : k < m.minFac := by
    by_contra hc
    push Not at hc
    have : m.minFac * m.minFac ≤ m.minFac * k := Nat.mul_le_mul_left _ hc
    omega
  -- now: m = minFac * k, and if m were composite, minFac < m, so k >= 2, but k < minFac...
  -- Actually we just need: m = minFac * k with minFac prime and 2 <= minFac and k < minFac.
  -- Then k must be 1 (else k has a prime divisor < minFac, contradicting minimality).
  rcases Nat.lt_or_ge 1 k with hk1 | hk1
  · -- 1 < k: k has a divisor >= 2, contradiction with minFac minimality
    have hk2 : 2 ≤ k := hk1
    have hdvdk : Nat.minFac k ∣ k := Nat.minFac_dvd k
    have hkprime : Nat.Prime (Nat.minFac k) := Nat.minFac_prime (by omega)
    have hminle : Nat.minFac k ≤ k := Nat.minFac_le (by omega)
    -- minFac k divides m
    have hdm : Nat.minFac k ∣ m := by
      rw [hk]; exact Dvd.dvd.mul_left hdvdk _
    have := Nat.minFac_le_of_dvd hkprime.two_le hdm
    -- minFac m <= minFac k < minFac m? need minFac k < minFac m
    -- minFac k <= k < m.minFac
    have hlt' : Nat.minFac k < m.minFac := lt_of_le_of_lt hminle hklt
    omega
  · -- k <= 1, and k != 0 (else m = 0)
    have hk0 : k ≠ 0 := by intro h0; rw [h0, Nat.mul_zero] at hk; omega
    have hk1' : k = 1 := by omega
    rw [hk1', Nat.mul_one] at hk
    rw [hk]
    exact hp

theorem twinLo_lt_sq {N n : ℕ} (hn : n ∈ blk N) (h16 : 16 ≤ N) : twinLo n ≤ N * N := by
  have hb := Finset.mem_Ioc.mp hn
  have hn1 : 1 ≤ n := by omega
  have : n ≤ 2 * N := hb.2
  unfold twinLo
  have h6 : 6 * n - 1 ≤ 12 * N := by omega
  nlinarith

theorem twinHi_lt_sq {N n : ℕ} (hn : n ∈ blk N) (h16 : 16 ≤ N) : twinHi n ≤ N * N := by
  have hb := Finset.mem_Ioc.mp hn
  have : n ≤ 2 * N := hb.2
  unfold twinHi
  nlinarith

theorem twinLo_ge {N n : ℕ} (hn : n ∈ blk N) : 2 ≤ twinLo n := by
  have hb := Finset.mem_Ioc.mp hn
  unfold twinLo
  omega

theorem twinHi_ge {N n : ℕ} (hn : n ∈ blk N) : 2 ≤ twinHi n := by
  have hb := Finset.mem_Ioc.mp hn
  unfold twinHi
  omega

/-- A low-column mark is a genuine prime. -/
theorem prime_of_loMark {N n : ℕ} (hn : n ∈ blk N) (h16 : 16 ≤ N)
    (h : N < (twinLo n).minFac) : Nat.Prime (twinLo n) :=
  prime_of_minFac_ge_sqrt (twinLo_ge hn) h (twinLo_lt_sq hn h16)

theorem prime_of_hiMark {N n : ℕ} (hn : n ∈ blk N) (h16 : 16 ≤ N)
    (h : N < (twinHi n).minFac) : Nat.Prime (twinHi n) :=
  prime_of_minFac_ge_sqrt (twinHi_ge hn) h (twinHi_lt_sq hn h16)

end CPNF
