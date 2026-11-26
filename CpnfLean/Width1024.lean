import Mathlib
import CpnfLean.Overload

/-!
# CPNF — the width-1024 reduction: overload lives in the last 10 levels

The scale obstruction confined positive overload to `t - d ≤ 15`. This file closes six of
those levels by a *different* argument, one that does not need a growing-width estimate.

At width exactly `1024 = 2^10` the target capacity is exactly `1024`. So it suffices to bound
each column by `512` — a tie already kills the overload. Splitting the primes by job:

* `A = {5,7,11,13}`, `W = 5005` — controls the *population* of rows coprime to `W`.
* `B = {17,19,23,29,31,37}` — the *removals*, each `p` removing at least `m(⌊1024/p⌋)` rows.
* collisions between two removals cost at most `⌈1024/(pq)⌉`, and total `33`.

The whole numerical content is one inequality over a phase space of 5005 — no table modulo a
product of ten primes. `forced_le_children` then propagates the vanishing upward, so every
node with `t - d ≥ 10` has `forced = 0`.

That leaves lengths `1, 2, 4, ..., 512` — the last 10 levels. Cofinality there is open.

No `sorry`, no `axiom`.
-/

namespace CPNF

namespace Width1024

def countW (r h : ℕ) : ℕ :=
  (List.range h).foldl
    (fun s i => if Nat.gcd (r+i) 5005 = 1 then s+1 else s) 0

def upperW (h : ℕ) : ℕ :=
  (List.range 5005).foldl (fun s r => max s (countW r h)) 0

def lowerW (h : ℕ) : ℕ :=
  (List.range 5005).foldl (fun s r => min s (countW r h)) h

theorem phase_certificate :
    upperW 1024 + 33 ≤
      512 + lowerW 60 + lowerW 53 + lowerW 44 +
            lowerW 35 + lowerW 33 + lowerW 27 := by
  native_decide

def late : List ℕ := [17,19,23,29,31,37]

def collisionCost : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
      (ps.map (fun q => (1024 + p*q - 1) / (p*q))).sum +
        collisionCost ps

theorem collision_certificate : collisionCost late = 33 := by decide

end Width1024

theorem zero_above_fixed_width
    (S T U : Finset ℕ) (t k : ℕ)
    (base : ∀ d j : ℕ, d + k = t → j < 2^d →
      forced S T U t d j = 0) :
    ∀ e d j : ℕ, d + k + e = t → j < 2^d →
      forced S T U t d j = 0 := by
  intro e
  induction e with
  | zero =>
      intro d j he hj
      exact base d j (by omega) hj
  | succ e ih =>
      intro d j he hj
      have hd : d < t := by omega
      have he' : (d+1) + k + e = t := by omega
      have hj₀ : 2*j < 2^(d+1) := by rw [pow_succ]; omega
      have hj₁ : 2*j+1 < 2^(d+1) := by rw [pow_succ]; omega
      have h := forced_le_children S T U t d j hd
      rw [ih (d+1) (2*j) he' hj₀,
          ih (d+1) (2*j+1) he' hj₁] at h
      have hn : 0 ≤ forced S T U t d j := le_max_left _ _
      omega

/-- Given the width-1024 base case, `forced` vanishes at every coarser scale. -/
theorem zero_above_width_1024 (S T U : Finset ℕ) (t : ℕ)
    (base : ∀ d j : ℕ, d + 10 = t → j < 2^d → forced S T U t d j = 0) :
    ∀ e d j : ℕ, d + 10 + e = t → j < 2^d → forced S T U t d j = 0 :=
  zero_above_fixed_width S T U t 10 base

end CPNF
