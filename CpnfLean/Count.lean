import Mathlib

/-!
# CPNF — the exact finite count

The density-free count of CPNF's twin sieve over a finite window. Everything here is
finite `ℕ` arithmetic: no logarithms, no Mertens, no analytic input.

A blocker `b` kills an index `n` when `b ∣ 6n-1` or `b ∣ 6n+1`. Since `6` is invertible mod
`b`, killing happens in exactly **two** residue classes mod `b`. That is the whole content of
the count: inclusion–exclusion over the finite blocker set, with the progression count done
in `ℕ` so no truncated subtraction can bite.

Moduli below are always `≥ 5` and coprime to `6`. The blockers `2` and `3` are excluded on
purpose: `2` hits nothing (`6n∓1` are odd) and `3` hits nothing (`6n∓1` are `≠ 0` mod 3), but
the "two residue classes" claim is **false** for them, so they must not enter the count.
-/

namespace CPNF

open scoped BigOperators

/-! ## Definitions -/

/-- Blocker `b` **hits** index `n` when it divides one of the twin members `6n-1`, `6n+1`.
    Written in residue form, because divisibility is what the sieve tests but residue
    classes are what can be counted. -/
def hit (b n : ℕ) : Prop := 6 * n % b = 1 ∨ 6 * n % b = b - 1

instance (b n : ℕ) : Decidable (hit b n) := by
  unfold hit
  infer_instance

/-- The product of a finite set of moduli — the modulus of one residue class after
    combining the blockers in `S` by CRT. -/
def d (S : Finset ℕ) : ℕ := ∏ b ∈ S, b

/-- The residues `r ∈ [1, d S]` that are hit by **every** blocker in `S`. Using the positive
    representative `d S` for the zero class keeps this inside `ℕ`. -/
def T (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (d S)).filter (fun r => ∀ b ∈ S, hit b r)

/-- The number of indices in `[1, W]` hit by every blocker of `S`. Inclusion–exclusion adds
    these with alternating signs. -/
def C (W : ℕ) (S : Finset ℕ) : ℕ := ∑ r ∈ T S, (W + d S - r) / d S

/-- The un-hit indices: the set the twin sieve actually keeps. -/
def G (A : Finset ℕ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter (fun n => ∀ b ∈ A, ¬ hit b n)

/-- The moduli the count is allowed to use: each at least `5`, each coprime to `6`, and
    pairwise coprime. -/
def GoodMods (A : Finset ℕ) : Prop :=
  (∀ b ∈ A, 5 ≤ b ∧ Nat.Coprime 6 b) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)

/-! ## 5b. One progression

The count of a single residue class in `[1, W]`. This is the only place arithmetic on the
window enters; everything after is inclusion–exclusion over finite sets. -/

/-- **One progression.** The indices `n ∈ [1, W]` congruent to `r` mod `D` number
    `(W + D - r) / D`. Written so that `W < r` also works: the window is simply too short. -/
theorem progression_card (W D r : ℕ) (hD : 0 < D) (hr : 1 ≤ r) (hrD : r ≤ D) :
    ((Finset.Icc 1 W).filter (fun n => n % D = r % D)).card = (W + D - r) / D := by
  have hbound (k : ℕ) :
      k ∈ Finset.range ((W + D - r) / D) ↔ D * k + r ≤ W := by
    rw [Finset.mem_range]
    change k.succ ≤ (W + D - r) / D ↔ D * k + r ≤ W
    rw [Nat.le_div_iff_mul_le hD, Nat.succ_mul, Nat.mul_comm k D]
    omega
  symm
  calc
    (W + D - r) / D = (Finset.range ((W + D - r) / D)).card :=
      (Finset.card_range _).symm
    _ = _ := by
      apply Finset.card_bij (fun k _ => D * k + r)
      · intro k hk
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (hbound k).mp hk⟩, ?_⟩
        rw [Nat.add_mod]
        simp
      · intro a ha b hb he
        exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_right_cancel he)
      · intro n hn
        obtain ⟨hI, hm⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn1, hnW⟩ := Finset.mem_Icc.mp hI
        have hz : (n + (D - r)) % D = 0 := by
          rw [Nat.add_mod, hm, ← Nat.add_mod, show r + (D - r) = D by omega,
            Nat.mod_self]
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hz
        cases q with
        | zero =>
          rw [Nat.mul_zero] at hq
          omega
        | succ k =>
          rw [Nat.mul_succ] at hq
          have he : D * k + r = n := by omega
          exact ⟨k, (hbound k).mpr (he ▸ hnW), he⟩

end CPNF
