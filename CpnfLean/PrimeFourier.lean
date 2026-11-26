import Mathlib

/-!
# CPNF — the circle-method route, and where it stops

The prime exponential sum `S_X(α) = Σ_{p∈(X,2X]} log p · e(pα)` carries the twin correlation as
its second Fourier coefficient: `∫ |S_X|² e(-2α) dα = Σ log p log(p+2)` over twin pairs. The
frontier's analysis:

* **Major arcs** (denominators `q ≤ (log X)^40`) give the *right signed mass*: `M_X(2) = (s+o(1))X`
  with `s = 2∏_{l>2}(1 - 1/(l-1)²) = 1.32032…`, via Siegel–Walfisz. This is unconditional.
* **Minor arcs**: Vaughan's bound gives `∫_𝔪 |S_X|⁴ ≪ X³/(log X)^31`, so `|E_X(h)| > X/log X` at
  only `O(X/(log X)^29)` shifts `h`. This is an unconditional *average* theorem.
* **The obstruction**: nothing in the average excludes the fixed shift `h = 2`. What must cancel
  there is `∫_𝔪 |S_X(α)|² cos(4πα) dα` — the binary Hardy–Littlewood prime-pair obstruction in
  circle-method form. With no spare factor to dominate, the method stalls at the twin conjecture
  itself.

What is formalized here is the *finite* link: positive pair-mass is literally a twin pair. The
analytic estimates (major-arc asymptotic, Vaughan's bound) are named inputs, not axioms, in the
accompanying note. No `sorry`, no `axiom`.
-/

namespace CPNF.PrimeFourier
open scoped BigOperators

def primesIn (X : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter Nat.Prime

noncomputable def primeSum (X : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ primesIn X, (Real.log (p : ℝ) : ℂ) * z ^ p

noncomputable def pairMass (X h : ℕ) : ℝ :=
  ∑ p ∈ primesIn X,
    if p + h ∈ primesIn X then
      Real.log (p : ℝ) * Real.log ((p + h : ℕ) : ℝ)
    else 0

theorem exists_pair_of_pos {X h : ℕ} (H : 0 < pairMass X h) :
    ∃ p ∈ primesIn X, p + h ∈ primesIn X := by
  by_contra hn
  have hz : pairMass X h = 0 := by
    unfold pairMass
    apply Finset.sum_eq_zero
    intro p hp
    have hpp : p + h ∉ primesIn X := fun hph => hn ⟨p, hp, hph⟩
    simp [hpp]
  rw [hz] at H
  exact (lt_irrefl _ H)

end CPNF.PrimeFourier
