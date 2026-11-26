import Mathlib
import CpnfLean.TopBand
import CpnfLean.Progression

/-!
# CPNF — the per-prime top-band bound (rung 3, complete)

The corrected top-band exclusion: a band prime `q` (coprime to the class modulus `M`, and
`q > 3`) divides `twinLo n` or `twinHi n` for at most `2 * ⌈L/q⌉` of the `L` rows of a
residue class, because each of the two signs pins `j` to a single residue class modulo `q`.

Structure:
* `classBlock_eq_progression` — a nonempty class is `{a + M*j : j < L}`;
* `affine_hit_residue` — all hits of `b + c*j` lie in one residue class when `q ∤ c`;
* `per_prime_bound` — the two signs, union bound, and `card_mod_eq_le`.

No prime-distribution estimate: finite progression counting only.
-/

namespace CPNF


theorem classBlock_eq_progression (X M r : ℕ) (hM : 0 < M)
    (h : (classBlock X M r).Nonempty) :
    classBlock X M r =
      (Finset.range (classBlock X M r).card).image
        (fun j => (classBlock X M r).min' h + M * j) := by
  classical
  let S := classBlock X M r
  let a := S.min' h
  let N := (2 * X - a) / M + 1
  let f : ℕ → ℕ := fun j => a + M * j
  change S = (Finset.range S.card).image f

  have memS (n : ℕ) :
      n ∈ S ↔ (X < n ∧ n ≤ 2 * X) ∧ n % M = r := by
    simp only [S, classBlock, blk, Finset.mem_filter, Finset.mem_Ioc]
  have ha : a ∈ S := S.min'_mem h
  obtain ⟨⟨hXa, haX⟩, har⟩ := (memS a).mp ha

  have bound (j : ℕ) : j ∈ Finset.range N ↔ f j ≤ 2 * X := by
    change j ∈ Finset.range ((2 * X - a) / M + 1) ↔ a + M * j ≤ 2 * X
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hM,
      Nat.mul_comm j M]
    omega

  have himg : S = (Finset.range N).image f := by
    ext n
    constructor
    · intro hn
      obtain ⟨⟨_, hnX⟩, hnr⟩ := (memS n).mp hn
      have han : a ≤ n := S.min'_le n hn
      have hquot : a / M ≤ n / M := Nat.div_le_div_right han
      let j := n / M - a / M
      have hj : n / M = a / M + j := by dsimp [j]; omega
      have hn' := Nat.div_add_mod n M
      have ha' := Nat.div_add_mod a M
      rw [hj, Nat.mul_add, hnr] at hn'
      rw [har] at ha'
      have he : f j = n := by change a + M * j = n; omega
      exact Finset.mem_image.mpr
        ⟨j, (bound j).mpr (he ▸ hnX), he⟩
    · intro hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      apply (memS _).mpr
      refine ⟨⟨?_, (bound j).mp hj⟩, ?_⟩
      · change X < a + M * j
        omega
      · change (a + M * j) % M = r
        rw [Nat.add_mod]
        simpa using har

  have hinj : Function.Injective f := by
    intro i j he
    change a + M * i = a + M * j at he
    exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel he)
  have hc : S.card = N := by
    calc
      S.card = ((Finset.range N).image f).card := congrArg Finset.card himg
      _ = (Finset.range N).card := Finset.card_image_of_injective _ hinj
      _ = N := Finset.card_range _
  rw [hc]
  exact himg

/-- All hits of a single affine form lie in one residue class.
    If there are no hits, the returned residue can be zero. -/
private theorem affine_hit_residue (q b c : ℕ) (hq : Nat.Prime q)
    (hc : ¬ q ∣ c) :
    ∃ s : ℕ, ∀ j : ℕ, q ∣ b + c * j → j % q = s := by
  classical
  by_cases hex : ∃ j : ℕ, q ∣ b + c * j
  · let k := Nat.find hex
    have hk : q ∣ b + c * k := Nat.find_spec hex
    refine ⟨k % q, ?_⟩
    intro j hj
    have hkj : k ≤ j := Nat.find_min' hex hj
    let d := j - k
    have he : j = k + d := by dsimp [d]; omega
    have hj' : q ∣ (b + c * k) + c * d := by
      simpa only [he, Nat.mul_add, Nat.add_assoc] using hj
    have hd' : q ∣ c * d := by
      have H := Nat.dvd_sub hj' hk
      simpa using H
    have hd : q ∣ d := (hq.dvd_mul.mp hd').resolve_left hc
    obtain ⟨t, ht⟩ := hd
    rw [he, ht, Nat.add_mod]
    simp
  · exact ⟨0, fun j hj => False.elim (hex ⟨j, hj⟩)⟩

theorem per_prime_bound (X M r q : ℕ) (hM : 0 < M) (hr : r < M)
    (hq : Nat.Prime q) (hq3 : 3 < q) (hcop : Nat.Coprime q M) :
    ((classBlock X M r).filter (fun n => q ∣ twinLo n ∨ q ∣ twinHi n)).card ≤
      2 * (((classBlock X M r).card + q - 1) / q) := by
  classical
  let S := classBlock X M r
  let L := S.card
  let P : ℕ → Prop := fun n => q ∣ twinLo n ∨ q ∣ twinHi n
  change (S.filter P).card ≤ 2 * ((L + q - 1) / q)
  by_cases hs : S.Nonempty
  · let a := S.min' hs
    let f : ℕ → ℕ := fun j => a + M * j
    have hparam : S = (Finset.range L).image f :=
      classBlock_eq_progression X M r hM hs
    have haS : a ∈ classBlock X M r := S.min'_mem hs
    have hXa : X < a :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp haS).1).1
    have h6 : ¬ q ∣ 6 := by
      intro hd
      have hu := Nat.le_of_dvd (by decide : 0 < 6) hd
      interval_cases q <;> norm_num at *
    have hc : ¬ q ∣ 6 * M := by
      intro hd
      exact (hq.coprime_iff_not_dvd.mp hcop) ((hq.dvd_mul.mp hd).resolve_left h6)

    obtain ⟨s, hsLo⟩ := affine_hit_residue q (6 * a - 1) (6 * M) hq hc
    obtain ⟨t, hsHi⟩ := affine_hit_residue q (6 * a + 1) (6 * M) hq hc
    have lo (j : ℕ) : twinLo (f j) = (6 * a - 1) + (6 * M) * j := by
      change 6 * (a + M * j) - 1 = _
      rw [Nat.mul_add, Nat.mul_assoc]
      omega
    have hi (j : ℕ) : twinHi (f j) = (6 * a + 1) + (6 * M) * j := by
      change 6 * (a + M * j) + 1 = _
      ring

    let R (u : ℕ) := (Finset.range L).filter (fun j => j % q = u)
    have sub : S.filter P ⊆ (R s ∪ R t).image f := by
      intro n hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      rw [hparam] at hnS
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hnS
      refine Finset.mem_image.mpr ⟨j, Finset.mem_union.mpr ?_, rfl⟩
      change q ∣ twinLo (f j) ∨ q ∣ twinHi (f j) at hnP
      rcases hnP with hl | hh
      · rw [lo] at hl
        exact Or.inl (Finset.mem_filter.mpr ⟨hj, hsLo j hl⟩)
      · rw [hi] at hh
        exact Or.inr (Finset.mem_filter.mpr ⟨hj, hsHi j hh⟩)

    calc
      (S.filter P).card ≤ ((R s ∪ R t).image f).card := Finset.card_le_card sub
      _ ≤ (R s ∪ R t).card := Finset.card_image_le
      _ ≤ (R s).card + (R t).card := Finset.card_union_le _ _
      _ ≤ ((L + q - 1) / q) + ((L + q - 1) / q) :=
        Nat.add_le_add (card_mod_eq_le q L s hq.pos) (card_mod_eq_le q L t hq.pos)
      _ = 2 * ((L + q - 1) / q) := (two_mul _).symm
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]


end CPNF
