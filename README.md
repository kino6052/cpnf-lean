# cpnf-lean

CPNF-LEAN is a formalization of the **Computational Prime Number Framework (CPNF)** in Lean 4 (with Mathlib).

**The stance is CPNF-only.** This repository defines its own mathematics. Primality is not assumed as a property of numbers; it is what the certification process decides. Correspondence to conventional number theory (infinitely many primes as a *fact* about a completed set) is deliberately *not* proved here; it is a later, separate step.

Gates in this repo:

1. **The sieve and the process** (`CpnfLean/Sieve.lean`, `CpnfLean/Process.lean`)
2. **The ordinary process, stage by stage** (`CpnfLean/Stage.lean`)

## What is proved

| Fact | Lemma | Meaning |
|---|---|---|
| Every blocker set above 1 has a survivor | `sieve_nonempty` | `(max+1)! + 1` is ≥ 2 and undivided by every blocker. This is CPNF's form of the Euclid argument. |
| Each stage certifies exactly one number | `step_stage` | the least survivor, fixed by the blockers alone |
| Blockers never shrink | `stage_subset_succ`, `stage_subset_of_le` | certification is irreversible |
| The process has no last stage | `always_a_next_step`, `certify_survives` | every stage has a next survivor to certify |

## What is consciously *not* proved

* **Soundness** ("no composite is ever certified"). In CPNF there is no such notion *within* the framework: a certified number is the least survivor. The claim "certified numbers are prime" is a statement about the correspondence between CPNF and the classical integers, and it belongs to a separate layer.
* Twin primes, twin indices, and the endless-chase argument. These are later phases.

## A note on a discarded lemma

An attempt was made to prove "a survivor stays a survivor after one stage". This lemma is **false** (e.g. `n = 9` survives `B = {2}` but not `B = {2,3}`). What is true and proved is the other direction: `sieve_nonempty` and `stage_subset_succ`. A false-but-plausible intermediate is exactly the kind of thing Lean is here for.

## Build

```bash
lake exe cache get
lake build
```

## Paper

Formalization follows *A Computational Framework for Prime Numbers: A Case Study on How Reification and Ontology Affect Prime Infinitude Arguments*, Yong Xue, December 26, 2025.
