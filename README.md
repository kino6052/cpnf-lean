# cpnf-lean

CPNF-LEAN is a formalization of the **Computational Prime Number Framework (CPNF)** in Lean 4 (with Mathlib).

**The stance is CPNF-only.** This repository defines its own mathematics. Primality is not assumed as a property of numbers; it is what the certification process decides. Correspondence to conventional number theory (infinitely many primes as a *fact* about a completed set) is deliberately *not* proved here; it is a later, separate step.

Gates in this repo:

1. **The sieve and the process** (`CpnfLean/Sieve.lean`, `CpnfLean/Process.lean`)
2. **The ordinary process, stage by stage** (`CpnfLean/Stage.lean`)
3. **Twin indices and the certification window** (`CpnfLean/Twin.lean`, `CpnfLean/TwinProcess.lean`)
4. **The twin process as a readout of the stages** (`CpnfLean/TwinStage.lean`)
5. **The chase, as far as it honestly goes** (`CpnfLean/Chase.lean`)

## What is proved

| Fact | Lemma | Meaning |
|---|---|---|
| Every blocker set above 1 has a survivor | `sieve_nonempty` | `(max+1)! + 1` is ≥ 2 and undivided by every blocker. This is CPNF's form of the Euclid argument. |
| Each stage certifies exactly one number | `step_stage` | the least survivor, fixed by the blockers alone |
| Blockers never shrink | `stage_subset_succ`, `stage_subset_of_le` | certification is irreversible |
| The process has no last stage | `always_a_next_step`, `certify_survives` | every stage has a next survivor to certify |
| The window bounds the pair | `window_bound` | `6n + 1 ≤ y²` for every index inside the window |
| The window is at least `y` long | `window_ge` | for `y ≥ 7`, `y ≤ W(y)`: the window grows |
| The window grows with the blockers | `window_mono` | monotone in the largest blocker |
| A blocker kills a pair only via one of its members | `killed_iff` | at most two residue classes per blocker |
| A certification meets both search conditions | `certifiedAt_spec` | admissible for stage `k`, and inside the window |
| The search takes the least candidate | `certifiedAt_least` | `min(candidates)`, as in Algorithm 2 |
| Admissibility flows *backwards* over stages | `admissible_of_stage_le` | more blockers means fewer admissible indices |

## What is consciously *not* proved

* **Soundness** ("no composite is ever certified"). In CPNF there is no such notion *within* the framework: a certified number is the least survivor. The claim "certified numbers are prime" is a statement about the correspondence between CPNF and the classical integers, and it belongs to a separate layer.
* **Irreversibility in the paper's strong form.** Lemma 9 says a certified index "remains certified". That is true for the *record* of certification, but not for admissibility: a later blocker can divide the index's pair, so it stops being admissible. The file proves the honest direction (`admissible_of_stage_le`) and does not dress the other one up.
* **The endless chase.** No permanent stagnation is *not* proved. It is the open part.
* **A counting argument.** An earlier draft of `Chase.lean` claimed a window of length `W` needs at least `W` blockers. That is false — one blocker `q` kills about `2W/q` indices, and `{5}` alone kills 3 of the 8 indices in the window at `y = 7`. The claim is gone from the file.

## A note on a discarded lemma

Three plausible intermediates turned out to be **false**, and Lean refused each one until the mathematics was corrected:

| Claim that failed | Counterexample |
|---|---|
| "a survivor stays a survivor after one stage" | `n = 9` survives `B = {2}` but not `B = {2,3}` |
| "admissible ⇒ `2 ∉ B`" | survival is a *negative* condition; a non-dividing blocker is harmless |
| "`y² - 1 ≤ 6y`", i.e. the window is shorter than `y` | fails at `y = 7`: `48 > 42` |

The last one matters most: it was assumed while building a window-versus-blocker comparison, and `omega` refused it roughly a dozen times before the arithmetic was checked by hand. The true statement is the reverse (`window_ge`), and the counting argument built on the false version is wrong, not merely unproved. This is the case Lean's gate is for.

## Build

```bash
lake exe cache get
lake build
```

## Paper

Formalization follows *A Computational Framework for Prime Numbers: A Case Study on How Reification and Ontology Affect Prime Infinitude Arguments*, Yong Xue, December 26, 2025.
