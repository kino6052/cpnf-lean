# Plan

- [x] Repo, Lean toolchain, Mathlib cache
- [x] Sieve operator, survivability, step, advance (`Sieve.lean`, `Process.lean`)
- [x] Stage sequence, determinism, monotonicity, non-termination (`Stage.lean`)
- [ ] Correspondence layer (CPNF ↔ classical integers), separate on purpose
- [x] Twin indices, certification window, admissible indices (`Twin.lean`)
- [x] Twin blockers above 3, twin sieve monotonicity (`TwinProcess.lean`)
- [x] Window grows; a blocker kills a pair only via one of two congruences (`Chase.lean`)
- [x] Twin certification process over stages (`TwinStage.lean`): stage window, search set,
      `min(candidates)`, minimality, admissibility only flows backwards over stages
- [ ] Endless chase refuted: no permanent stagnation
- [ ] Adversarial coverings excluded in CPNF

## Notes on what the chase needs (not yet proved)

- The earlier "a window of length `W` needs at least `W` blockers" claim is **false**:
  one blocker `q` kills about `2W/q` indices, and `{5}` already kills 3 indices in the
  window at `y = 7`. Corrected in the `Chase.lean` header.
- What *is* true and now proved: `window_ge` (`y ≤ W(y)` for `y ≥ 7`), `window_mono`,
  `killed_iff`, and the whole twin stage readout in `TwinStage.lean`.
