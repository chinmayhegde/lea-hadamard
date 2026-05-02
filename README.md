# lea-hadamard

Blueprint-driven autonomous formalization of Damek Davis's
[*Counting partial Hadamard matrices in the cubic regime*](https://arxiv.org/abs/2603.30013)
(arXiv:2603.30013, 2026), driven by [Lea](https://github.com/chinmayhegde/lea-prover).


## Status

Step 1: infrastructure scaffold. Lake project skeleton (Lean v4.28.0 +
Mathlib v4.28.0, matching Davis). Blueprint parser in `tools/`. Sample
blueprint chapter in `blueprint/src/` for parser smoke-testing.

## Layout

- `LeaHadamard/` — Lean modules (grows as formalization proceeds).
- `LeaHadamard.lean` — package entrypoint.
- `blueprint/src/` — blueprint LaTeX source (statements + dependency graph).
- `tools/` — Python tooling (parser, dispatcher, status tracker).
- `runs/` — Lea dispatch logs (gitignored).

## References

- Davis, *Counting partial Hadamard matrices in the cubic regime*, arXiv:2603.30013 (2026).
- [damek/counting_hadamard](https://github.com/damek/counting_hadamard) — Davis's Lean formalization (used as reference oracle, not used in our runs).
- [Lea-prover](https://github.com/chinmayhegde/lea-prover) — the agent driving formalization.
