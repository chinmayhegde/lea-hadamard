# lea-hadamard

Blueprint-driven autonomous formalization of Damek Davis's
[*Counting partial Hadamard matrices in the cubic regime*](https://arxiv.org/abs/2603.30013)
(arXiv:2603.30013, 2026), driven by [Lea](https://github.com/chinmayhegde/lea-prover).

## What this project does

Davis's paper proves a first-order asymptotic expansion for the number of
`n × 4t` partial Hadamard matrices in the regime `t ≥ C₀ n³`. He has
[a complete Lean formalization](https://github.com/damek/counting_hadamard)
(~46k lines, 0 sorries, AI-assisted).

This project asks: can a blueprint-driven dispatcher automate the same
formalization using Lea-prover? Concretely:

1. Parse a blueprint (LaTeX with `\lean{}`, `\uses{}`, `\leanok` annotations)
   into a dependency DAG of theorems.
2. Topologically sort. For each leaf without `\leanok`, dispatch Lea on a
   prompt constructed from the statement plus already-proven prerequisites.
3. Validate Lea's output with `lake build`. Mark `\leanok` on success;
   retry / escalate on failure.
4. Track progress, cost, and trust surface (`#print axioms`).

The endpoint deliverable is a Lean formalization of the paper's main theorem
that builds clean and depends only on the standard Mathlib axiom base
(`propext`, `Classical.choice`, `Quot.sound`).

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
- [damek/counting_hadamard](https://github.com/damek/counting_hadamard) — Davis's Lean formalization (used as reference oracle, not copied).
- [Lea-prover](https://github.com/chinmayhegde/lea-prover) — the agent driving formalization.
