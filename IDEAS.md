# IDEAS

Strategy and open decisions for blueprint-driven autonomous formalization.

## Active goal

Formalize Davis's main theorem (Theorem 1.1 of arXiv:2603.30013) in Lean
v4.28.0 + Mathlib v4.28.0, driven autonomously by Lea via a blueprint
dispatcher. End state: `lake build` clean, zero `sorry`, axiom base limited
to `propext`/`Classical.choice`/`Quot.sound`.

## Architectural pattern

**Blueprint as spec; Lea as worker; lake as verifier.** Three-layer split:

1. **Blueprint (LaTeX, human-authored)** — declares each theorem with its
   statement, `\lean{name}`, `\uses{...}`, optional sketch.
2. **Dispatcher (Python)** — parses blueprint, topologically sorts, generates
   per-lemma Lea prompts, manages retries, tracks status.
3. **Lea (existing agent)** — proves each lemma given statement + already-proven
   dependencies + Mathlib search access.

The dispatcher never modifies Lean code directly. Lea's tools (`write_file`,
`edit_file`, `lean_check`) are the only way Lean files change. The
dispatcher's role is orchestration, not authorship.

## Why this shape

For [35,10,13] code search, the bottleneck was combinatorial (SAT-shaped).
Lea added little. For paper formalization, the bottleneck is *proof-shaped*:
many small-to-medium Lean proofs with clear statements and dependencies.
That's exactly Lea's strength.

## Phasing

- **Step 1 (scaffold)** — Lake project, blueprint parser, sample blueprint
  chapter for smoke-testing. *Done when* the parser emits a valid DAG from
  a sample TeX file.
- **Step 2 (dispatcher MVP)** — per-lemma prompt generator, single-lemma
  dispatch loop, status tracking, lake-build validation. *Done when* we
  can dispatch Lea on one lemma end-to-end and mark it `\leanok`.
- **Step 3 (small-chapter run)** — author a setup chapter (definitions +
  trivialities), dispatch Lea on the whole chapter, measure success rate
  and cost. *Done when* we have empirical data on Lea's per-lemma cost
  for a non-trivial chunk.
- **Step 4 (full project)** — author / port the full blueprint, dispatch on
  everything, manually intervene on stuck lemmas. *Done when* either the
  main theorem builds clean or we hit a wall and pivot.

## Open decisions

- **Blueprint authoring**: author from paper directly, or fork Davis's
  blueprint structure (with attribution, after asking permission)?
  Forking saves weeks but couples to his proof architecture. Authoring
  ours gives proof-route freedom but is heavier upfront.
- **Lea model**: default Gemini 3.1 Pro? Escalate to Opus 4.7 for hard
  lemmas? Per-lemma model selection?
- **Cost cap**: hard budget per lemma (e.g. $2 max, then escalate) and
  per-project (e.g. $500 total before pause for review).
- **Failure handling**: what to do with stuck lemmas — retry with stronger
  model, hand off to user, mark blueprint with `\notyet`, skip and continue?
- **Cross-session memory**: 100+ lemmas can't fit in one Lea session.
  Per-lemma sessions? Shared "lessons learned" notes file?

## Reference oracle

Davis's [counting_hadamard](https://github.com/damek/counting_hadamard) repo
has the complete formalization. We treat it as a *reference oracle*:

- We do *not* copy Davis's Lean code.
- We *may* compare our outputs to his after we finish a lemma.
- We *may* read his proof structure to inform our blueprint authoring.
- License is unspecified in his repo (de facto all-rights-reserved), so
  redistribution is out of scope. Citations and links are fine.

## Held alternatives

- **Different paper**. If Davis's proves intractable, smaller papers
  with self-contained main theorems (1-3 pages of proof, single chapter
  blueprints) are a fallback. Combinatorial / discrete-math papers
  generally tract better than measure-theoretic ones.
- **Mathlib gap-filling**. If autonomous-formalization-of-papers proves
  to be the wrong shape, target the Mathlib TODO list directly.
