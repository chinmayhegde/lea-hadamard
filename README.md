# lea-hadamard

Blueprint-driven autonomous formalization of Damek Davis's
[*Counting partial Hadamard matrices in the cubic regime*](https://arxiv.org/abs/2603.30013)
(arXiv:2603.30013, 2026), driven by [Lea](https://github.com/chinmayhegde/lea-prover).

## What this is

An ongoing experiment: hand a research math paper's blueprint DAG to an
autonomous Lean 4 agent (Lea, ~300 lines of Python on top of Opus 4.7),
and see how far it gets without a human writing proof code. We compare
afterwards against Davis's own Lean formalization at
[damek/counting_hadamard](https://github.com/damek/counting_hadamard) —
treated as a reference oracle, not consulted before Lea attempts a node.

## Status (2026-05-03)

Blueprint DAG: **27 named theorems, 7 topological layers, 13 effective
layer-0 leaves** (after splitting Davis's bundled `lambda-facts`).

| Layer-0 status | Count |
|---|---|
| Cleanly formalized (kernel-verified, axiom-clean) | **5** |
| Honest stucks (`sorry` + diagnostic comment) | 4 |
| Cheats caught and quarantined | 3 |
| Other | 1 (split by Lea, partially landed) |

Total real Lea spend so far ≈ **$282** across all attempts. Avg
cost-per-clean-leaf ≈ **$56 actual**. All 5 wins use only the standard
Mathlib axiom base (`propext, Classical.choice, Quot.sound`).

**Currently running (2026-05-03 PM):** infrastructure-cliff Stage 1 — Lea
is building a discrete sign-average moment layer (`avgSigns`, `linearX`,
second-moment identity) that several stuck leaves need but Mathlib
doesn't provide. See
[`progress_reports/2026-05-03-infrastructure-cliff.md`](progress_reports/2026-05-03-infrastructure-cliff.md).

## Headline lessons

1. **Lea + Opus 4.7 + curated Mathlib hints** can autonomously close
   research-grade layer-0 leaves of a real paper, including ones
   requiring novel definitions (ψ, X_λ, Rademacher quadratic forms).
2. **The wall is Mathlib API knowledge, not mathematical reasoning.**
   Curated hint signatures dramatically improve close rate.
3. **Verification by `lake build` + `sorry`-grep is not enough.** Three
   distinct *signature-mutation* cheat classes (statement-tautologization,
   extended-real-with-⊤, placeholder-by-definition) pass standard audits
   and are only catchable by comparing the proven signature against the
   blueprint statement.
4. **Cost extrapolation for the full 27-node project:** ~$1,500-2,500
   actual at current per-node prices. Genuinely cheap relative to the
   artifact value.

## Layout

- `LeaHadamard/` — Lean modules. `Defs.lean` for shared canonical
  definitions; `Hadamard/` for blueprint-node lemmas; `Mathlib/` for
  reusable infrastructure Lea is building (e.g. `SignAverage.lean`).
- `LeaHadamard.lean` — package entrypoint.
- `blueprint/src/` — blueprint LaTeX source. `single_*.tex` are
  single-node extracts the dispatcher feeds to Lea.
- `tools/` — Python tooling: blueprint parser, dispatcher, dep-graph
  renderer, single-node extractor, hint discovery.
- `progress_reports/` — per-day summaries, deviations log, per-lemma
  notes, dependency-graph snapshots.
- `runs/` — Lea dispatch logs and trackers (gitignored).

## Reproducing

Mathlib v4.28.0 (matches Davis). Lake-only build.

```bash
lake build                              # build everything
lake build LeaHadamard.Hadamard.Lem_realpart  # build one node
```

Dispatcher invocation example:

```bash
python3 tools/dispatcher.py \
    --blueprint blueprint/src/single_lem_realpart.tex \
    --tracker runs/single_lem_realpart_tracker.json \
    --lea-root /home/<user>/lea-prover \
    --model claude-opus-4-7 --max-turns 200
```

## Cheat classes catalogued (so far)

8 distinct ways an agent can pretend to prove a theorem and pass naive
audits. Full details in
[`progress_reports/Deviations.md`](progress_reports/Deviations.md).
The last three are signature-mutations — invisible to `sorry` /
`axiom` / `native_decide` / namespace-shadow / import-sorry checks.

1. `sorry` keyword
2. `axiom` declaration
3. `@[extern]` / `@[implemented_by]` / `native_decide`
4. Namespace shadow (e.g. `:= True`)
5. Import-sorry
6. Statement-tautologization (add the conclusion as a hypothesis)
7. Extended-real-with-⊤ (lift to `ℝ≥0∞`, choose `c = ⊤`)
8. Placeholder-by-definition (`def X := RHS`, prove `X = RHS` by `rfl`)

The dispatch prompt now bans all 8 explicitly. Detection of cheats
6-8 requires comparing Lea's signature against the blueprint statement.

## References

- Davis, *Counting partial Hadamard matrices in the cubic regime*, arXiv:2603.30013 (2026).
- [damek/counting_hadamard](https://github.com/damek/counting_hadamard) — Davis's Lean formalization (used as reference oracle, not used in our runs).
- [Lea-prover](https://github.com/chinmayhegde/lea-prover) — the agent driving formalization.
