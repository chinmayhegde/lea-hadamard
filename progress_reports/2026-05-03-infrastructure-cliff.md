# The infrastructure cliff push — 2026-05-03

A 6-stage experiment running the same afternoon: have Lea autonomously
build the missing Mathlib infrastructure that several stuck blueprint
leaves needed, then retry the leaves on top of the new infrastructure.

## The setup

After day 1 we had 5 of 13 effective layer-0 leaves cleanly formalized
and 4 stuck on missing Mathlib infrastructure:

| Stuck leaf | Missing infrastructure |
|---|---|
| `lem:gaussian-quadratic` | Multivariate complex-symmetric Fresnel integrals |
| `lem:hc` | Bonami-Beckner / hypercontractivity on the discrete cube |
| `fact:fixed-n` | Partial-Hadamard count `N_{n,t}` + Tauberian passage |
| `lem:weak-comparison` | Lindeberg comparison theorem (third-derivative form) |

Davis crossed all four cliffs in his ~46k-line repo (we believe with
help from a fine-tuned tool, likely Aristotle). The question for the
afternoon: **can Lea (open-source, generic Opus 4.7, 6 tools, 300
lines of Python) approximate that cliff-crossing?**

## The plan

Six staged dispatches, each with explicit scope set by us (not the
blueprint DAG). Stages 1, 2, 4, 5 are direct Lea calls writing into
`LeaHadamard/Mathlib/`. Stages 3 and 6 are blueprint-node retries
through the standard dispatcher.

| Stage | Target | Approach |
|---|---|---|
| 1 | second-moment identity for Rademacher linear forms | direct Lea, `SignAverage.lean` |
| 2 | fourth-moment identity (using Stage 1) | direct Lea, extends `SignAverage.lean` |
| 3 | `fact:fixed-n` retry | dispatcher, with Stage 1+2 hints |
| 4 | Bonami two-point inequality | direct Lea, `BonamiTwoPoint.lean` |
| 5 | hypercontractive at degree 2 (using 1+2+4) | direct Lea, `Hypercontractive.lean` |
| 6 | `lem:hc` retry (using 5) | dispatcher, with all infra hints |

## Outcome

| Stage | Turns | Cost (actual) | Lines | Status |
|---|---|---|---|---|
| 1 — second moment | 19 | ~$4.4 | 195 | ✅ clean |
| 2 — fourth moment | 10 | ~$0.83 | 66 | ✅ clean |
| 3 — fact:fixed-n retry | 1 | ~$0.58 | (sorry) | honest sorry — needs lattice + Tauberian, not moment infra |
| 4 — Bonami two-point | 14 | ~$1.27 | 107 | ✅ clean |
| 5 — hypercontractive deg-2 | 71 | ~$31.2 | 834 | ✅ clean |
| 6 — lem:hc retry | 9 | ~$0.58 | 63 | ✅ clean — **`lem:hc` CLOSED** |
| **Total** | **123** | **~$38.9** | **1265** | |

All 5 clean stages: kernel-verified, axiom-clean
(`propext, Classical.choice, Quot.sound` only), no signature
mutations, real proofs. Cost-per-line **~$0.031** — *cheaper* than
`lem:triangle` (~$0.13/line, a layer-0 leaf), and roughly half the
cumulative-layer-0 average.

## What we learned

1. **The cliff narrative does not hold at this scope.** We hypothesized
   that "new infra" would cost 5-10× per-line vs. theorem-chaining.
   Empirically: same cost or cheaper. Three qualitatively different
   content classes (algebraic identities, real-analytic inequalities,
   polynomial-structure induction with Cauchy-Schwarz) all crossed
   cleanly under the same staged-dispatch pattern.

2. **The cheat-prevention prompt works in retry.** Stage 3
   (`fact:fixed-n`) had previously cheated via statement-tautologization;
   under the strengthened prompt + new infra hints, Lea took the
   honest path — defined the missing structure, locked the signature
   to the blueprint, and `sorry`'d the conclusion with a paragraph
   listing what's still missing. Same Lea, same model, different
   prompt.

3. **Stage-staging matters.** Each stage was scoped tight (one file,
   3-5 specific declarations, explicit signatures). When Stage 5
   needed 71 turns vs 10-19 for the smaller stages, the difference
   was in *content* (Walsh structure, Cauchy-Schwarz, polynomial
   induction) not in scope-management slippage. Tight scope +
   reference material (Davis's parallel file as read-only inspiration)
   keeps the dispatch focused even on hard content.

4. **Lea's path can diverge from Davis's.** Davis's pipeline doesn't
   contain an explicit Bonami-Beckner inequality (he uses Lindeberg
   + direct moment computations to sidestep). Lea built the
   inequality directly. Same downstream lemma (`lem:hc`), genuinely
   different proof architecture. **Architectural diversity is a
   feature**: it means we're not constrained to follow Davis's
   choices, and we can sometimes find a cleaner route.

5. **The pattern generalizes (probably).** The cliff push validates
   a workflow we can now apply to the remaining stuck leaves:

   - Identify the missing infrastructure (read the blueprint, the
     stuck file's `sorry` comment, and Davis's parallel work).
   - Stage it: 3-6 small files, each with explicit scope.
   - Dispatch each as a direct Lea call writing into
     `LeaHadamard/Mathlib/`.
   - Retry the blueprint leaf through the dispatcher with the new
     infrastructure exposed via prompt hints.

   Estimated cost for `lem:weak-comparison` (Lindeberg) and
   `lem:gaussian-quadratic` (multivariate Fresnel): ~$30-100 actual
   each, by analogy. `fact:fixed-n` is harder — needs the bulk of
   Davis's downstream chain, not infra-extraction.

## Files

- [`LeaHadamard/Mathlib/SignAverage.lean`](../LeaHadamard/Mathlib/SignAverage.lean)
- [`LeaHadamard/Mathlib/BonamiTwoPoint.lean`](../LeaHadamard/Mathlib/BonamiTwoPoint.lean)
- [`LeaHadamard/Mathlib/Hypercontractive.lean`](../LeaHadamard/Mathlib/Hypercontractive.lean)
- [`LeaHadamard/Auto/Lem_hc.lean`](../LeaHadamard/Auto/Lem_hc.lean)
- Layer overview: [`lemma_notes/infra_hypercontractive_layer.md`](lemma_notes/infra_hypercontractive_layer.md)
- Closed-leaf note: [`lemma_notes/lem_hc.md`](lemma_notes/lem_hc.md)

Per-stage logs are under `runs/infra/stage{1,2,4,5}.log` and
`runs/dispatcher_logs/retry_{fixed_n,lem_hc}/` (gitignored).
