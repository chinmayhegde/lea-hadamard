# `lem:realpart` — design notes

## Statement

If `s(λ) ≤ 1/2`, then `Re ψ(λ) ∈ [3/4, 1]`,
where `ψ(λ) = E[exp(i Σ_{i<j} λ_{ij} ξ_i ξ_j)]` and
`s(λ) = Σ_e λ_e²`.

## Why this lemma was hard

Like `fact:psi-sq`, the statement uses ψ which isn't in Mathlib. Lea
had to define ψ, the quadratic form `X_λ`, and `s(λ)` from scratch —
in this file, separately from the ψ already defined in
`Fact_psi_sq.lean` (since both are `private` to their respective
files). **This is the duplication issue flagged in the psi-sq notes:
each ψ-using lemma redoes the setup until we promote a shared
`Defs.lean` module.**

## What Lea built

Lea wrote 310 lines, with 12 named helpers plus the main theorem:

- `rad`, `rad_sq`, `rad_not` — Rademacher signs.
- `Xform`, `psi`, `sval` — the quadratic form, characteristic function,
  and energy.
- `re_psi_eq_avg_cos` — express `Re ψ(λ)` as `(1/2^n) Σ_ξ cos(X_λ(ξ))`.
- `re_psi_le_one` — the trivial upper bound.
- `flipAt`, `flipAt_apply_eq`, `flipAt_apply_ne`, `flipAt_involutive`,
  `flipAt_ne` — the bit-flip involution on `ξ` used to evaluate
  Rademacher moments.
- `sum_rad_quadruple_eq_zero_of_unique` and three variants
  — moment lemmas: `E[ξ_a ξ_b ξ_c ξ_d] = 0` unless indices pair up
  evenly. The crucial probabilistic step.
- `sum_rad_quadruple_off_diag`, `sum_rad_quadruple_diag`
  — case-split versions used to compute the second moment.
- `avg_Xform_sq_eq` — `(1/2^n) Σ_ξ X_λ(ξ)² = ‖λ‖²`. The key moment
  identity that makes the proof work.
- `re_psi_taylor4_decomposition` — main theorem.

## The proof in one line

`cos(x) ≥ 1 - x²/2` (Mathlib's `Real.one_sub_sq_div_two_le_cos`)
applied pointwise inside the Rademacher average, then
`(1/2^n) Σ_ξ X_λ(ξ)² = ‖λ‖² ≤ 1/2` from `avg_Xform_sq_eq` and the
hypothesis, then `linarith`. Three lines of high-level proof; the
work is in setting up the moment identity.

## Comparison to Davis

Davis's proof (per the blueprint sketch):
> `Re ψ(λ) = E[cos X_λ] ≥ 1 - (1/2) s(λ) ≥ 3/4`.

Same argument. Lea's chain is identical: `cos ≥ 1 - x²/2` → average →
`E[X²] = ‖λ‖²`. The 12 helper lemmas are because Lea has to *prove*
`E[X²] = ‖λ‖²` from first principles using bit-flip involutions and
case-by-case analysis of which Rademacher quadruples vanish — Davis
likely has analogous machinery in his `HadamardCn3Defs` and
`HadamardCn3Moments` files.

## Encoding deviation worth noting

Lea generalized the type of `λ`'s index set:
```lean
{n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
(p : E → Fin n × Fin n)
(hp_lt : ∀ e, (p e).1 < (p e).2)
(hp_inj : Function.Injective p)
(lam : E → ℝ)
```

The blueprint says "λ ∈ ℝ^d with d = (n choose 2)". Lea instead takes
*any* finite indexing type `E` with an injective ordered-pair label,
and `λ : E → ℝ`. Specializing `E := {(i,j) : i < j}` recovers the
blueprint statement; *more general* than the blueprint. This is also
**stricter than what Davis does** (he uses unordered pairs directly
in his types). Lea's parametric generalization is genuinely useful —
it would be the right Mathlib-upstream form.

## Tracker false negative — lake-build race

`Lem_realpart.lean` was initially marked `stuck` despite being
complete. Reason: the dispatcher's success criterion is "global
`lake build` clean", but `Lem_triangle.lean` was mid-iteration with
errors at the time of realpart's validation. So *another file's*
broken state caused realpart to be miscategorized.

**Process bug**: when running 5 dispatchers in parallel, each tries
to lake-build the whole project. Concurrent broken-mid-iteration
files cross-contaminate. Tomorrow's fix: the dispatcher should
build *only its own* target (`lake build LeaHadamard.Hadamard.X`),
not the whole project.

## Hints provided

```
Real.cos_le_one, Real.one_sub_sq_div_two_le_cos, Real.cos_lt_one,
Complex.exp_re, Complex.exp_im, Real.cos_pi_div_three, Real.cos_zero,
MeasureTheory.integral_cos
```

8 hints — most resolved by the dispatcher's grep (the `Real.cos*`
ones). `Real.one_sub_sq_div_two_le_cos` is the load-bearing one.

## Outcome

| Attempt | Model | Hints | max-turns | Outcome | Cost (actual) |
|---|---|---|---|---|---|
| 1 | Opus 4.7 | 8 | 200 | ✓ done (310 lines, ~80 turns) | ~$27 |

`#print axioms`: clean Mathlib base.
File: `LeaHadamard/Hadamard/Lem_realpart.lean`.
