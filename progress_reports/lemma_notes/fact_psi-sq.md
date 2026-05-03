# `fact:psi-sq` — design notes

## Statement (paraphrased)

Let `ξ_1, ..., ξ_n` be independent Rademacher signs and define
`ψ(γ) := E[exp(i Σ_{i<j} γ_{ij} ξ_i ξ_j)]`.
Then for every `γ ∈ [-π, π]^d` (with `d = (n choose 2)`) and every
`k ∈ {1, ..., n}`,
$$|\psi(\gamma)|^2 \le \tfrac12 + \tfrac12 \prod_{i \ne k} \cos(2\gamma_{\{i,k\}}).$$

## Why this lemma was hard

Unlike `lem:gaussian-radial` and `lem:inner-core`, the statement of
`fact:psi-sq` uses ψ, which is *not* in Mathlib. To even state the
theorem in Lean, Lea had to:

1. Define Rademacher signs (as `Bool` valued; `true ↦ +1`, `false ↦ -1`).
2. Define the quadratic phase `Σ_{i<j} γ_{ij} ξ_i ξ_j` (the symmetric
   sum over unordered pairs).
3. Define ψ as the average over the `2^n` sign configurations.
4. Then prove the cosine-product bound.

This is a far cry from "use a Mathlib lemma." It's a complete mini
formalization of the relevant probabilistic / characteristic-function
setup, end-to-end.

## What Lea built

11 helper definitions and lemmas plus the main theorem
(537 lines total):

- `rad`, `rad_sq`, `rad_mul_self`, `abs_rad`,
  `rad_update_ne`, `rad_update_self_true`, `rad_update_self_false`
  — Rademacher-sign abstraction.
- `edge`, `edge_diag`, `edge_symm`
  — symmetric edge weights via canonical (min, max) ordering, so
  asymmetric input γ is silently symmetrized to the right convention.
- `phase`, `Lcoef`, `Qcoef`
  — the inner quadratic form, plus coefficients `L`(linear in `ξ_k`)
  and `Q`(constant in `ξ_k`) when conditioning on the `k`th sign.
  This is the *non-trivial* algebraic step: the proof flips on
  expanding ψ as `Average_{ξ_{≠k}} [Average_{ξ_k} exp(i (L ξ_k + Q))]`,
  which collapses to `Average_{ξ_{≠k}} cos(L) · exp(iQ)`.
- `phase_split`, `Lcoef_update`, `Qcoef_update`, `exp_phase_average`,
  `sum_exp_phase_eq`
  — the supporting identities.
- `universal_magnitude_bound_full`
  — the main theorem (the actual cosine-product bound).

## Comparison to Davis

Davis's `psi` (in `RequestProject/HadamardCn3Defs.lean`):
```lean
def psi (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℂ := ...
```

Lea's:
```lean
private noncomputable def psi {n : ℕ} (γ : Fin n → Fin n → ℝ) : ℂ :=
  ((1 : ℝ) / (2 ^ n : ℝ) : ℂ) *
    ∑ ξ : Fin n → Bool, Complex.exp (Complex.I * (phase γ ξ : ℂ))
```

Same shape, same content. The chief difference is that Lea's `psi` is
`private` (only visible inside this file) — meaning *every later
ψ-using lemma will need its own ψ definition unless we promote
something to a shared module*. Worth flagging as a refactor target
once we hit `lem:realpart` (also needs ψ). Davis declares ψ once in
his `Defs.lean` and reuses everywhere; we should mirror that.

## Hints provided

```
Complex.abs_sq, Complex.norm_eq_abs, Complex.exp_im, Complex.cos,
Real.cos_le_one, Finset.prod_le_prod, Finset.expectation, uniformOn
```

8 hints, **all of which the dispatcher's grep failed to resolve** (Lea
saw "(not found by grep — check spelling or import path)" for every
single one). She still succeeded — meaning hints aren't strictly
necessary for difficult cases, just helpful when they hit.

## Things we should look for in the paper

- Davis's proof of the cosine-product bound is "fold the ξ_k average
  into a single cosine" — exactly what Lea did. Same structural
  argument.
- The `\prod_{i ≠ k} cos(2 γ_{i,k})` form requires the `i = k` row to
  be exempted; Lea handled this by erasing `k` from the sum and using
  `edge_diag` for the diagonal (`γ_{k,k}` doesn't matter because
  `edge γ k k = 0`).
- Lea's signature requires `γ` to be symmetric explicitly
  (`hγ : ∀ i j, γ i j = γ j i`). Davis bakes symmetry into the type
  by working on unordered pairs (his `lam` is indexed by edges,
  not pairs of indices). Equivalent; different ergonomics.

## Outcome

| Attempt | Model | Hints | max-turns | Outcome | Cost (actual) |
|---|---|---|---|---|---|
| 1 | Opus 4.7 | 8 (all unresolved) | 200 | ✓ done (155 turns, 537 lines) | ~$73 |

`#print axioms`: clean Mathlib base.
File: `LeaHadamard/Hadamard/Fact_psi_sq.lean`.

## Implications

This is the **first time Lea formalized a statement that required her
to first formalize the surrounding infrastructure** (ψ and friends).
The success here is qualitatively different from `lem:gaussian-radial`
and `lem:inner-core`: those were Mathlib-adjacent. `fact:psi-sq`
needed Lea to *invent* the right Lean API for a probabilistic object
the Lean ecosystem doesn't yet have.

This also means we now have ψ defined (privately) in our project. If
we want `lem:realpart`, `fact:psi-sq` retry with shared definition, etc.,
we should *promote* Lea's ψ definition (and helpers) to a public
`LeaHadamard/Hadamard/Defs.lean` module so other lemmas can import it.
