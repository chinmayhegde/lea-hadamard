# `lem:triangle` — design notes

## Statement

For `λ ∈ ℝ^d` with `d = (n choose 2)` and Rademacher signs ξ, define
`X_λ(ξ) := Σ_{i<j} λ_{ij} · ξ_i · ξ_j` and
`T(λ) := Σ_{i<j<k} λ_{ij} · λ_{ik} · λ_{jk}`.
Then `T(λ) = (1/6) · E[X_λ³]`.

## Why this lemma was substantive

This is a moment-matching identity: the cubic functional `T` (a sum over
triangles in the complete graph on `n` vertices) equals one-sixth of the
third Rademacher moment of `X_λ`. The proof requires:

1. Cubing `X_λ`: `X_λ³ = Σ_{p,q,r} λ_p λ_q λ_r · ξ-product` over triples
   of edges `(p, q, r)`.
2. Evaluating `E[ξ-product]`: a product of `sgn(ξ_i)` factors over the 6
   indices in the triple `(p, q, r)`. Average is `2^n` if every index
   appears an even number of times, else 0.
3. Identifying which (ordered) triples of edges have each vertex with
   even multiplicity. Combinatorial case analysis: it's exactly the
   triples where the three edges form a triangle (each vertex in 2 edges).
4. Counting orderings: each unordered triangle `{(i,j), (i,k), (j,k)}`
   gives `3! = 6` ordered triples.

This is the standard "method of moments / multigraph counting" argument,
done formally for the first time in our code (Davis presumably has a
similar lemma in his `HadamardCn3Moments.lean`).

## What Lea built

888 lines, 0 sorries, clean Mathlib axioms. The proof structure
(seen via the `theorem triangle_formula` skeleton):
1. `sum_X_cubed_eq lam`: rewrite `Σ_ξ X_λ(ξ)³` as a sum over balanced
   (every-vertex-even-multiplicity) ordered triples of edges, scaled by
   `2^n`.
2. Apply combinatorial counting: balanced triples are exactly
   triangle orderings; each unordered triangle contributes `6 · λλλ`.

Lea defined:
- `sgn` (Rademacher sign)
- `X` (the Rademacher quadratic form)
- `T` (the cubic functional / triangle sum)
- `Pset`, `Tset` (pair set, triple set as `Finset`)
- `slot`, `mult` (helper for indexing the 6 vertices in a triple)

Plus many lemmas around `Finset` manipulation, `if_neg` after
substitution patterns, etc.

## Hints provided

```
Finset.sum_pow, Finset.sum_mul_sum, Finset.expectation, uniformOn,
MeasureTheory.integral_dirac, MeasureTheory.integral_finset_sum,
Finset.prod_range_succ
```

7 hints — **all unresolved by the dispatcher's grep**. Lea proved this
without curated hints (similar to `fact:psi-sq`). The pattern is
emerging: when Mathlib has the exact lemma, hints help; when Lea has to
build infrastructure, hints are mostly decorative.

## Comparison to Davis

Same proof skeleton: cube, count even-multiplicity multigraphs,
identify triangles, multiply by 6. Davis's manuscript proof is one
paragraph; his Lean is presumably a few hundred lines with helpers.
Ours is 888 lines — possibly some cruft (Lea iterated many times
restructuring), but the core proof is sound.

**Notable iteration**: Lea hit 119+ turns. Most of the back-and-forth
(visible in the lea log) was on the combinatorial bookkeeping —
specifically getting `simp` to behave correctly on `if-then-else`
expressions inside `Finset.sum`. This is a real friction point with
Mathlib's tactics for combinatorial sums.

## Outcome

| Attempt | Model | Hints | max-turns | Outcome | Cost (actual) |
|---|---|---|---|---|---|
| 1 | Opus 4.7 | 7 (none resolved) | 200 | ✓ done (888 lines, 119+ turns) | ~$117 |

`#print axioms`: clean Mathlib base.
File: `LeaHadamard/Hadamard/Lem_triangle.lean`.

## Implications

This is the **most expensive layer-0 leaf so far** ($117 actual). It's
also the most combinatorially intricate — pure index manipulation
inside `Finset.sum`, which Mathlib's automation handles less smoothly
than algebraic / analytic content. Future combinatorial-heavy lemmas
(e.g., the cycle-counting lemmas in deeper layers) should budget
similarly.
