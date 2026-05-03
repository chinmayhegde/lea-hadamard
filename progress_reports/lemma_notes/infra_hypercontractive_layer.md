# Hypercontractive infrastructure layer — design notes (landed)

A 1265-line, 4-file Lea-authored layer that gives the project a
Bonami-Beckner-style hypercontractive inequality on the discrete cube.
None of this exists in Mathlib v4.28.0; it's the first substantial
piece of infrastructure Lea built autonomously rather than chained
from existing lemmas. Built across Stages 1+2+4+5 of the
[infrastructure-cliff push](../2026-05-03-infrastructure-cliff.md);
the closed downstream node is [`lem:hc`](lem_hc.md).

## File-by-file

### [`LeaHadamard/Mathlib/SignAverage.lean`](../../LeaHadamard/Mathlib/SignAverage.lean) — 261 lines, ~$5 actual

Discrete uniform-measure expectation on Bool^n.

- `avgSigns n (f : (Fin n → Bool) → ℝ) := (∑ σ, f σ) / 2^n`
- `linearX n x σ := ∑ i, x i · rad (σ i)` — Rademacher linear form.
- Linearity (`avgSigns_const`, `_add`, `_mul_const_left`, `_sum`).
- Splitting (`avgSigns_split_last`): peel off the last sign via
  `Fin.snoc`, splits `avgSigns (n+1)` as `avgSigns n` of an inner
  Bool-average.
- **Second-moment identity** `avgSigns_linearX_sq`: `E[L²] = ∑ x_i²`.
- **Fourth-moment identity** `avgSigns_linearX_four`:
  `E[L⁴] = 3·(∑ x_i²)² − 2·(∑ x_i⁴)`.

Both moment identities are proved by induction on `n` with the
snoc decomposition. The fourth-moment proof uses the second-moment
identity in its inductive step — the dependency wove cleanly.

Encoding note: Davis encodes signs as `Fin 2`; we use `Bool`.
Lea adapted independently and defined her own
`boolVecLastEquiv : (Fin (n+1) → Bool) ≃ (Fin n → Bool) × Bool`
to bridge — slightly more Mathlib-idiomatic than Davis's raw
`Fin.snoc` plumbing.

### [`LeaHadamard/Mathlib/BonamiTwoPoint.lean`](../../LeaHadamard/Mathlib/BonamiTwoPoint.lean) — 107 lines, ~$1.27 actual

The Bonami-Beckner two-point inequality (n = 2 base case).

- `avgSigns_linearX_fourth_le_three_sq_second_sq`: `E[L⁴] ≤ 3·E[L²]²`
  for the linear form (immediate corollary of the moment identities).
- `bonami_two_point_fourth`:
  `((a+b)⁴ + (a−b)⁴)/2 ≤ 9 · (((a+b)² + (a−b)²)/2)²`. Proved by
  `nlinarith` on a square-nonneg-hint set.
- `bonami_two_point_two_var`: the Bool×Bool base case for arbitrary
  `f : Bool × Bool → ℝ`, with the four function values extracted via
  `set` and the inequality closed by `nlinarith`.

This is the first stage that's qualitatively *real-analytic*
(`nlinarith` + square-nonneg hint engineering), not just algebraic
identities.

### [`LeaHadamard/Mathlib/Hypercontractive.lean`](../../LeaHadamard/Mathlib/Hypercontractive.lean) — 834 lines, ~$31 actual

The headline. Largest single Lea-authored file in the project.

**Structures.** `WalshDeg1 n` (constant + linear coefficients) and
`WalshDeg2 n` (constant + linear + symmetric quadratic coefficients,
zero-on-diagonal). `evalDeg1`, `eval` evaluation maps. `WalshDeg2.tail`
and `WalshDeg2.lastSlice` decompositions for inductive-step plumbing.

**Walsh orthogonality (proved via flip-bit involutions on the cube):**
- `avgSigns_rad_eq_zero (i : Fin n) : avgSigns n (rad ∘ (· i)) = 0`
- `avgSigns_rad_mul_rad_eq_zero (i j : Fin n) (hij : i ≠ j) : ...`
- `avgSigns_linearX_eq_zero` (1st moment vanishes)
- `avgSigns_linearX_cube` (3rd moment vanishes — flip-all-bits negates
  the form)

**L² Parseval** `avgSigns_walshDeg2_sq`: sum-of-squared-coefficients
formula. Expand `(eval p σ)²`, distribute through linearity, kill
cross-terms via orthogonality.

**Cauchy-Schwarz on `avgSigns`** (`avgSigns_mul_sq_le`): real Mathlib
plumbing through `sum_mul_sq_le_sq_mul_sq` and `div_le_div_iff₀`.
Non-trivial; required Lea to find the right Mathlib name across two
generations (`div_le_div_iff` failed; `div_le_div_iff₀` worked).

**Degree-1 hypercontractive** `hc_degree1_fourth`: bound for affine
forms `c + L`, derived from `avgSigns_linearX_four` plus
cube-vanishing.

**Headline — `hc_degree2_fourth`**: induction on `n`. Successor case
writes `f(σ, b) = G(σ) + rad b · H(σ)` via `tail`/`lastSlice`,
applies `avgSigns_split_last`, bounds the cross-term `EGH = E[G²·H²]`
via Cauchy-Schwarz, combines with the inductive hypothesis (on G,
deg ≤ 2) and the degree-1 bound (on H, deg ≤ 1), and closes the
resulting polynomial in `EG2, EH2, EG4, EH4, EGH` via `nlinarith`.
Constant **81** matches the textbook Bonami-Beckner bound at
`(p, q) = (4, 2)`.

### [`LeaHadamard/Auto/Lem_hc.lean`](../../LeaHadamard/Auto/Lem_hc.lean) — 63 lines, ~$0.58 actual

Closes the `lem:hc` blueprint node. One-line term-mode proof:
`hc_degree2_fourth p`. See [`lem_hc.md`](lem_hc.md) for the full
story.

## Architectural notes

**Different from Davis's path.** Davis's `HadamardCn3DiscreteMoments.lean`
contains parallel moment identities (analogues of Stages 1+2) but
**no explicit Bonami-Beckner inequality** — he sidesteps the need for
hypercontractivity in his pipeline via direct moment computations and
Lindeberg-style arguments. Lea instead built the inequality directly.
Same downstream lemma (`lem:hc`), genuinely different proof
architecture.

**Plausible upstream-Mathlib candidate.** Modulo cleanup, this layer
is roughly the right shape for a Mathlib PR. The `WalshDeg2`
structure is ad-hoc (an explicit-form encoding rather than the
general `Walsh n d` indexed family Mathlib would prefer), but the
moment identities, orthogonality lemmas, and the `hc_degree2_fourth`
result itself would be welcomed. Worth flagging for follow-up.

**Cost-per-line: ~$0.031.** Lower than `lem:triangle` (~$0.13/line)
and roughly half the cumulative-layer-0 average. The "infrastructure
cliff" framing — where new infra is supposed to cost 5-10× per line
relative to chaining — does not hold at this scope.

## Trust surface

All headline theorems (`avgSigns_linearX_sq`, `avgSigns_linearX_four`,
`bonami_two_point_fourth`, `bonami_two_point_two_var`,
`hc_degree2_fourth`, `fixedDegreeHC_degree2_W_fourth`) report
`propext, Classical.choice, Quot.sound` from `#print axioms`.
No `sorry`, no `axiom`, no `native_decide`, no namespace shadows,
no signature mutations. `lake build` clean.

## Reused / prerequisite Mathlib lemmas

Lea pulled at least the following from Mathlib v4.28.0 — all from
`search_mathlib`:

- `Finset.sum_div`, `Finset.sum_add_distrib`, `Finset.mul_sum`,
  `Finset.sum_congr`, `Finset.sum_nonneg`, `Finset.sum_univ_castSucc`
- `Fin.snoc`, `Fin.init`, `Fin.lastCases`
- `Fintype.sum_bool`, `Fintype.sum_prod_type`
- `pow_succ`, `sq_nonneg`, `div_pow`, `div_mul_div_comm`,
  `div_le_div_iff₀`, `mul_le_mul_of_nonneg_left/right`
- `sum_mul_sq_le_sq_mul_sq` (Cauchy-Schwarz on finite sums)
- `Function.update`, `Bool.not`
- `nlinarith`, `positivity`, `linarith`, `ring`

The two non-obvious finds were `div_le_div_iff₀` (not the older
unzeroed name) and `sum_mul_sq_le_sq_mul_sq` (the precise Cauchy-
Schwarz form). Both came out of Lea's `search_mathlib` queries.
