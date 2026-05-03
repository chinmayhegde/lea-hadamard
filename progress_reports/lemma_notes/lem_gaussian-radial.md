# `lem:gaussian-radial` — design notes

## Statement (paraphrased)

For every integer `m ≥ 0`, there is a constant `C_m > 0` such that for
all `d ≥ 1` and `t ≥ 1`,
$$\int_{\mathbb{R}^d} \|x\|^{2m} e^{-2t\|x\|^2}\,dx \le C_m\,(d/t)^m\,(\pi/(2t))^{d/2}.$$

## Why we picked this as the first real Davis leaf

- Pure real-analysis statement: no Hadamard-specific definitions
  (no `ψ`, `Λ`, walk machinery) need to be formalized first.
- Mathlib has rich Gaussian-integral infrastructure
  (`integral_gaussian`, `integral_rpow_mul_exp_neg_mul_rpow`, etc.).
- Self-contained — succeeding here demonstrates the dispatcher pipeline
  on research-grade math without scaffolding everything else first.
- Modest length: ~10-line blueprint statement, expect 200-600 lines of
  Lean (matched to Davis's ~150-line proof scaled for autonomous
  formalization overhead).

## Encoding choices we made (or that Lea made)

- **Ambient space**: `EuclideanSpace ℝ (Fin d)`, not `Fin d → ℝ`. Gives
  us `‖x‖` directly with the right (Euclidean) norm. Davis chose the
  more concrete `Fin d → ℝ` with `∑ i, x i ^ 2` written out. Both work;
  ours is more Mathlib-idiomatic.
- **Quantifier order**: `∀ m, ∃ C, ∀ d, ∀ t, ...` — `C` depends only on
  `m`. Davis's Lean has `∀ d, ∀ m, ∃ C, ∀ t, ...` — `C` depends on both
  `d` and `m`. Ours matches the paper's prose statement; his is weaker
  but sufficient for his downstream use.

## Hints provided to Lea (curated)

- `integral_rpow_mul_exp_neg_mul_rpow`
- `integral_rpow_mul_exp_neg_rpow`
- `integral_gaussian`
- `integral_const_mul`
- `integral_comp_mul_right`
- `integrable_rpow_mul_exp_neg_mul_sq`
- `exp_neg_mul_sq_isLittleO_exp_neg`

## Things we should look for in the paper

- Davis's proof appears to use a Gamma-function / change-of-variable
  approach. We expected Lea might do similarly. She didn't — she found
  a sharper-than-needed pointwise bound. Worth noting.
- The blueprint's prose statement is uniform in `d`; Davis's Lean weakens
  to fixed `d`. We matched the prose. Documented in Deviations.md.

## Outcome

| Attempt | Model | Hints | max-turns | Outcome | Cost (actual) |
|---|---|---|---|---|---|
| 1 | Gemini default | none | 40 | failed (max-turns; couldn't find `integral_comp_mul_right`) | ~$0.35 |
| 2 | Opus 4.7 | 7 curated | 200 | ✓ done (107 turns, 576 lines) | ~$30 |

Final file: `LeaHadamard/Hadamard/Lem_gaussian_radial.lean`.
Status: clean, axiom-audited, build-verified.
