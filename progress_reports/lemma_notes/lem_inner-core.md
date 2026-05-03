# `lem:inner-core` — design notes (in flight)

## Statement (paraphrased)

There is an absolute constant `c_* > 0` such that for all `d ≥ 1` and
`t ≥ 1`,
$$\int_{\{\lambda \in \mathbb{R}^d : \|\lambda\|^2 \le d/t\}} e^{-2t\|\lambda\|^2}\,d\lambda
\;\ge\; (1 - e^{-c_* d})\,(\pi/(2t))^{d/2}.$$

## Why this lemma

- Concrete tail bound on the *core region* of a Gaussian integral.
  Used in Davis's primary-box decomposition.
- Pure real analysis: no Hadamard machinery. Mathlib has Gaussian
  integrals.
- Inverts the typical "Gaussian tail is small" lemma: here we want
  the *complement* (the integral over the small-radius region) to be
  large. So we'd estimate the tail and subtract.

## Encoding choices

We chose to match Davis's blueprint statement exactly. The
constraint set `{λ : ‖λ‖² ≤ d/t}` is a Euclidean ball; Mathlib has
`Metric.ball` and `closedBall`, plus `MeasureTheory.setIntegral`.

Lea will need to:
1. Express the full integral `(π/(2t))^(d/2)` (this is the d-dim
   Gaussian normalization).
2. Express the tail `∫_{‖λ‖² > d/t} e^{-2t‖λ‖²} dλ`.
3. Bound the tail by `e^{-c_*d} · (π/(2t))^(d/2)`.
4. Subtract.

Davis's proof uses a sharp argument: on `‖λ‖² > d/t`,
`e^{-2t‖λ‖²} ≤ e^{-d} · e^{-t‖λ‖²}`, so the tail is at most
`e^{-d} · (π/t)^(d/2) ≤ e^{-c_*d} · (π/(2t))^(d/2)` with
`c_* = 1 - (1/2) log 2`.

## Hints provided

- `integral_gaussian` — for the full d-dim Gaussian
- `integrable_exp_neg_mul_sq` — for integrability arguments
- `exp_neg_mul_sq_isLittleO_exp_neg` — tail decay
- `integral_pi` (couldn't resolve)
- `setIntegral_le_integral` — set-integral monotonicity
- `integrable_rpow_mul_exp_neg_mul_sq`
- `integral_mono_of_nonneg`

## Things we should look for in the paper

- Davis's `c_*` is `1 - (1/2)log 2 ≈ 0.653`. Will Lea match this, get
  a worse constant, or get a different (perhaps sharper) one?
- The proof critically uses an inequality between two Gaussians at
  different temperatures. Mathlib may not state this directly; Lea
  may have to derive it from `Real.exp_le_exp` plus a quadratic
  inequality.
- Davis's proof is short (~5 lines); ours is unlikely to be that
  short due to Mathlib API friction. Watch for size disparity.

## Status

In flight as of 2026-05-03. Opus 4.7, max-turns 200, 7 hints.
Live log at `runs/logs/lem_inner-core.lea.log`. Result captured
in `runs/davis_l0_innercore_tracker.json`.
