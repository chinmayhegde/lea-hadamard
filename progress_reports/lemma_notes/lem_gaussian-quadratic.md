# `lem:gaussian-quadratic` — design notes (in flight)

## Statement (paraphrased)

Let `A` be a complex symmetric `m × m` matrix whose real part is
positive definite. Then
$$\int_{\mathbb{R}^m} e^{-x^\top A x}\,dx = \pi^{m/2}\,\det(A)^{-1/2}.$$

(Davis's blueprint also includes a second part about `|E[exp(ig^T M g/2)]|`
for Gaussian `g`. We're attempting only the first part for now.)

## Why this lemma

- Pure complex linear algebra + Gaussian integration. No Hadamard
  setup needed.
- Mathlib has `integral_gaussian_complex` for the 1D case; the
  multivariate generalization is the work.
- Tests Lea on a different proof shape than `lem:gaussian-radial`:
  here we need diagonalization or matrix factorization, not just
  pointwise-bound chasing.

## Encoding choices

We chose to mirror the paper's prose: `A` is a complex matrix, we
integrate `exp(-x^T A x)` over `ℝ^m`. Mathlib expresses this via
`Matrix.toBilin` or `Matrix.dotProduct`. Lea will pick the precise
formulation.

We did not pre-stage definitions for "complex symmetric matrix with
positive-definite real part" — Lea has to find the right Mathlib type
class (`Matrix.IsHermitian`? `IsSymm`? `PosDef` on `Matrix.re`?). This
is genuinely uncertain — Mathlib's matrix-analysis support for complex
matrices is patchier than for real.

## Hints provided

- `integral_gaussian_complex` — 1D complex Gaussian integral
- `integral_gaussian` — 1D real Gaussian
- `integral_gaussian_sq_complex`
- `continuousAt_gaussian_integral`
- `integral_gaussian_complex_Ioi`
- `integral_pi` (intended: multivariate via Fubini — but grep didn't
  resolve this name; Lea will need to find the right Pi-integral lemma)
- `Matrix.det_isHermitian` (similarly unresolved)
- `IsHermitian.det_eq_prod_eigenvalues`

## Things we should look for in the paper

- Davis's proof "diagonalizes `S = Re(A)^{-1/2} Im(A) Re(A)^{-1/2}`,
  factors the integral into 1D Fresnel integrals, reassembles via
  `det(A) = det(Re A) · det(I + iS)`." Sophisticated route.
- Will Lea find this? Or will she pick a different approach? Either
  outcome is interesting.
- What does Mathlib have for *complex* symmetric matrix
  diagonalization? Real symmetric is well-supported (spectral theorem);
  complex symmetric (different from Hermitian) is rarer.

## Status

In flight as of 2026-05-03. Opus 4.7, max-turns 200, 8 hints (3 of
which the dispatcher couldn't resolve via grep — Lea will work around).
Live log at `runs/logs/lem_gaussian-quadratic.lea.log`. Result captured
in `runs/davis_l0_quadratic_tracker.json`.
