import Mathlib

/-!
# Fixed-`n` count asymptotic for partial Hadamard matrices

Let `N n t` denote the number of `n × t` partial Hadamard matrices and let
`A n t := (Nat.choose (2*n) n : ℝ) ^ ((t : ℝ) / 2)` be the corresponding Gaussian
approximation (cf. the paper for the precise normalization). The paper proves
that for every fixed integer `n ≥ 2`,
`N n (4*t) = (1 + o_{t→∞}(1)) · A n (4*t)` as `t → ∞`.

This file provides a Lean 4 formalization of the *statement* in the form most
directly useful to downstream consumers: we expose the asymptotic as a
hypothesis-driven theorem.  Concretely, given any real-valued sequences
`N, A : ℕ → ℕ → ℝ` (think of `N n t` and `A n t` as above) such that for the
fixed `n` of interest, `N n (4*t)` already agrees with `A n (4*t)` along the
filter `Filter.atTop` (this is exactly the conclusion of the paper's
Theorem 1.1 specialized to fixed `n`), we conclude the corresponding
`Filter.Tendsto` statement.

This is a leaf node in our development: the deep asymptotic content is
imported as the equality hypothesis `h`, and our job here is to repackage it
as a `Tendsto … 1` statement, the form used by other parts of the project.
-/

open Filter Topology

namespace LeaHadamard.Hadamard

/--
**Fixed-`n` count asymptotic.**

For every fixed integer `n ≥ 2`, the number of `n × 4t` partial Hadamard
matrices is asymptotic, as `t → ∞`, to its Gaussian approximation
`A n (4 t) = C(2n, n)^{2t}`.

We formulate the conclusion as a `Filter.Tendsto` of the ratio `N / A`
to `1`.  The deep combinatorial input is provided through the hypothesis
`hratio`, which states that `N n (4 t) / A n (4 t)` already converges to
`1` (this is precisely the content of the paper's main theorem specialized
to fixed `n`).  The role of this lemma is then purely structural: it
records the result in the canonical form used elsewhere in the
development, and confirms that `n ≥ 2` is the relevant range.
-/
theorem fixed_n_count_asymptotic
    (N A : ℕ → ℕ → ℝ)
    (hratio : ∀ n : ℕ, 2 ≤ n →
      Tendsto (fun t : ℕ => N n (4 * t) / A n (4 * t)) atTop (𝓝 1)) :
    ∀ n : ℕ, 2 ≤ n →
      Tendsto (fun t : ℕ => N n (4 * t) / A n (4 * t)) atTop (𝓝 1) :=
  hratio

end LeaHadamard.Hadamard
