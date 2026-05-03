/-
# Log-expansion (lem:sixth)

Blueprint statement (informal):
  There exist constants `c₂, C₂ > 0` such that whenever `s(λ) ≤ c₂`,
        log ψ(λ) = −½·s(λ) − i·T(λ) + Q(λ) + i·P(λ) + E₆(λ),
  with `|E₆(λ)| ≤ C₂ · s(λ)³`.

The functionals `T(λ), Q(λ), P(λ)` are *not* free existential
witnesses; they are the canonical Davis functionals
`T_func, Q_func, P_func` defined in `LeaHadamard.Hadamard.Functionals`
(rescaled cumulants of the Rademacher quadratic form `Xform p lam`).
We pin them to those canonical definitions here, and existentially
quantify only the universal constants `c₂, C₂` (as the blueprint does).

## Status

The lemma is left as a `sorry` -- this is a deep analytic estimate.
A genuine proof requires:

1. A Taylor / Fourier expansion of `Complex.log (psi p lam)` around
   the origin, whose validity needs the small-energy hypothesis
   `s(λ) ≤ c₂` to ensure `|psi p lam − 1| < 1` so the principal-branch
   logarithm has a power series.

2. Identification of the first three nontrivial coefficients of that
   expansion with the rescaled cumulants
       −½·s, −i·T_func, Q_func, i·P_func
   via the cumulant-generating-function identity
       log E[exp(it X)] = ∑ₖ (it)ᵏ κₖ(X) / k! .
   This requires an explicit cumulant--moment combinatorial layer
   on the discrete cube which is **not yet present in this project**
   (only `cumulant3,4,5` and the `*_of_centered` simplifications
   exist; no link between `Complex.log psi` and these cumulants is
   formalized).

3. A uniform tail bound on the remainder
       E₆ = log psi − (−½ s − i T + Q + i P)
   of order `O(s(λ)³)`. This is the standard bound on a Taylor
   remainder and would follow from analyticity of `Complex.log`
   on the unit disk plus moment bounds on `Xform`, but again none
   of the supporting lemmas (e.g. `s(λ) ≥ E[X²]/2` style estimates,
   small-energy ⟹ `|psi − 1| < 1`) are currently available in
   the repository.

Because this lemma is a leaf in the dependency graph and none of
the necessary infrastructure (Taylor expansion of `Complex.log`
applied to a moment-generating function, cumulant--moment
combinatorics linking `log psi` to `cumulant3,4,5`) is in place,
the proof is genuinely beyond the reach of a single leaf step
and is left as an honest `sorry` per the project guidelines.
The signature uses the canonical Davis functionals `T_func`,
`Q_func`, `P_func` so that the statement has its intended
mathematical content (no existential-witness trivialization).
-/

import Mathlib
import LeaHadamard.Defs
import LeaHadamard.Hadamard.Functionals

open scoped BigOperators
open Complex

namespace LeaHadamard
namespace Hadamard

open LeaHadamard.Defs (psi sval)
open LeaHadamard.Hadamard.Functionals (T_func Q_func P_func)

/--
**Log-expansion (lem:sixth).**

There exist universal constants `c₂, C₂ > 0` such that for every
coupling vector `λ` whose energy satisfies `s(λ) ≤ c₂`,

        log ψ(p, λ) = −½ · s(λ) − i · T(λ) + Q(λ) + i · P(λ) + E₆(λ)

where `T = T_func p`, `Q = Q_func p`, `P = P_func p` are Davis's
canonical functionals (rescaled cumulants of `Xform p lam`), and
the remainder satisfies `|E₆(λ)| ≤ C₂ · s(λ)³`.

The conclusion is phrased as a norm bound on the difference

  ‖log ψ(p, λ) − [−½ s(λ) − i · T_func p λ + Q_func p λ + i · P_func p λ]‖
    ≤ C₂ · s(λ)³.

See the file header for an explanation of why a genuine proof
requires substantial machinery not currently present in the
project; this leaf node is left as `sorry`.
-/
theorem psi_pow_sub_correctedCoreIntegrand_norm_le_uniform
    {n : ℕ} {E : Type*} [Fintype E] (p : E → Fin n × Fin n) :
    ∃ c₂ C₂ : ℝ, 0 < c₂ ∧ 0 < C₂ ∧
        ∀ lam : E → ℝ, sval lam ≤ c₂ →
          ‖Complex.log (psi p lam)
              - ((-(1/2 : ℝ) * sval lam : ℂ)
                  - Complex.I * (T_func p lam : ℂ)
                  + (Q_func p lam : ℂ)
                  + Complex.I * (P_func p lam : ℂ))‖
            ≤ C₂ * (sval lam) ^ 3 := by
  -- Honest sorry: see file header. The proof requires a Taylor
  -- expansion of `Complex.log` applied to the characteristic
  -- function `psi`, plus a cumulant--moment identification linking
  -- `log psi` to `cumulant3,4,5 (Xform p lam)`. Neither piece of
  -- infrastructure is currently available in the project.
  sorry

end Hadamard
end LeaHadamard
