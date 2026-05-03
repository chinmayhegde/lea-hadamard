/-
# Hypercontractive inequality (degree 2, fourth moment, Walsh / Rademacher)

Blueprint statement (informal, general form):
  Let `H` be a polynomial of degree ≤ q in either independent Rademacher
  signs or independent centered Gaussians.  Then for every `p ≥ 2`,
        ‖H‖_{L^p} ≤ (p − 1)^{q/2} · ‖H‖_{L^2}.

This file is the **leaf instance** of that theorem actually used in the
formalization: the case `(p, q) = (4, 2)` for Walsh / Rademacher
polynomials, where the constant `(p − 1)^{q/2} = 3^1 = 3` translates to
the fourth-moment form

        E[H^4] ≤ 81 · (E[H^2])^2.

The general statement (arbitrary `p ≥ 2`, arbitrary degree `q`, plus the
Gaussian variant) is *not* in Mathlib — the Bonami–Beckner /
Nelson–Gross hypercontractivity machinery is not formalised in any
ambient form.  Stating it would require, at minimum, an `MeasureTheory`
infrastructure for `Lp` norms over the discrete cube and over Gaussian
space, plus the tensorisation argument at general `p`.  The blueprint
only ever invokes the leaf case `(4, 2)`, which is exactly the headline
of `LeaHadamard/Mathlib/Hypercontractive.lean`.

The theorem below therefore packages the leaf case under the requested
name `fixedDegreeHC_degree2_W_fourth` (= "fixed degree 2 hypercontractive,
Walsh, fourth moment").  Its proof is a direct application of
`hc_degree2_fourth`.
-/

import Mathlib
import LeaHadamard.Mathlib.Hypercontractive

open scoped BigOperators
open LeaHadamard.SignAverage
open LeaHadamard.Hypercontractive

namespace LeaHadamard
namespace Hadamard

/--
**Fixed-degree hypercontractive inequality, Walsh form, fourth moment.**

For every Walsh polynomial `p` of degree ≤ 2 in `n` Rademacher variables,

  E[p^4] ≤ 81 · (E[p^2])^2,

equivalently `‖p‖₄ ≤ 3 · ‖p‖₂`.  The constant `81 = 3^4` is exactly
`((p − 1)^{q/2})^p` at `(p, q) = (4, 2)`, matching the general
Bonami–Beckner bound `‖H‖_{L^p} ≤ (p − 1)^{q/2} · ‖H‖_{L^2}`.

This is the leaf instance of the general hypercontractive inequality
that is actually invoked in the blueprint.  The proof is a direct
application of `hc_degree2_fourth` from
`LeaHadamard.Mathlib.Hypercontractive`.
-/
theorem fixedDegreeHC_degree2_W_fourth {n : ℕ} (p : WalshDeg2 n) :
    avgSigns n (fun σ => (eval p σ) ^ 4)
      ≤ 81 * (avgSigns n (fun σ => (eval p σ) ^ 2)) ^ 2 :=
  hc_degree2_fourth p

end Hadamard
end LeaHadamard
