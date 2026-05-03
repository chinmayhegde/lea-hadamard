/-
# Fixed-$n$ count asymptotic

Blueprint statement (informal):
  Let $N_{n,t}$ be the number of $n \times t$ partial Hadamard matrices,
  i.e. the number of $\pm 1$-valued $n \times t$ matrices whose rows are
  pairwise orthogonal.  Let
        $A_{n,t} := \binom{2n}{n}^{t/2}$
  be the Gaussian (lattice point) approximation.  Then for every fixed
  integer $n \ge 2$,
        $N_{n,4t} = [1 + o_{t\to\infty}(1)]\, A_{n,4t}$
  as $t \to \infty$.

We make the conclusion precise by stating that
        $N_{n,4t} / A_{n,4t} \longrightarrow 1$
  in the filter `Filter.atTop` on $t \in \mathbb{N}$.

This is the headline asymptotic of the paper and is genuinely beyond
reach without the rest of the formalization (lattice $\Lambda$, the
fourth-moment / Gaussian inversion bound, the disjoint-box decomposition,
etc.).  Hence the theorem statement is honest but the proof is `sorry`.
-/

import Mathlib
import LeaHadamard.Defs

open scoped BigOperators
open Filter Topology

namespace LeaHadamard
namespace Hadamard

/-- Indicator that an `n × t` matrix `M : Fin n → Fin t → ℝ` with values in
`{-1, +1}` is a *partial Hadamard matrix*: each entry is `±1` and any two
distinct rows are orthogonal. -/
def IsPartialHadamard (n t : ℕ) (M : Fin n → Fin t → ℝ) : Prop :=
  (∀ i j, M i j = 1 ∨ M i j = -1) ∧
    (∀ i k : Fin n, i ≠ k → ∑ j, M i j * M k j = 0)

/-- The set of `n × t` partial Hadamard matrices represented by sign assignments
`Fin n → Fin t → Bool` (with `true ↦ +1`, `false ↦ -1`). -/
noncomputable def partialHadamardSet (n t : ℕ) : Finset (Fin n → Fin t → Bool) := by
  classical
  exact (Finset.univ : Finset (Fin n → Fin t → Bool)).filter
    (fun σ => IsPartialHadamard n t (fun i j => LeaHadamard.Defs.rad (σ i j)))

/-- $N_{n,t}$: the number of $n \times t$ partial Hadamard matrices. -/
noncomputable def partialHadamardCount (n t : ℕ) : ℕ :=
  (partialHadamardSet n t).card

/-- $A_{n,t} := \binom{2n}{n}^{t/2}$, the Gaussian lattice-point approximation,
expressed as a real number.  We use $\binom{2n}{n}^{t/2} = \sqrt{\binom{2n}{n}}^{\,t}$;
equivalently for the regime `t = 4t'` we have an exact rational power. -/
noncomputable def gaussianApprox (n t : ℕ) : ℝ :=
  ((Nat.choose (2 * n) n : ℝ)) ^ ((t : ℝ) / 2)

/--
**Fixed-$n$ count asymptotic.**

For every fixed integer `n ≥ 2`, the ratio
$N_{n,4t}/A_{n,4t}$ tends to `1` as `t → ∞`, i.e.
$N_{n,4t} = [1 + o_{t\to\infty}(1)]\,A_{n,4t}$.

This is the main theorem of the paper.  Its proof requires the entire
formalization apparatus (lattice $\Lambda$, fourth-moment Gaussian inversion,
disjoint-box decomposition, triangle / inner-core / real-part bounds, etc.)
and is genuinely beyond reach as a leaf node — hence the `sorry`.
-/
theorem fixed_n_count_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Filter.Tendsto
      (fun t : ℕ =>
        (partialHadamardCount n (4 * t) : ℝ) / gaussianApprox n (4 * t))
      Filter.atTop (𝓝 (1 : ℝ)) := by
  -- The proof is the culmination of the paper.  It needs:
  --   * the lattice/box decomposition of `Lambda` (LeaHadamard.Hadamard.Lambda),
  --   * the Gaussian radial estimate (Lem_gaussian_radial),
  --   * the disjoint-box covering count (Lem_disjoint_boxes),
  --   * the inner-core / triangle / real-part lemmas,
  --   * a Tauberian / Laplace-method passage from finite-`t` moments
  --     to the `t → ∞` limit,
  -- none of which are in Mathlib.  We leave the asymptotic as `sorry`
  -- with this signature locked to the blueprint.
  sorry

end Hadamard
end LeaHadamard
