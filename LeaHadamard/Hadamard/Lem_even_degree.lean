/-
# Even-degree characterization of `Λ`

Davis (arXiv:2603.30013), blueprint label `lem:even-degree`:

> Let `λ ∈ Λ₀` and let `λ^{(2)} ∈ {0,1}^d` be its mod-2 reduction,
> viewed as the edge-indicator of a subgraph `G_{λ^{(2)}}` of `K_n`.
> Then `λ ∈ Λ ⟺ every vertex `k ∈ {1,…,n}` has even degree in `G_{λ^{(2)}}`.

In `Lambda.lean` we **defined** `Λ` by the linear-algebraic incidence-zero
condition (vanishing of the mod-2 incidence sum). Here we prove that
this is equivalent to the combinatorial even-degree property, by
identifying the mod-2 sum with the cardinality of the incident "on" edges
modulo 2.
-/

import LeaHadamard.Hadamard.Lambda

open scoped BigOperators
open Finset

namespace LeaHadamard.Hadamard

variable {n : ℕ}

/-- The incidence-`ZMod 2` sum at vertex `v` equals the cast of the
`degree` (number of incident "on" edges) into `ZMod 2`. -/
lemma incidence_sum_eq_degree_cast (lam : Lambda_0 n) (v : Fin n) :
    (∑ e ∈ incidentSet n v, lam.parityZ e) = ((lam.degree v : ℕ) : ZMod 2) := by
  -- rewrite each summand as `if parity then 1 else 0`
  have hsum : (∑ e ∈ incidentSet n v, lam.parityZ e)
            = ∑ e ∈ incidentSet n v, (if lam.parity e then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simpa using Lambda_0.parityZ_eq lam e
  rw [hsum]
  -- now apply `sum_boole` which gives the cardinality of the filter.
  rw [Finset.sum_boole]
  -- rewrite `degree` as that cardinality.
  unfold Lambda_0.degree
  rfl

/-- A natural number `m` satisfies `(m : ZMod 2) = 0` iff `m` is even. -/
lemma natCast_zmod2_eq_zero_iff_even (m : ℕ) : ((m : ℕ) : ZMod 2) = 0 ↔ Even m := by
  rw [natCast_zmod2_eq_zero_iff, Nat.even_iff]

/-- **Even-degree characterization of `Λ`** (blueprint
`lem:even-degree`).

`λ ∈ Λ` iff every vertex `v` has even degree in the subgraph
`G_{λ^{(2)}}` (i.e. the number of edges incident to `v` whose mod-2
reduction is `true` is even). -/
theorem parityEvenBool_iff_incidence_zero (lam : Lambda_0 n) :
    lam ∈ Lambda n ↔ ∀ v : Fin n, Even (lam.degree v) := by
  rw [mem_Lambda]
  unfold InLambda
  refine forall_congr' (fun v => ?_)
  rw [incidence_sum_eq_degree_cast lam v, natCast_zmod2_eq_zero_iff_even]

end LeaHadamard.Hadamard
