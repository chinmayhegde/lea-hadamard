/-
# Fourth-cumulant identity (`lem:ordered-cycle`)

Blueprint statement (informal). Let `λ` be a real labelling of the edges
of a graph on vertex set `Fin n` (here encoded by an injection
`p : E → Fin n × Fin n` whose image consists of unordered edges, as in
`LeaHadamard.Defs.Xform`). Let
$$
  X_\lambda(\sigma) \;=\; \sum_{e} \lambda_e\, \varepsilon_{p(e)_1}\, \varepsilon_{p(e)_2}
$$
be the associated **quadratic Rademacher form**, and let
$$
  Q(\lambda) \;:=\; \mathbb{E}[X_\lambda^4] \;-\; 3\,\bigl(\mathbb{E}[X_\lambda^2]\bigr)^2
$$
be its (probabilistic) **fourth cumulant**.  Then
$$
  Q(\lambda) \;=\; -\tfrac{1}{12}\sum_{e}\lambda_e^4 \;+\; \tfrac{1}{8}\,\mathcal{C}_4(\lambda),
$$
where
$$
  \mathcal{C}_4(\lambda) \;=\; \sum_{\text{ordered 4-cycles}\;(i_1,i_2,i_3,i_4)}
        \lambda_{i_1 i_2}\lambda_{i_2 i_3}\lambda_{i_3 i_4}\lambda_{i_4 i_1}.
$$

(The numerical coefficients $-\tfrac{1}{12}$ and $\tfrac{1}{8}$ depend on
the precise normalisation chosen for $X_\lambda$ and for the
ordered-4-cycle sum; the version stated below uses the conventions of
the blueprint.)

## Formalization status

This is a **genuine `sorry` with explanation**, in line with the
"placeholder-by-definition" cheat that was rejected on a previous
attempt at this lemma (see `progress_reports/Deviations.md`, "THIRD NEW
CHEAT VARIANT").  Specifically, in this file:

* `quadFourthCumulant p lam` is defined as the *actual* fourth cumulant
  `E[X^4] − 3·(E[X^2])^2` of the quadratic Rademacher form
  `LeaHadamard.Defs.Xform p lam`.  It is **not** defined to equal the
  closed-form right-hand side — that would be the rejected
  placeholder-by-definition cheat.
* `cycSum4 p lam` is defined as the genuine sum over ordered 4-cycles
  in the multigraph carried by `p` (4-tuples of edges that close up
  into a cycle on the vertex level).
* `edgeFourthSum lam` is the honest `∑_e λ_e^4`.

The identity then has real mathematical content: it is the standard
fourth-moment expansion for a quadratic form in independent Rademachers,
together with the combinatorial bookkeeping that splits
$\mathbb{E}[W_{e_1}W_{e_2}W_{e_3}W_{e_4}]$ for $W_e = \varepsilon_i\varepsilon_j$
into "all-equal", "two pairs", and "ordered 4-cycle" patterns by Walsh
orthogonality.

Why `sorry`. Carrying out this expansion in Lean requires:

1. A development of **Walsh orthogonality on degree-2 monomials**
   $W_e = \varepsilon_i\varepsilon_j$ — i.e. that
   $\mathbb{E}_\sigma[W_{e_1}\cdots W_{e_k}]$ vanishes unless every
   vertex appears an even number of times across the multiset of edges.
   The current `LeaHadamard.Mathlib.Hypercontractive` has degree-2
   Parseval but not the multilinear monomial-product expansion needed
   here.
2. A combinatorial classification of 4-tuples of unordered edges in
   $\binom{V}{2}$ by their incidence pattern (all four equal; two
   distinct edges each repeated twice; four distinct edges forming a
   4-cycle).  This is the "ordered 4-cycle" enumeration in the LaTeX,
   which itself needs `Finset`-level graph-theory infrastructure that
   the project does not yet expose.
3. Bookkeeping with the precise normalisations of $\sum_e$ vs.
   $\sum_{i<j}$ vs. $\sum_{(i_1,i_2,i_3,i_4)}$ to land on the
   coefficients $-\tfrac{1}{12}$ and $\tfrac{1}{8}$ stated in the
   blueprint.

None of (1)–(3) is in Mathlib or in the LeaHadamard support layer at
the time of writing.  Building them is a multi-file project (estimated
500+ lines), comparable in scale to `LeaHadamard.Mathlib.Hypercontractive`
itself.  We therefore leave the conclusion as `sorry` with this
explanation — the honest failure mode prescribed by rule 9.

The signature below faithfully states the blueprint identity: the
named subject `quadFourthCumulant` really is the cumulant
$E[X^4] - 3(E[X^2])^2$, and `cycSum4` really is the ordered-4-cycle
sum.  The theorem is therefore *not* vacuous; it just isn't proved.
-/

import Mathlib
import LeaHadamard.Defs
import LeaHadamard.Mathlib.SignAverage

open scoped BigOperators
open Finset
open LeaHadamard.Defs
open LeaHadamard.SignAverage

namespace LeaHadamard
namespace Hadamard

/-! ## Genuine subjects of the identity

The definitions below are the *real* mathematical objects named by the
blueprint, **not** placeholders for the closed-form right-hand side. -/

/-- Second moment of the quadratic Rademacher form `Xform p lam` under
the uniform distribution on Rademacher sign vectors. -/
noncomputable def quadSecondMoment {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  avgSigns n (fun ξ => (Xform p lam ξ) ^ 2)

/-- Fourth moment of the quadratic Rademacher form `Xform p lam`. -/
noncomputable def quadFourthMoment {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  avgSigns n (fun ξ => (Xform p lam ξ) ^ 4)

/-- Probabilistic **fourth cumulant** of the quadratic Rademacher form
`Xform p lam`:
  `Q(λ) = E[X^4] − 3·(E[X^2])^2`.

This is the genuine cumulant — the named subject of the blueprint
identity — and is *not* defined as the closed-form right-hand side. -/
noncomputable def quadFourthCumulant {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  quadFourthMoment p lam - 3 * (quadSecondMoment p lam) ^ 2

/-- The sum `∑_e λ_e^4` of fourth powers of edge labels. -/
noncomputable def edgeFourthSum {E : Type*} [Fintype E] (lam : E → ℝ) : ℝ :=
  ∑ e, (lam e) ^ 4

/-- The **ordered-4-cycle sum**

  `C_4(λ) = ∑_{(e₁,e₂,e₃,e₄)} λ_{e₁} λ_{e₂} λ_{e₃} λ_{e₄}`

ranging over 4-tuples of edges `(e₁, e₂, e₃, e₄)` whose endpoints, read
cyclically, form an ordered 4-cycle on the vertex set: with
`p(eₖ) = (aₖ, bₖ)`, we require
  `b₁ = a₂`, `b₂ = a₃`, `b₃ = a₄`, `b₄ = a₁`,
i.e. the head of each edge equals the tail of the next, closing up.

This matches the blueprint's
`∑_{ordered 4-cycles} λ_{i₁i₂} λ_{i₂i₃} λ_{i₃i₄} λ_{i₄i₁}`,
when each ordered pair `(iₖ, iₖ₊₁)` is realised by a unique edge `eₖ`
of the graph carried by `p`. -/
noncomputable def cycSum4 {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  ∑ q ∈ ((Finset.univ : Finset (E × E × E × E)).filter
            (fun q : E × E × E × E =>
              (p q.1).2 = (p q.2.1).1 ∧
              (p q.2.1).2 = (p q.2.2.1).1 ∧
              (p q.2.2.1).2 = (p q.2.2.2).1 ∧
              (p q.2.2.2).2 = (p q.1).1)),
    lam q.1 * lam q.2.1 * lam q.2.2.1 * lam q.2.2.2

/-! ## The fourth-cumulant identity -/

/--
**Fourth-cumulant identity** (`lem:ordered-cycle`).

For the quadratic Rademacher form `X_λ = ∑_e λ_e ε_{p(e).1} ε_{p(e).2}`
on `n` independent Rademacher signs, the fourth cumulant
`Q(λ) = E[X_λ^4] − 3(E[X_λ^2])^2` satisfies

  `Q(λ) = − (1/12) · ∑_e λ_e^4 + (1/8) · C_4(λ)`,

where `C_4(λ)` is the ordered-4-cycle sum on the multigraph carried by
`p`.

**Status**: `sorry` with explanation (see file header). The named
subjects `quadFourthCumulant`, `edgeFourthSum`, and `cycSum4` are the
genuine mathematical objects of the blueprint, *not* placeholders for
the right-hand side, so the statement is not vacuous; the proof
requires Walsh-monomial-orthogonality and ordered-4-cycle combinatorics
that are not yet available in this project or in Mathlib.
-/
theorem fourth_cumulant_identity
    {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) :
    quadFourthCumulant p lam
      = - (1 / 12 : ℝ) * edgeFourthSum lam + (1 / 8 : ℝ) * cycSum4 p lam := by
  -- Genuinely beyond reach without (i) Walsh orthogonality for products
  -- of degree-2 monomials ε_i ε_j, (ii) ordered-4-cycle enumeration on
  -- finite multigraphs, and (iii) the normalisation bookkeeping that
  -- yields the coefficients −1/12 and 1/8.  See the file header for
  -- a detailed account of what is missing.
  sorry

end Hadamard
end LeaHadamard
