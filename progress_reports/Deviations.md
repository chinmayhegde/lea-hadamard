# Deviations from Davis's formalization

A running log of where our Lea-driven formalization differs from
Damek Davis's reference Lean code (https://github.com/damek/counting_hadamard).

We treat Davis's repo as a *reference oracle*: we don't read his proofs
before Lea attempts a lemma, but we compare afterwards. This file records
what's notably different — better, worse, or just different. Each entry
should give a future reader (or paper author) a feel for what an
independent autonomous formalization actually produces relative to a
careful human-driven one.

The categories below are stable; entries grow as more lemmas land.

---

## `lem:gaussian-radial` — landed 2026-05-02

**Notable deviation: stronger statement (uniform constant in `d`).**

Davis's Lean statement quantifies the constant for fixed `d`:
```lean
theorem gaussian_radial_moments (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ∫ x : Fin d → ℝ, (∑ i, x i ^ 2) ^ m * Real.exp (-2 * t * ∑ i, x i ^ 2)
        ≤ (C / t ^ m) * gaussianF d t
```
The implicit `C` here depends on both `d` and `m` (it's defined in terms
of an integral over `ℝ^d`).

Lea's statement quantifies `C` only over `m`, then enters the `∀ d`:
```lean
theorem gaussian_radial_moments :
    ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ t : ℝ, 1 ≤ t →
        ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖^(2*m) * Real.exp (-(2*t) * ‖x‖^2) ≤
          C * ((d : ℝ)/t)^m * (Real.pi/(2*t))^((d : ℝ)/2)
```
Lea proves `C = √2 · m!`. **This is a strictly stronger statement: a
uniform-in-`d` constant.** The blueprint's prose statement (in Davis's
manuscript) explicitly says "for every integer m ≥ 0 there is a constant
C_m > 0 ... for all d, t ≥ 1", so Lea's form is the one the *paper* states
(uniform in `d`); Davis's Lean weakens it to fixed `d` because his
downstream uses are at fixed `d` and weaker is fine.

Worth flagging: Lea's `√2 · m!` constant is almost certainly tight up to
a small factor (the `√2` slack comes from the factorial bound), while
Davis's `K / (2^m π^{d/2})` is the asymptotically sharp constant when
the integral is evaluated. So Lea's form is uniform in `d` but not as
sharp in the constant; Davis's is sharper but `d`-dependent.

**Notable deviation: different proof strategy.**

- Davis uses a change-of-variable argument: substitute `y = √(2t)·x`,
  reducing to a `d`-dimensional integral with no `t`-dependence (the
  constant `K`), then the `t^{-d/2 - m}` scaling factor falls out from
  the Jacobian via `MeasureTheory.Measure.integral_comp_smul`.
- Lea takes a pointwise-bound approach: prove `u^m e^{-u} ≤ m!`, lift it
  to `x^{2m} e^{-2tx²} ≤ (m!/t^m) e^{-tx²}`, then Fubini-reduce the
  `d`-dim integral to a product of 1D Gaussians.

These are very different routes. Davis's would generalize to *equalities*;
Lea's only proves the inequality direction (which is what the paper
states). For our purposes the inequality is enough.

**Notable deviation: ambient space type.**

- Davis: `Fin d → ℝ` with the explicit `∑ i, x i ^ 2` as the squared
  norm.
- Lea: `EuclideanSpace ℝ (Fin d)` with `‖x‖^2`, which equals the same
  `∑ i, x i ^ 2` but is the standard Mathlib-idiomatic way to express
  Euclidean space.

Both are valid; Lea's is more abstract (uses the inner-product space
machinery) and slightly easier for downstream uses that want
`InnerProductSpace`-flavored lemmas. Davis's is more concrete and
matches his other modules. No mathematical difference.

**Constants table:**

| Aspect | Davis | Lea |
|---|---|---|
| Statement form | `(C(d,m) / t^m) · gaussianF(d,t)` | `C(m) · (d/t)^m · (π/(2t))^{d/2}` |
| Constant explicit value | `K / (2^m π^{d/2}) + 1` | `√2 · m!` |
| Constant grows with `d`? | yes | no |
| Constant grows with `m`? | factorially (via `K`) | factorially |

**File**: `LeaHadamard/Hadamard/Lem_gaussian_radial.lean` (576 lines).
**Cost**: ~$30 actual.
**Trust**: clean Mathlib axioms (`propext, Classical.choice, Quot.sound`).
