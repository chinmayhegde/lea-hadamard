/-
# Bonami two-point inequality (Stage 4)

This file builds on the Stage 1+2 discrete moment layer
(`LeaHadamard/Mathlib/SignAverage.lean`) and adds:

* `avgSigns_linearX_fourth_le_three_sq_second_sq` — the immediate
  L⁴ ≤ √3 · L² bound for Rademacher linear forms;

* `bonami_two_point_fourth` — the headline two-point inequality for
  arbitrary `a, b ∈ ℝ` in its L⁴-vs-(L²)² form;

* `bonami_two_point_two_var` — the Bonami–Beckner two-point base case
  for arbitrary `f : Bool × Bool → ℝ` (every such `f` is automatically
  a degree-≤-2 polynomial in two Rademacher variables).
-/

import Mathlib
import LeaHadamard.Mathlib.SignAverage

open scoped BigOperators
open Finset
open LeaHadamard.SignAverage

namespace LeaHadamard.BonamiTwoPoint

/-! ## A. Linear-form corollary of Stage 2 -/

/--
For Rademacher *linear forms* `linearX n x σ = ∑ i, x i · rad (σ i)` we
get the L⁴ ≤ √3 · L² bound for free from the second- and fourth-moment
identities established in Stage 2:

`E[linearX⁴] = 3·(∑ x²)² − 2·∑ x⁴ ≤ 3·(∑ x²)² = 3·(E[linearX²])²`.
-/
lemma avgSigns_linearX_fourth_le_three_sq_second_sq
    (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => (linearX n x σ) ^ 4)
      ≤ 3 * (avgSigns n (fun σ => (linearX n x σ) ^ 2)) ^ 2 := by
  rw [avgSigns_linearX_four, avgSigns_linearX_sq]
  have hx4_nonneg : (0 : ℝ) ≤ ∑ i : Fin n, (x i) ^ 4 := by
    refine Finset.sum_nonneg ?_
    intro i _
    positivity
  nlinarith [hx4_nonneg]

/-! ## B. The Bonami two-point inequality -/

/--
The Bonami–Beckner two-point inequality in its L⁴-vs-(L²)² form: for
all `a b : ℝ`,

`((a+b)⁴ + (a−b)⁴) / 2 ≤ 9 · (((a+b)² + (a−b)²)/2)²`.

The LHS equals `a⁴ + 6 a²b² + b⁴`; the RHS equals `9 (a² + b²)²`.
The gap is `8 a⁴ + 12 a²b² + 8 b⁴ ≥ 0`.
-/
theorem bonami_two_point_fourth (a b : ℝ) :
    (((a + b) ^ 4 + (a - b) ^ 4) / 2)
      ≤ 9 * (((a + b) ^ 2 + (a - b) ^ 2) / 2) ^ 2 := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a * b), sq_nonneg (a^2 - b^2),
             sq_nonneg (a^2 + b^2), sq_nonneg (a + b), sq_nonneg (a - b)]

/-! ## C. The two-point inequality at degree 2 over `Bool × Bool` -/

/--
The Bonami–Beckner two-point base case for arbitrary functions
`f : Bool × Bool → ℝ`. Since `Bool × Bool` has only four points, every
such `f` is automatically a polynomial of degree ≤ 2 in the two
Rademacher coordinates. The inequality

`((∑ f p ⁴)/4) ≤ 9 · ((∑ f p ²)/4)²`

is the L⁴ ≤ 3 · L² statement under the uniform measure on `Bool × Bool`.
The constant `9` is not tight (the truth is closer to `4 = (√2)⁴`),
but `9` matches the named Bonami inequality and is the form Davis's
chain expects.
-/
theorem bonami_two_point_two_var (f : Bool × Bool → ℝ) :
    ((∑ p : Bool × Bool, f p ^ 4) / 4)
      ≤ 9 * (((∑ p : Bool × Bool, f p ^ 2) / 4)) ^ 2 := by
  -- Enumerate the four points.
  set a := f (true, true)
  set b := f (true, false)
  set c := f (false, true)
  set d := f (false, false)
  have hsum4 : (∑ p : Bool × Bool, f p ^ 4) = a^4 + b^4 + c^4 + d^4 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    show f (true, true) ^ 4 + f (true, false) ^ 4
          + (f (false, true) ^ 4 + f (false, false) ^ 4)
        = a^4 + b^4 + c^4 + d^4
    ring
  have hsum2 : (∑ p : Bool × Bool, f p ^ 2) = a^2 + b^2 + c^2 + d^2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    show f (true, true) ^ 2 + f (true, false) ^ 2
          + (f (false, true) ^ 2 + f (false, false) ^ 2)
        = a^2 + b^2 + c^2 + d^2
    ring
  rw [hsum4, hsum2]
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d,
             sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - d^2),
             sq_nonneg (b^2 - c^2), sq_nonneg (b^2 - d^2), sq_nonneg (c^2 - d^2),
             sq_nonneg (a^2 + b^2 + c^2 + d^2),
             sq_nonneg (a*b), sq_nonneg (c*d),
             sq_nonneg (a + b + c + d)]

end LeaHadamard.BonamiTwoPoint
