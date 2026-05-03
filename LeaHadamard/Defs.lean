/-
# Canonical shared definitions for the Hadamard formalization

This module collects the foundational objects that the layer-0 lemmas
defined privately and that layer-1+ lemmas will share.

The names below are the *canonical* forms. They live in `LeaHadamard.Defs`
so they don't collide with the file-local definitions inside
`LeaHadamard.Hadamard.Lem_realpart` or other layer-0 files (which have
their own `rad`, `psi`, `Xform`, `sval` for self-contained proofs).

Future lemmas (layer-1+) should `import LeaHadamard.Defs` and use
`LeaHadamard.Defs.psi` / `LeaHadamard.Defs.rad` / etc. directly.

If we eventually refactor the layer-0 files to drop their locals in
favor of these canonical versions, we'd add equivalence lemmas of the
form `Lem_realpart.psi p lam = LeaHadamard.Defs.psi p lam` (definitional)
and update the proofs. That refactor is **not** part of this commit;
this is purely additive.
-/

import Mathlib

open scoped BigOperators
open Complex Real

namespace LeaHadamard.Defs

/-! ## Rademacher signs -/

/-- Rademacher sign attached to a boolean: `true ↦ 1`, `false ↦ -1`. -/
def rad (b : Bool) : ℝ := if b then 1 else -1

lemma rad_sq (b : Bool) : rad b * rad b = 1 := by
  cases b <;> simp [rad]

lemma rad_pow_two (b : Bool) : (rad b) ^ 2 = 1 := by
  rw [sq]; exact rad_sq b

lemma abs_rad (b : Bool) : |rad b| = 1 := by
  cases b <;> simp [rad]

lemma rad_not (b : Bool) : rad (!b) = -rad b := by
  cases b <;> simp [rad]

lemma rad_ne_zero (b : Bool) : rad b ≠ 0 := by
  cases b <;> simp [rad]

/-! ## Quadratic forms -/

/-- E-indexed quadratic Rademacher form
    `Xform p lam ξ = ∑_e lam e · rad (ξ (p e).1) · rad (ξ (p e).2)`. -/
noncomputable def Xform {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) (ξ : Fin n → Bool) : ℝ :=
  ∑ e, lam e * rad (ξ (p e).1) * rad (ξ (p e).2)

/-- Matrix-form quadratic Rademacher phase, summed over `i < j`. -/
noncomputable def phaseMatrix {n : ℕ}
    (γ : Fin n → Fin n → ℝ) (ξ : Fin n → Bool) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
    γ p.1 p.2 * rad (ξ p.1) * rad (ξ p.2)

/-! ## Characteristic function ψ -/

/-- E-indexed characteristic function:
    `psi p lam = E_ξ [exp(i · Xform p lam ξ)]`,
    where the expectation is over the uniform distribution on Rademacher
    sign vectors. -/
noncomputable def psi {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℂ :=
  ((1 : ℝ) / (2 : ℝ) ^ n : ℝ) *
    ∑ ξ : Fin n → Bool, Complex.exp (Complex.I * (Xform p lam ξ : ℂ))

/-- Matrix-form characteristic function:
    `psiMatrix γ = E_ξ [exp(i · phaseMatrix γ ξ)]`. -/
noncomputable def psiMatrix {n : ℕ} (γ : Fin n → Fin n → ℝ) : ℂ :=
  ((1 : ℝ) / (2 ^ n : ℝ) : ℂ) *
    ∑ ξ : Fin n → Bool, Complex.exp (Complex.I * (phaseMatrix γ ξ : ℂ))

/-! ## Energy -/

/-- The energy `s(λ) := Σ_e λ_e²` (E-indexed). -/
noncomputable def sval {E : Type*} [Fintype E] (lam : E → ℝ) : ℝ :=
  ∑ e, (lam e) ^ 2

lemma sval_nonneg {E : Type*} [Fintype E] (lam : E → ℝ) :
    0 ≤ sval lam :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end LeaHadamard.Defs
