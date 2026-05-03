/-
# Davis's `T`, `Q`, `P` functionals + low-order cumulants of `X_λ` (Stage 7a)

In Davis's paper, the log-expansion of `ψ(λ) = E[exp(i · X_λ)]` near
`λ = 0` is
```
log ψ(λ) = -½ · s(λ) - i · T(λ) + Q(λ) + i · P(λ) + E_6(λ)
```
where `T, Q, P` are the imaginary-cubic, real-quartic, and
imaginary-quintic terms of the Taylor expansion of `log` of the
characteristic function. They are (rescaled) cumulants of the
Rademacher quadratic form `X_λ = Xform p lam`:

  - `T(λ) = (1/6)   · κ₃(X_λ) = (1/6)   · E[X_λ³]`             (centered)
  - `Q(λ) = (1/24)  · κ₄(X_λ)`
  - `P(λ) = (1/120) · κ₅(X_λ)`

This file provides:
* `moment n k f` – the `k`-th moment of `f : (Fin n → Bool) → ℝ` under
  the uniform Rademacher measure.
* `cumulant3`, `cumulant4`, `cumulant5` – the genuine
  moment-polynomial expressions for the third, fourth, and fifth
  cumulants of a real random variable.
* `cumulant3_of_centered`, `cumulant4_of_centered`,
  `cumulant5_of_centered` – simplifications when the first moment
  vanishes.
* `T_func`, `Q_func`, `P_func` – Davis's three functionals, defined
  on top of cumulants of `Xform p lam`.

This is a foundational definition file; no nontrivial inequalities
are proved here.
-/

import Mathlib
import LeaHadamard.Defs
import LeaHadamard.Mathlib.SignAverage

open scoped BigOperators

namespace LeaHadamard.Hadamard.Functionals

open LeaHadamard.SignAverage (avgSigns)

/-! ## A. Moments and cumulants of a real random variable -/

/-- The `k`-th moment of a real-valued function `f` on `(Fin n → Bool)`
    under the uniform Rademacher measure. -/
noncomputable def moment (n k : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  avgSigns n (fun σ => (f σ) ^ k)

/-- Third cumulant `κ₃ = m₃ − 3 m₁ m₂ + 2 m₁³`.
    For centered `f` (i.e. `m₁ = 0`), this simplifies to `m₃`. -/
noncomputable def cumulant3 (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  moment n 3 f
    - 3 * moment n 1 f * moment n 2 f
    + 2 * (moment n 1 f) ^ 3

/-- Fourth cumulant
    `κ₄ = m₄ − 4 m₁ m₃ − 3 m₂² + 12 m₁² m₂ − 6 m₁⁴`.
    For centered `f`, this simplifies to `m₄ − 3 m₂²`. -/
noncomputable def cumulant4 (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  moment n 4 f
    - 4 * moment n 1 f * moment n 3 f
    - 3 * (moment n 2 f) ^ 2
    + 12 * (moment n 1 f) ^ 2 * moment n 2 f
    - 6 * (moment n 1 f) ^ 4

/-- Fifth cumulant
    `κ₅ = m₅ − 5 m₁ m₄ − 10 m₂ m₃ + 20 m₁² m₃ + 30 m₁ m₂²
          − 60 m₁³ m₂ + 24 m₁⁵`.
    For centered `f`, this simplifies to `m₅ − 10 m₂ m₃`. -/
noncomputable def cumulant5 (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  moment n 5 f
    - 5 * moment n 1 f * moment n 4 f
    - 10 * moment n 2 f * moment n 3 f
    + 20 * (moment n 1 f) ^ 2 * moment n 3 f
    + 30 * moment n 1 f * (moment n 2 f) ^ 2
    - 60 * (moment n 1 f) ^ 3 * moment n 2 f
    + 24 * (moment n 1 f) ^ 5

/-! ### Centered-form simplifications -/

/-- For centered `f` (`m₁ = 0`), `κ₃ = m₃`. -/
lemma cumulant3_of_centered {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : moment n 1 f = 0) :
    cumulant3 n f = moment n 3 f := by
  unfold cumulant3
  rw [hf]
  ring

/-- For centered `f` (`m₁ = 0`), `κ₄ = m₄ − 3 m₂²`. -/
lemma cumulant4_of_centered {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : moment n 1 f = 0) :
    cumulant4 n f = moment n 4 f - 3 * (moment n 2 f) ^ 2 := by
  unfold cumulant4
  rw [hf]
  ring

/-- For centered `f` (`m₁ = 0`), `κ₅ = m₅ − 10 m₂ m₃`. -/
lemma cumulant5_of_centered {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : moment n 1 f = 0) :
    cumulant5 n f = moment n 5 f - 10 * moment n 2 f * moment n 3 f := by
  unfold cumulant5
  rw [hf]
  ring

/-! ## B. Davis's `T`, `Q`, `P` functionals

The random variable is the Rademacher quadratic form
`Xform p lam ξ = ∑_e λ_e · rad(ξ_{p(e).1}) · rad(ξ_{p(e).2})`
from `LeaHadamard.Defs`. It is centered (`E[X_λ] = 0`) provided the
edges avoid the diagonal — see `LeaHadamard.Hadamard.Lem_triangle`
for the relevant identities.
-/

open LeaHadamard.Defs (Xform)

/-- Davis's `T` functional: `(1/6) · E[X_λ³]`, equivalently
    `(1/6) · κ₃(X_λ)` on centered `X_λ`. -/
noncomputable def T_func {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  (1 / 6 : ℝ) * cumulant3 n (fun ξ : Fin n → Bool => Xform p lam ξ)

/-- Davis's `Q` functional: `(1/24) · κ₄(X_λ)`, the rescaled fourth
    cumulant of `X_λ`. -/
noncomputable def Q_func {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  (1 / 24 : ℝ) * cumulant4 n (fun ξ : Fin n → Bool => Xform p lam ξ)

/-- Davis's `P` functional: `(1/120) · κ₅(X_λ)`, the rescaled fifth
    cumulant of `X_λ`. -/
noncomputable def P_func {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℝ :=
  (1 / 120 : ℝ) * cumulant5 n (fun ξ : Fin n → Bool => Xform p lam ξ)

/-! ### Centered-form simplifications for the functionals

When `X_λ` has zero first moment under the uniform Rademacher measure
(which holds whenever the edges `p e` avoid the diagonal), the three
functionals reduce to direct expressions in the moments of `X_λ`.
-/

/-- If `X_λ` is centered, `T_func = (1/6) · m₃(X_λ)`. -/
lemma T_func_of_centered {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ)
    (hX : moment n 1 (fun ξ : Fin n → Bool => Xform p lam ξ) = 0) :
    T_func p lam
      = (1 / 6 : ℝ) * moment n 3 (fun ξ : Fin n → Bool => Xform p lam ξ) := by
  unfold T_func
  rw [cumulant3_of_centered _ hX]

/-- If `X_λ` is centered, `Q_func = (1/24) · (m₄ − 3 m₂²)`. -/
lemma Q_func_of_centered {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ)
    (hX : moment n 1 (fun ξ : Fin n → Bool => Xform p lam ξ) = 0) :
    Q_func p lam
      = (1 / 24 : ℝ) *
          (moment n 4 (fun ξ : Fin n → Bool => Xform p lam ξ)
            - 3 * (moment n 2 (fun ξ : Fin n → Bool => Xform p lam ξ)) ^ 2) := by
  unfold Q_func
  rw [cumulant4_of_centered _ hX]

/-- If `X_λ` is centered, `P_func = (1/120) · (m₅ − 10 m₂ m₃)`. -/
lemma P_func_of_centered {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ)
    (hX : moment n 1 (fun ξ : Fin n → Bool => Xform p lam ξ) = 0) :
    P_func p lam
      = (1 / 120 : ℝ) *
          (moment n 5 (fun ξ : Fin n → Bool => Xform p lam ξ)
            - 10 * moment n 2 (fun ξ : Fin n → Bool => Xform p lam ξ)
                  * moment n 3 (fun ξ : Fin n → Bool => Xform p lam ξ)) := by
  unfold P_func
  rw [cumulant5_of_centered _ hX]

/-! ## C. Cross-reference

`T_func p lam` corresponds to `(1/6) · E[X_λ³]`, the same quantity
that appears (in possibly slightly different notation) in
`LeaHadamard.Hadamard.Lem_triangle`. A definitional equality lemma
between the two phrasings could be added once the layer-0 file is
refactored to share the canonical `Xform`/`avgSigns` from
`LeaHadamard.Defs` and `LeaHadamard.Mathlib.SignAverage`. -/

end LeaHadamard.Hadamard.Functionals
