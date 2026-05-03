/-
# Gaussian moment infrastructure (Stage 7b)

Moment bounds for Gaussian linear forms `⟨a, x⟩` against the unnormalized
Gaussian density `e^{-2t‖x‖²}` on `EuclideanSpace ℝ (Fin d)`.

This is the Gaussian analogue of `LeaHadamard/Mathlib/SignAverage.lean`
(which provides the second/fourth moment identities for Rademacher
linear forms).

## Definitions

* `gaussWeight t x = exp(-2t‖x‖²)` — the unnormalized Gaussian density.
* `gaussNormConst d t = (π/(2t))^{d/2}` — the integral of `gaussWeight`.
* `gaussAvg t f = (∫ f · gaussWeight) / gaussNormConst` — Gaussian
  expectation of `f`.
* `gaussLinear a x = ⟨a, x⟩` — the linear form.

## Headline lemmas

* `gauss_linear_sq_bound` — second moment of the linear form.
* `gauss_linear_fourth_bound` — fourth moment of the linear form.
* `gauss_linear_pow_bound` — general `2k`-th moment.

All bounds are upper bounds with concrete constants packaged
as `∃ C, ...` in the same style as `Lem_gaussian_radial.gaussian_radial_moments`.
The constants are *not* `Classical.choice` — they are produced by the
proof witnesses inside the existential. This matches the project's
convention.

## Proof strategy

We use Cauchy–Schwarz: `⟨a, x⟩^{2k} ≤ ‖a‖^{2k} · ‖x‖^{2k}`. This
reduces to the *radial* moment bound for `‖x‖^{2k}` against the Gaussian
density, which is exactly what `Lem_gaussian_radial.gaussian_radial_moments`
provides.

Note: a tighter `d`-independent constant `C(k) · t^{-k}` is achievable
via direct Fubini parity-cancellation of cross terms `a_i a_j x_i x_j`
for `i ≠ j`. We leave that refinement for a follow-up; the present
Cauchy–Schwarz constants are sufficient for the downstream applications
(`lem:cubic`, `lem:quintic`, `lem:sixth`).
-/

import Mathlib
import LeaHadamard.Hadamard.Lem_gaussian_radial

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace LeaHadamard.GaussianMoments

/-! ## Definitions -/

/-- The unnormalized Gaussian density at temperature `t`. -/
noncomputable def gaussWeight {d : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-2 * t * ‖x‖^2)

/-- The Gaussian normalization constant `(π / (2t))^{d/2}`. -/
noncomputable def gaussNormConst (d : ℕ) (t : ℝ) : ℝ :=
  (Real.pi / (2 * t)) ^ ((d : ℝ) / 2)

/-- Average of `f` against the unnormalized Gaussian density, divided
by the normalization constant. -/
noncomputable def gaussAvg {d : ℕ} (t : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (∫ x : EuclideanSpace ℝ (Fin d), f x * gaussWeight t x) / gaussNormConst d t

/-- The Gaussian linear form `⟨a, x⟩`. -/
noncomputable def gaussLinear {d : ℕ} (a x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ a x

/-! ## Basic positivity / nonnegativity -/

lemma gaussNormConst_pos (d : ℕ) {t : ℝ} (ht : 0 < t) : 0 < gaussNormConst d t := by
  unfold gaussNormConst
  exact Real.rpow_pos_of_pos (div_pos Real.pi_pos (by linarith)) _

lemma gaussWeight_nonneg {d : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ gaussWeight t x := (Real.exp_pos _).le

lemma gaussWeight_pos {d : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 < gaussWeight t x := Real.exp_pos _

/-! ## Cauchy–Schwarz pointwise bound -/

/-- Cauchy–Schwarz for the Gaussian linear form: `⟨a, x⟩² ≤ ‖a‖² · ‖x‖²`. -/
lemma gaussLinear_sq_le_norm_sq {d : ℕ} (a x : EuclideanSpace ℝ (Fin d)) :
    (inner ℝ a x : ℝ)^2 ≤ ‖a‖^2 * ‖x‖^2 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) a x
  have habs : (inner ℝ a x : ℝ)^2 = ‖inner ℝ a x‖^2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [habs]
  have hprod : (‖a‖ * ‖x‖)^2 = ‖a‖^2 * ‖x‖^2 := by ring
  rw [← hprod]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Higher-power Cauchy–Schwarz: `⟨a, x⟩^{2k} ≤ ‖a‖^{2k} · ‖x‖^{2k}`. -/
lemma gaussLinear_pow_le_norm_pow {d : ℕ} (a x : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (inner ℝ a x : ℝ) ^ (2 * k) ≤ ‖a‖ ^ (2 * k) * ‖x‖ ^ (2 * k) := by
  have h := gaussLinear_sq_le_norm_sq a x
  have hsq_nn : 0 ≤ (inner ℝ a x : ℝ)^2 := sq_nonneg _
  have hpow_eq : (inner ℝ a x : ℝ) ^ (2 * k) = ((inner ℝ a x : ℝ)^2) ^ k := by
    rw [pow_mul]
  rw [hpow_eq]
  have hbound : ((inner ℝ a x : ℝ)^2) ^ k ≤ (‖a‖^2 * ‖x‖^2) ^ k :=
    pow_le_pow_left₀ hsq_nn h k
  calc ((inner ℝ a x : ℝ)^2) ^ k ≤ (‖a‖^2 * ‖x‖^2) ^ k := hbound
    _ = (‖a‖^2)^k * (‖x‖^2)^k := mul_pow _ _ _
    _ = ‖a‖ ^ (2 * k) * ‖x‖ ^ (2 * k) := by rw [← pow_mul, ← pow_mul]

/-! ## Integrability of the radial Gaussian moment integrand -/

/-- Pointwise envelope: `‖x‖^{2k} · exp(-(2t)‖x‖²) ≤ (k!/t^k) · exp(-t‖x‖²)`. -/
private lemma radial_pow_exp_envelope {d : ℕ} (k : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2) ≤
      (k.factorial : ℝ) / t ^ k * Real.exp (-t * ‖x‖ ^ 2) := by
  -- Set `r := ‖x‖`. Then we want a 1D-flavoured inequality on `r²`.
  set r : ℝ := ‖x‖ with hr_def
  have hr_nn : (0 : ℝ) ≤ r := norm_nonneg _
  -- Use the same algebraic manipulation as `pow_mul_exp_neg_two_t_sq_le` (in
  -- `Lem_gaussian_radial`), inlined here since that lemma is `private`.
  have hrsq_nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg _
  have htrsq_nn : (0 : ℝ) ≤ t * r ^ 2 := mul_nonneg ht.le hrsq_nn
  have htm : (0 : ℝ) < t ^ k := pow_pos ht k
  -- (tS)^k · exp(-tS) ≤ k!  for any S ≥ 0.
  have hub : (t * r ^ 2) ^ k * Real.exp (-(t * r ^ 2)) ≤ (k.factorial : ℝ) := by
    have h1 : (t * r ^ 2) ^ k / k.factorial ≤ Real.exp (t * r ^ 2) :=
      Real.pow_div_factorial_le_exp _ htrsq_nn k
    have h2 : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    have h3 : (t * r ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (t * r ^ 2) := by
      rw [div_le_iff₀ h2] at h1; linarith
    calc (t * r ^ 2) ^ k * Real.exp (-(t * r ^ 2))
        ≤ ((k.factorial : ℝ) * Real.exp (t * r ^ 2)) * Real.exp (-(t * r ^ 2)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      _ = (k.factorial : ℝ) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  -- Expand (t * r²)^k = t^k * r^{2k}.
  have hxpw : r ^ (2 * k) = (r ^ 2) ^ k := by rw [pow_mul]
  have hexpand : (t * r ^ 2) ^ k * Real.exp (-(t * r ^ 2)) =
      t ^ k * r ^ (2 * k) * Real.exp (-(t * r ^ 2)) := by
    rw [hxpw, mul_pow]
  rw [hexpand] at hub
  -- t^k * r^{2k} * exp(-t r²) ≤ k!.
  have hstep : r ^ (2 * k) * Real.exp (-(t * r ^ 2)) ≤ (k.factorial : ℝ) / t ^ k := by
    rw [le_div_iff₀ htm]
    nlinarith [hub, Real.exp_nonneg (-(t * r ^ 2))]
  -- Multiply by exp(-t r²) ≥ 0:
  have key :
    r ^ (2 * k) * Real.exp (-(t * r ^ 2)) * Real.exp (-(t * r ^ 2)) ≤
      (k.factorial : ℝ) / t ^ k * Real.exp (-(t * r ^ 2)) :=
    mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
  -- exp(-(2t) r²) = exp(-(t r²)) * exp(-(t r²)).
  have h2tr : -(2 * t) * r ^ 2 = -(t * r ^ 2) + -(t * r ^ 2) := by ring
  have hexp_split : Real.exp (-(2 * t) * r ^ 2) =
      Real.exp (-(t * r ^ 2)) * Real.exp (-(t * r ^ 2)) := by
    rw [h2tr, Real.exp_add]
  have hntr : Real.exp (-t * r ^ 2) = Real.exp (-(t * r ^ 2)) := by
    congr 1; ring
  show r ^ (2 * k) * Real.exp (-(2 * t) * r ^ 2) ≤
       (k.factorial : ℝ) / t ^ k * Real.exp (-t * r ^ 2)
  rw [hexp_split, ← mul_assoc, hntr]
  exact key

/-- Integrability of `exp(-b‖x‖²)` on `EuclideanSpace ℝ (Fin d)` for `b > 0`. -/
private lemma integrable_rexp_neg_mul_sq_norm
    {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖x‖ ^ 2)) := by
  -- Match the pattern from `Lem_inner_core`: use the complex Gaussian integrability
  -- on a finite-dimensional inner product space.
  have hbC : 0 < (b : ℂ).re := by simpa using hb
  have hint :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ (Fin d))
      (b := (b : ℂ)) hbC 0 (0 : EuclideanSpace ℝ (Fin d))
  have hint' : Integrable
      (fun v : EuclideanSpace ℝ (Fin d) => Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)) := by
    have heq : (fun v : EuclideanSpace ℝ (Fin d) =>
              Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)) =
            (fun v : EuclideanSpace ℝ (Fin d) =>
              Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + (0 : ℂ) * inner ℝ
                (0 : EuclideanSpace ℝ (Fin d)) v)) := by
      funext v; simp
    rw [heq]; exact hint
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin d),
      ‖Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)‖ = Real.exp (-b * ‖v‖ ^ 2) := by
    intro v
    rw [Complex.norm_exp]
    have h2 : -(b : ℂ) * (‖v‖ : ℂ) ^ 2 = ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2, Complex.ofReal_re]
  have hni := hint'.norm
  refine (hni.congr ?_)
  exact Filter.Eventually.of_forall (fun v => hnorm v)

/-- Integrability of `‖x‖^{2k} · exp(-(2t)‖x‖²)` on `EuclideanSpace ℝ (Fin d)`. -/
private lemma integrable_norm_pow_mul_gaussWeight
    {d : ℕ} (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2)) := by
  have h2t_pos : (0 : ℝ) < 2 * t := by linarith
  -- Comparison with `(k!/t^k) · exp(-t ‖x‖²)` via `radial_pow_exp_envelope`.
  have hint_majorant : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (k.factorial : ℝ) / t ^ k * Real.exp (-t * ‖x‖ ^ 2)) :=
    (integrable_rexp_neg_mul_sq_norm ht).const_mul _
  refine Integrable.mono' hint_majorant ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hnorm : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) := continuous_norm
    have hsq : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) := hnorm.pow 2
    have hpw : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (2 * k)) :=
      hnorm.pow (2 * k)
    have hexp : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
        Real.exp (-(2 * t) * ‖x‖ ^ 2)) :=
      Real.continuous_exp.comp ((continuous_const.mul hsq))
    exact hpw.mul hexp
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hnn : 0 ≤ ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2) :=
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact radial_pow_exp_envelope k ht x

/-! ## Continuity of `gaussWeight` and the linear-form integrand -/

private lemma continuous_gaussWeight {d : ℕ} (t : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => gaussWeight t x) := by
  unfold gaussWeight
  have hsq : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) :=
    (continuous_norm).pow 2
  exact Real.continuous_exp.comp ((continuous_const.mul hsq))

private lemma continuous_inner_left {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => (inner ℝ a x : ℝ)) := by
  exact (continuous_inner.comp (Continuous.prodMk continuous_const continuous_id))

/-- Integrability of the linear-form integrand
    `⟨a, x⟩^{2k} · gaussWeight t x` on `EuclideanSpace ℝ (Fin d)`. -/
private lemma integrable_gaussLinear_pow {d : ℕ} (k : ℕ) {t : ℝ} (ht : 0 < t)
    (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x) := by
  -- Compare to ‖a‖^{2k} * ‖x‖^{2k} * gaussWeight via Cauchy–Schwarz.
  have hgw_eq : ∀ x : EuclideanSpace ℝ (Fin d),
      gaussWeight t x = Real.exp (-(2 * t) * ‖x‖ ^ 2) := by
    intro x; unfold gaussWeight; congr 1; ring
  have hint_radial := integrable_norm_pow_mul_gaussWeight (d := d) k ht
  have hint_majorant : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x)) := by
    refine Integrable.const_mul ?_ _
    have heq : (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖x‖ ^ (2 * k) * gaussWeight t x) =
        (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2)) := by
      funext x; rw [hgw_eq]
    rw [heq]; exact hint_radial
  refine Integrable.mono' hint_majorant ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hpw : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
        (inner ℝ a x : ℝ) ^ (2 * k)) := (continuous_inner_left a).pow (2 * k)
    exact hpw.mul (continuous_gaussWeight t)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hcs := gaussLinear_pow_le_norm_pow a x k
    have hgw_nn := gaussWeight_nonneg t x
    have hpow_nn : 0 ≤ (inner ℝ a x : ℝ) ^ (2 * k) := by
      rw [show 2 * k = k + k from by ring, pow_add]
      exact mul_self_nonneg _
    have hlhs_nn : 0 ≤ (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x :=
      mul_nonneg hpow_nn hgw_nn
    rw [Real.norm_eq_abs, abs_of_nonneg hlhs_nn]
    have step : (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x ≤
        (‖a‖ ^ (2 * k) * ‖x‖ ^ (2 * k)) * gaussWeight t x :=
      mul_le_mul_of_nonneg_right hcs hgw_nn
    calc (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x
        ≤ (‖a‖ ^ (2 * k) * ‖x‖ ^ (2 * k)) * gaussWeight t x := step
      _ = ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x) := by ring

/-! ## Headline moment bounds for Gaussian linear forms -/

open LeaHadamard.Hadamard in
/-- General `2k`-th moment bound for the Gaussian linear form.

`∫ ⟨a, x⟩^{2k} · e^{-2t‖x‖²} dx ≤ C · ‖a‖^{2k} · (d/t)^k · (π/(2t))^{d/2}`.

The constant `C = √2 · k!` is the same one supplied by
`gaussian_radial_moments` in `Lem_gaussian_radial`. The factor `(d/t)^k`
carries the `d`-dependence inherited from the Cauchy–Schwarz reduction
to a radial moment bound. -/
theorem gauss_linear_pow_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ t : ℝ, 1 ≤ t →
        ∀ a : EuclideanSpace ℝ (Fin d),
          ∫ x : EuclideanSpace ℝ (Fin d),
              (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x ≤
            C * ‖a‖ ^ (2 * k) * ((d : ℝ) / t) ^ k * gaussNormConst d t := by
  -- Extract the constant from the radial moment lemma.
  obtain ⟨C, hC_pos, hC⟩ := gaussian_radial_moments k
  refine ⟨C, hC_pos, ?_⟩
  intro d hd t ht a
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  -- Pointwise Cauchy–Schwarz bound, against the *radial* integrand.
  have hgw_eq : ∀ x : EuclideanSpace ℝ (Fin d),
      gaussWeight t x = Real.exp (-(2 * t) * ‖x‖ ^ 2) := by
    intro x; unfold gaussWeight; congr 1; ring
  -- Step 1: ∫ ⟨a,x⟩^{2k} · gaussWeight ≤ ‖a‖^{2k} · ∫ ‖x‖^{2k} · gaussWeight.
  have hpw : ∀ x : EuclideanSpace ℝ (Fin d),
      (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x ≤
        ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x) := by
    intro x
    have hcs := gaussLinear_pow_le_norm_pow a x k
    have hgw_nn := gaussWeight_nonneg t x
    have step : (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x ≤
        (‖a‖ ^ (2 * k) * ‖x‖ ^ (2 * k)) * gaussWeight t x :=
      mul_le_mul_of_nonneg_right hcs hgw_nn
    calc (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x
        ≤ (‖a‖ ^ (2 * k) * ‖x‖ ^ (2 * k)) * gaussWeight t x := step
      _ = ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x) := by ring
  have hint_LHS := integrable_gaussLinear_pow k ht_pos a
  have hint_radial_gw : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖x‖ ^ (2 * k) * gaussWeight t x) := by
    have heq : (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖x‖ ^ (2 * k) * gaussWeight t x) =
        (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2)) := by
      funext x; rw [hgw_eq]
    rw [heq]
    exact integrable_norm_pow_mul_gaussWeight k ht_pos
  have hint_RHS : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x)) :=
    hint_radial_gw.const_mul _
  have hbound1 :
    ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x ≤
    ∫ x : EuclideanSpace ℝ (Fin d), ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x) := by
    exact integral_mono hint_LHS hint_RHS hpw
  -- Step 2: simplify the RHS integral as a constant times the radial integral.
  have hRHS_eq :
      ∫ x : EuclideanSpace ℝ (Fin d), ‖a‖ ^ (2 * k) * (‖x‖ ^ (2 * k) * gaussWeight t x) =
      ‖a‖ ^ (2 * k) *
        ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ (2 * k) * gaussWeight t x := by
    rw [integral_const_mul]
  -- Step 3: bound the radial integral by `gaussian_radial_moments`.
  have hradial_eq :
      ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ (2 * k) * gaussWeight t x =
      ∫ x : EuclideanSpace ℝ (Fin d),
        ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    show ‖y‖ ^ (2 * k) * gaussWeight t y =
         ‖y‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖y‖ ^ 2)
    rw [hgw_eq]
  have hradial_bound :
      ∫ x : EuclideanSpace ℝ (Fin d),
        ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2) ≤
      C * ((d : ℝ) / t) ^ k * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) :=
    hC d hd t ht
  -- gaussNormConst = (π/(2t))^(d/2).
  have hgnc_eq : gaussNormConst d t = (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := rfl
  -- Combine.
  have ha_pow_nn : 0 ≤ ‖a‖ ^ (2 * k) := pow_nonneg (norm_nonneg _) _
  calc ∫ x : EuclideanSpace ℝ (Fin d),
            (inner ℝ a x : ℝ) ^ (2 * k) * gaussWeight t x
      ≤ ‖a‖ ^ (2 * k) *
            ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ (2 * k) * gaussWeight t x := by
            rw [← hRHS_eq]; exact hbound1
    _ = ‖a‖ ^ (2 * k) *
            ∫ x : EuclideanSpace ℝ (Fin d),
              ‖x‖ ^ (2 * k) * Real.exp (-(2 * t) * ‖x‖ ^ 2) := by rw [hradial_eq]
    _ ≤ ‖a‖ ^ (2 * k) *
            (C * ((d : ℝ) / t) ^ k * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hradial_bound ha_pow_nn
    _ = C * ‖a‖ ^ (2 * k) * ((d : ℝ) / t) ^ k *
            (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by ring
    _ = C * ‖a‖ ^ (2 * k) * ((d : ℝ) / t) ^ k * gaussNormConst d t := by
        rw [hgnc_eq]

/-- Second moment bound for the Gaussian linear form (k = 1).

Specialization of `gauss_linear_pow_bound` to `k = 1`:
`∫ ⟨a, x⟩² · e^{-2t‖x‖²} ≤ C · ‖a‖² · (d/t) · (π/(2t))^{d/2}`. -/
theorem gauss_linear_sq_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ t : ℝ, 1 ≤ t →
        ∀ a : EuclideanSpace ℝ (Fin d),
          ∫ x : EuclideanSpace ℝ (Fin d),
              (inner ℝ a x : ℝ) ^ 2 * gaussWeight t x ≤
            C * ‖a‖ ^ 2 * ((d : ℝ) / t) * gaussNormConst d t := by
  obtain ⟨C, hC_pos, hC⟩ := gauss_linear_pow_bound 1
  refine ⟨C, hC_pos, ?_⟩
  intro d hd t ht a
  have h := hC d hd t ht a
  -- Rewrite `2 * 1 = 2` and `(d/t)^1 = d/t`.
  simp only [Nat.mul_one, pow_one] at h
  exact h

/-- Fourth moment bound for the Gaussian linear form (k = 2).

Specialization of `gauss_linear_pow_bound` to `k = 2`:
`∫ ⟨a, x⟩^4 · e^{-2t‖x‖²} ≤ C · ‖a‖^4 · (d/t)² · (π/(2t))^{d/2}`. -/
theorem gauss_linear_fourth_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ t : ℝ, 1 ≤ t →
        ∀ a : EuclideanSpace ℝ (Fin d),
          ∫ x : EuclideanSpace ℝ (Fin d),
              (inner ℝ a x : ℝ) ^ 4 * gaussWeight t x ≤
            C * ‖a‖ ^ 4 * ((d : ℝ) / t) ^ 2 * gaussNormConst d t := by
  obtain ⟨C, hC_pos, hC⟩ := gauss_linear_pow_bound 2
  refine ⟨C, hC_pos, ?_⟩
  intro d hd t ht a
  have h := hC d hd t ht a
  -- Rewrite `2 * 2 = 4`.
  have h4 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h4] at h
  exact h

end LeaHadamard.GaussianMoments
