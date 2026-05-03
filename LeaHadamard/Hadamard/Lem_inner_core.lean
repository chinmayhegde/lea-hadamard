import Mathlib

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace LeaHadamard.Hadamard

/-! ## Core Gaussian mass lemma

We prove that the integral of `exp(-2t‖λ‖²)` over the ball `‖λ‖² ≤ d/t`
captures all but an exponentially-small fraction of the full Gaussian mass.

The proof is by a Markov-style estimate: on the complement
`{‖λ‖² > d/t}`, we have `e^{-2t‖λ‖²} ≤ e^{-d} e^{-t‖λ‖²}`. Integrating,
the tail is at most `e^{-d} (π/t)^{d/2} = (2/e²)^{d/2} (π/(2t))^{d/2}`,
so we may take `c_* = 1 - (1/2) ln 2 > 0`.
-/

/-- The full multivariate Gaussian integral, real version: `∫ e^{-b‖v‖²} = (π/b)^{d/2}`. -/
private lemma integral_rexp_neg_mul_sq_norm_euclidean
    {d : ℕ} {b : ℝ} (hb : 0 < b) :
    ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖v‖ ^ 2) =
      (Real.pi / b) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin d)) hb
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h
  exact h

/-- The integrand `exp(-b‖v‖²)` is integrable on `EuclideanSpace ℝ (Fin d)`. -/
private lemma integrable_rexp_neg_mul_sq_norm_euclidean
    {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖v‖ ^ 2)) := by
  have hbC : 0 < (b : ℂ).re := by simpa using hb
  have hint :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ (Fin d))
      (b := (b : ℂ)) hbC 0 (0 : EuclideanSpace ℝ (Fin d))
  -- Simplify the complex integrand to the real-coerced version.
  have hint' : Integrable
      (fun v : EuclideanSpace ℝ (Fin d) => Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)) := by
    have : (fun v : EuclideanSpace ℝ (Fin d) =>
              Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)) =
            (fun v : EuclideanSpace ℝ (Fin d) =>
              Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + (0 : ℂ) * inner ℝ (0 : EuclideanSpace ℝ (Fin d)) v)) := by
      funext v
      simp
    rw [this]
    exact hint
  -- Use that the real exp is the real part / coerces from complex.
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin d),
      ‖Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)‖ = Real.exp (-b * ‖v‖ ^ 2) := by
    intro v
    rw [Complex.norm_exp]
    have : (-(b : ℂ) * (‖v‖ : ℂ) ^ 2).re = -b * ‖v‖ ^ 2 := by
      have h := Complex.ofReal_mul (-b) (‖v‖ ^ 2)
      have h2 : -(b : ℂ) * (‖v‖ : ℂ) ^ 2 = ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [h2, Complex.ofReal_re]
    rw [this]
  -- Integrability of complex implies integrability of norm.
  have hni := hint'.norm
  refine (hni.congr ?_)
  exact Filter.Eventually.of_forall (fun v => hnorm v)

/-- Pointwise Markov bound on the tail set: if `‖v‖² > d/t`, then
    `e^{-2t‖v‖²} ≤ e^{-d} e^{-t‖v‖²}`. -/
private lemma tail_pointwise {d : ℕ} {t : ℝ} (ht : 0 < t)
    {v : EuclideanSpace ℝ (Fin d)} (hv : (d : ℝ) / t < ‖v‖ ^ 2) :
    Real.exp (-(2 * t) * ‖v‖ ^ 2) ≤ Real.exp (-(d : ℝ)) * Real.exp (-t * ‖v‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- Want: -2t‖v‖² ≤ -d - t‖v‖², i.e., -t‖v‖² ≤ -d, i.e., t‖v‖² ≥ d.
  have hge : (d : ℝ) ≤ t * ‖v‖ ^ 2 := by
    have := (div_lt_iff₀ ht).mp hv
    linarith
  nlinarith [hge]

/-- Core Gaussian mass lower bound. -/
theorem inner_core_gaussian_mass :
    ∃ c_star : ℝ, 0 < c_star ∧
      ∀ d : ℕ, 1 ≤ d → ∀ t : ℝ, 1 ≤ t →
        (1 - Real.exp (-(c_star * d))) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) ≤
        ∫ v in {v : EuclideanSpace ℝ (Fin d) | ‖v‖ ^ 2 ≤ (d : ℝ) / t},
          Real.exp (-(2 * t) * ‖v‖ ^ 2) := by
  -- Take c_* = 1 - (1/2) ln 2 > 0.
  refine ⟨1 - (1 / 2) * Real.log 2, ?_, ?_⟩
  · -- 0 < 1 - (1/2) ln 2.  Use log_two_lt_d9: log 2 < 0.6931471808 < 2.
    have hlog2 : Real.log 2 < 2 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  intro d hd t ht
  -- Setup.
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h2t_pos : (0 : ℝ) < 2 * t := by linarith
  have hd_pos : 0 < d := hd
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hd_real_nn : (0 : ℝ) ≤ (d : ℝ) := hd_real_pos.le
  -- Abbreviations.
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun v => Real.exp (-(2 * t) * ‖v‖ ^ 2) with hf_def
  set S : Set (EuclideanSpace ℝ (Fin d)) := {v | ‖v‖ ^ 2 ≤ (d : ℝ) / t} with hS_def
  set Sc : Set (EuclideanSpace ℝ (Fin d)) := {v | (d : ℝ) / t < ‖v‖ ^ 2} with hSc_def
  -- f is integrable.
  have hf_int : Integrable f := integrable_rexp_neg_mul_sq_norm_euclidean h2t_pos
  have hf_nn : ∀ v, 0 ≤ f v := fun v => Real.exp_nonneg _
  -- Total integral of f.
  have h_total : ∫ v : EuclideanSpace ℝ (Fin d), f v = (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) :=
    integral_rexp_neg_mul_sq_norm_euclidean h2t_pos
  -- Splitting: ∫ f = ∫_S f + ∫_Sc f, and S, Sc are complementary.
  have hSc_compl : Sc = Sᶜ := by
    ext v
    simp only [hS_def, hSc_def, Set.mem_setOf_eq, Set.mem_compl_iff]
    exact ⟨fun h => not_le.mpr h, fun h => not_le.mp h⟩
  -- Measurability of S.
  have hS_meas : MeasurableSet S := by
    refine measurableSet_le ?_ measurable_const
    exact (continuous_norm.pow 2).measurable
  have hSc_meas : MeasurableSet Sc := by
    rw [hSc_compl]; exact hS_meas.compl
  -- Setup: ∫_S f = ∫ f - ∫_Sc f.
  have h_split : ∫ v in S, f v = (∫ v, f v) - ∫ v in Sc, f v := by
    have h1 := integral_add_compl hS_meas hf_int
    -- h1 : ∫ v in S, f v + ∫ v in Sᶜ, f v = ∫ v, f v
    have h2 : (∫ v in Sc, f v) = ∫ v in Sᶜ, f v := by rw [hSc_compl]
    linarith [h1, h2]
  -- Now bound the tail integral ∫_Sc f.
  -- Pointwise: on Sc, f v ≤ exp(-d) * exp(-t‖v‖²).
  set g : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun v => Real.exp (-(d : ℝ)) * Real.exp (-t * ‖v‖ ^ 2) with hg_def
  have hg_int : Integrable g := by
    show Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(d : ℝ)) * Real.exp (-t * ‖v‖ ^ 2))
    exact (integrable_rexp_neg_mul_sq_norm_euclidean ht_pos).const_mul _
  have hg_nn : ∀ v, 0 ≤ g v := fun v =>
    mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have h_tail_le : ∫ v in Sc, f v ≤ ∫ v in Sc, g v := by
    apply setIntegral_mono_on hf_int.integrableOn hg_int.integrableOn hSc_meas
    intro v hv
    exact tail_pointwise ht_pos hv
  -- ∫_Sc g ≤ ∫_univ g = exp(-d) * (π/t)^{d/2}.
  have h_g_total : ∫ v, g v = Real.exp (-(d : ℝ)) * (Real.pi / t) ^ ((d : ℝ) / 2) := by
    show ∫ v : EuclideanSpace ℝ (Fin d),
        Real.exp (-(d : ℝ)) * Real.exp (-t * ‖v‖ ^ 2) =
      Real.exp (-(d : ℝ)) * (Real.pi / t) ^ ((d : ℝ) / 2)
    rw [integral_const_mul]
    rw [integral_rexp_neg_mul_sq_norm_euclidean ht_pos]
  have h_setg_le : ∫ v in Sc, g v ≤ ∫ v, g v := by
    apply setIntegral_le_integral hg_int
    exact Filter.Eventually.of_forall hg_nn
  have h_tail_total : ∫ v in Sc, f v ≤
      Real.exp (-(d : ℝ)) * (Real.pi / t) ^ ((d : ℝ) / 2) := by
    calc ∫ v in Sc, f v
        ≤ ∫ v in Sc, g v := h_tail_le
      _ ≤ ∫ v, g v := h_setg_le
      _ = Real.exp (-(d : ℝ)) * (Real.pi / t) ^ ((d : ℝ) / 2) := h_g_total
  -- Now: (π/t)^{d/2} = 2^{d/2} * (π/(2t))^{d/2}.
  have hpi2t_pos : (0 : ℝ) < Real.pi / (2 * t) := div_pos Real.pi_pos h2t_pos
  have hpit_pos : (0 : ℝ) < Real.pi / t := div_pos Real.pi_pos ht_pos
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_factor : (Real.pi / t) ^ ((d : ℝ) / 2) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by
    have h1 : Real.pi / t = 2 * (Real.pi / (2 * t)) := by
      field_simp
    rw [h1]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hpi2t_pos.le]
  -- So tail ≤ exp(-d) * 2^{d/2} * (π/(2t))^{d/2}.
  -- We claim: exp(-d) * 2^{d/2} ≤ exp(-c_* * d), where c_* = 1 - (1/2) ln 2.
  set c_star : ℝ := 1 - (1 / 2) * Real.log 2 with hc_def
  have h_exp_factor : Real.exp (-(d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) / 2) =
      Real.exp (-(c_star * d)) := by
    -- 2^{d/2} = exp((d/2) * log 2).
    have h2 : (2 : ℝ) ^ ((d : ℝ) / 2) = Real.exp (((d : ℝ) / 2) * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      ring_nf
    rw [h2, ← Real.exp_add]
    congr 1
    rw [hc_def]
    ring
  -- Combine: tail ≤ exp(-c_* d) * (π/(2t))^{d/2}.
  have h_tail_final : ∫ v in Sc, f v ≤
      Real.exp (-(c_star * d)) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by
    calc ∫ v in Sc, f v
        ≤ Real.exp (-(d : ℝ)) * (Real.pi / t) ^ ((d : ℝ) / 2) := h_tail_total
      _ = Real.exp (-(d : ℝ)) *
            ((2 : ℝ) ^ ((d : ℝ) / 2) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2)) := by
              rw [h_factor]
      _ = (Real.exp (-(d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) / 2)) *
            (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by ring
      _ = Real.exp (-(c_star * d)) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by
              rw [h_exp_factor]
  -- Final assembly:
  -- ∫_S f = ∫ f - ∫_Sc f ≥ (π/(2t))^{d/2} - exp(-c_* d)*(π/(2t))^{d/2}
  --                     = (1 - exp(-c_* d)) * (π/(2t))^{d/2}.
  have hRHS : (1 - Real.exp (-(c_star * d))) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) =
      (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) -
        Real.exp (-(c_star * d)) * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by
    ring
  rw [hRHS, h_split, h_total]
  linarith [h_tail_final]

end LeaHadamard.Hadamard
