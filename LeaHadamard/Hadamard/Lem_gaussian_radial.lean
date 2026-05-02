import Mathlib

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace LeaHadamard.Hadamard

/-! ## Auxiliary lemmas -/

/-- Pointwise bound: `u^m * exp(-u) ≤ m!` for nonnegative `u`. -/
private lemma pow_mul_exp_neg_le_factorial (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ m * Real.exp (-u) ≤ (m.factorial : ℝ) := by
  have h1 : u ^ m / m.factorial ≤ Real.exp u := Real.pow_div_factorial_le_exp u hu m
  have h2 : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h3 : u ^ m ≤ (m.factorial : ℝ) * Real.exp u := by
    rw [div_le_iff₀ h2] at h1; linarith
  calc u ^ m * Real.exp (-u)
      ≤ ((m.factorial : ℝ) * Real.exp u) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = (m.factorial : ℝ) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Pointwise bound: For `t > 0` and any `x : ℝ` and `m : ℕ`,
`x^{2m} * exp(-2t x²) ≤ (m!/t^m) * exp(-t x²)`. -/
private lemma pow_mul_exp_neg_two_t_sq_le (m : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    x ^ (2 * m) * Real.exp (-(2 * t) * x ^ 2) ≤
      (m.factorial : ℝ) / t ^ m * Real.exp (-t * x ^ 2) := by
  have hxsq : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have htxsq : (0 : ℝ) ≤ t * x ^ 2 := mul_nonneg ht.le hxsq
  have htm : (0 : ℝ) < t ^ m := pow_pos ht m
  have hub := pow_mul_exp_neg_le_factorial m htxsq
  have hxpw : x ^ (2 * m) = (x ^ 2) ^ m := by rw [pow_mul]
  have hexpand : (t * x ^ 2) ^ m * Real.exp (-(t * x ^ 2)) =
      t ^ m * x ^ (2 * m) * Real.exp (-(t * x ^ 2)) := by
    rw [hxpw, mul_pow]
  rw [hexpand] at hub
  -- t^m * x^{2m} * e^{-tx²} ≤ m!.
  have hstep : x ^ (2 * m) * Real.exp (-(t * x ^ 2)) ≤ (m.factorial : ℝ) / t ^ m := by
    rw [le_div_iff₀ htm]
    nlinarith [hub, Real.exp_nonneg (-(t * x ^ 2))]
  -- Multiply by e^{-t x²} ≥ 0:
  have key :
    x ^ (2 * m) * Real.exp (-(t * x ^ 2)) * Real.exp (-(t * x ^ 2)) ≤
      (m.factorial : ℝ) / t ^ m * Real.exp (-(t * x ^ 2)) :=
    mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
  have h2tx : -(2 * t) * x ^ 2 = -(t * x ^ 2) + -(t * x ^ 2) := by ring
  have hexp_split : Real.exp (-(2 * t) * x ^ 2) =
      Real.exp (-(t * x ^ 2)) * Real.exp (-(t * x ^ 2)) := by
    rw [h2tx, Real.exp_add]
  have hntx : Real.exp (-t * x ^ 2) = Real.exp (-(t * x ^ 2)) := by
    congr 1; ring
  rw [hexp_split, ← mul_assoc, hntx]
  exact key

/-- Integrability of `x^{2m} * exp(-b * x^2)` for `b > 0`. -/
private lemma integrable_pow_mul_exp_neg_mul_sq (m : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ (2 * m) * Real.exp (-b * x ^ 2)) := by
  have hs_pos : (-1 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq hb
    (s := ((2 * m : ℕ) : ℝ)) hs_pos
  have heq : (fun x : ℝ => x ^ (((2 * m : ℕ) : ℝ)) * Real.exp (-b * x ^ 2)) =
      (fun x : ℝ => x ^ (2 * m) * Real.exp (-b * x ^ 2)) := by
    funext x
    rw [Real.rpow_natCast]
  rw [heq] at h
  exact h

/-- 1D moment bound: for `m : ℕ` and `t > 0`,
`∫ x^{2m} e^{-2t x²} dx ≤ (m!/t^m) * √(π/t)`. -/
private lemma integral_pow_mul_exp_neg_mul_sq_le (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * m) * Real.exp (-(2 * t) * x ^ 2) ≤
      (m.factorial : ℝ) / t ^ m * Real.sqrt (Real.pi / t) := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  -- Pointwise bound integrated
  have hint_lhs := integrable_pow_mul_exp_neg_mul_sq m h2t
  have hint_rhs : Integrable (fun x : ℝ =>
      (m.factorial : ℝ) / t ^ m * Real.exp (-t * x ^ 2)) :=
    (integrable_exp_neg_mul_sq ht).const_mul _
  have hmono : ∫ x : ℝ, x ^ (2 * m) * Real.exp (-(2 * t) * x ^ 2) ≤
      ∫ x : ℝ, (m.factorial : ℝ) / t ^ m * Real.exp (-t * x ^ 2) := by
    apply integral_mono hint_lhs hint_rhs
    intro x
    exact pow_mul_exp_neg_two_t_sq_le m ht x
  -- Now compute the RHS integral.
  have hint_eval : ∫ x : ℝ, (m.factorial : ℝ) / t ^ m * Real.exp (-t * x ^ 2) =
      (m.factorial : ℝ) / t ^ m * Real.sqrt (Real.pi / t) := by
    rw [integral_const_mul]
    congr 1
    exact integral_gaussian t
  linarith [hmono, hint_eval ▸ le_refl
    ((m.factorial : ℝ) / t ^ m * Real.sqrt (Real.pi / t))]

theorem gaussian_radial_moments :
    ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ t : ℝ, 1 ≤ t →
        ∫ x : EuclideanSpace ℝ (Fin d), ‖x‖^(2*m) * Real.exp (-(2*t) * ‖x‖^2) ≤
          C * ((d : ℝ)/t)^m * (Real.pi/(2*t))^((d : ℝ)/2) := by
  intro m
  refine ⟨Real.sqrt 2 * (m.factorial : ℝ), ?_, ?_⟩
  · -- 0 < √2 * m!
    have h1 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
    exact mul_pos h1 h2
  intro d hd t ht
  -- Setup: t > 0, d ≥ 1.
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h2t_pos : (0 : ℝ) < 2 * t := by linarith
  have hd_pos : 0 < d := hd
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  -- Key shorthands.
  set J : ℝ := Real.sqrt (Real.pi / (2 * t)) with hJ_def
  have hJ_nn : 0 ≤ J := Real.sqrt_nonneg _
  have hJ_sq : J ^ 2 = Real.pi / (2 * t) := by
    rw [hJ_def]; rw [sq_sqrt]
    have : 0 < Real.pi / (2 * t) := div_pos Real.pi_pos h2t_pos
    linarith
  -- Pull integral from EuclideanSpace to Fin d → ℝ.
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  -- Convert ‖toLp 2 x‖² to ∑ i, (x i)².
  have hnorm_sq : ∀ x : Fin d → ℝ,
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    show ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) i‖ ^ 2 = (x i) ^ 2
    rw [show (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) i = x i from rfl]
    rw [Real.norm_eq_abs, sq_abs]
  -- Rewrite ‖·‖^(2m) = (‖·‖²)^m.
  have hnorm_pow : ∀ x : Fin d → ℝ,
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ (2 * m) =
        (∑ i : Fin d, (x i) ^ 2) ^ m := by
    intro x; rw [pow_mul, hnorm_sq]
  -- Replace integrand using simp_rw.
  conv_lhs => rw [show (fun x : Fin d → ℝ =>
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ (2 * m) *
          Real.exp (-(2 * t) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2)) =
        (fun x : Fin d → ℝ =>
          (∑ i : Fin d, (x i) ^ 2) ^ m *
            Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)) from
      funext fun x => by rw [hnorm_sq, hnorm_pow]]
  -- Power mean inequality: d * (∑ x_i²)^m ≤ d^m * ∑ x_i^{2m}.
  have hpm : ∀ x : Fin d → ℝ,
      (d : ℝ) * (∑ i : Fin d, (x i) ^ 2) ^ m ≤
        (d : ℝ) ^ m * ∑ i : Fin d, (x i) ^ (2 * m) := by
    intro x
    -- Apply Real.pow_arith_mean_le_arith_mean_pow with weights w_i = 1/d.
    have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin d)), (0 : ℝ) ≤ ((d : ℝ))⁻¹ := by
      intro i _; positivity
    have hw_sum : ∑ _i ∈ (Finset.univ : Finset (Fin d)), ((d : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (d : ℝ) ≠ 0 := ne_of_gt hd_real_pos
      field_simp
    have hz_nn : ∀ i ∈ (Finset.univ : Finset (Fin d)), (0 : ℝ) ≤ (x i) ^ 2 := by
      intro i _; exact sq_nonneg _
    have key := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin d))
      (fun _ => ((d : ℝ))⁻¹) (fun i => (x i) ^ 2) hw_nn hw_sum hz_nn m
    -- key: (∑ i, d⁻¹ * (x i)²)^m ≤ ∑ i, d⁻¹ * ((x i)²)^m.
    have lhs_eq : (∑ i ∈ (Finset.univ : Finset (Fin d)),
        ((d : ℝ))⁻¹ * (x i) ^ 2) = ((d : ℝ))⁻¹ * ∑ i, (x i) ^ 2 := by
      rw [← Finset.mul_sum]
    have rhs_eq : (∑ i ∈ (Finset.univ : Finset (Fin d)),
        ((d : ℝ))⁻¹ * ((x i) ^ 2) ^ m) = ((d : ℝ))⁻¹ * ∑ i, (x i) ^ (2 * m) := by
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_mul]
    rw [lhs_eq, rhs_eq, mul_pow] at key
    -- key: d⁻¹^m * (∑ x_i²)^m ≤ d⁻¹ * (∑ x_i^{2m}).
    -- Multiply both sides by d * d^m.
    have hdm_pos : (0 : ℝ) < (d : ℝ) ^ m := pow_pos hd_real_pos m
    have hd_pos' : (0 : ℝ) < (d : ℝ) := hd_real_pos
    have hcoeff_pos : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) ^ m :=
      (mul_pos hd_pos' hdm_pos).le
    have key2 := mul_le_mul_of_nonneg_left key hcoeff_pos
    -- key2: (d * d^m) * (d⁻¹^m * (∑x²)^m) ≤ (d * d^m) * (d⁻¹ * ∑x^{2m})
    have hne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos'
    have hdpow_inv_pow : ((d : ℝ) ^ m) * (((d : ℝ))⁻¹ ^ m) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hne, one_pow]
    have h_left : ((d : ℝ) * (d : ℝ) ^ m) * (((d : ℝ))⁻¹ ^ m * (∑ i, (x i) ^ 2) ^ m) =
        (d : ℝ) * (∑ i, (x i) ^ 2) ^ m := by
      calc ((d : ℝ) * (d : ℝ) ^ m) * (((d : ℝ))⁻¹ ^ m * (∑ i, (x i) ^ 2) ^ m)
          = (d : ℝ) * ((d : ℝ) ^ m * ((d : ℝ))⁻¹ ^ m) * (∑ i, (x i) ^ 2) ^ m := by ring
        _ = (d : ℝ) * 1 * (∑ i, (x i) ^ 2) ^ m := by rw [hdpow_inv_pow]
        _ = (d : ℝ) * (∑ i, (x i) ^ 2) ^ m := by ring
    have h_right : ((d : ℝ) * (d : ℝ) ^ m) * (((d : ℝ))⁻¹ * ∑ i, (x i) ^ (2 * m)) =
        (d : ℝ) ^ m * ∑ i, (x i) ^ (2 * m) := by
      calc ((d : ℝ) * (d : ℝ) ^ m) * (((d : ℝ))⁻¹ * ∑ i, (x i) ^ (2 * m))
          = ((d : ℝ) * ((d : ℝ))⁻¹) * (d : ℝ) ^ m * ∑ i, (x i) ^ (2 * m) := by ring
        _ = 1 * (d : ℝ) ^ m * ∑ i, (x i) ^ (2 * m) := by
              rw [mul_inv_cancel₀ hne]
        _ = (d : ℝ) ^ m * ∑ i, (x i) ^ (2 * m) := by ring
    linarith [key2, h_left.symm.le, h_left.le, h_right.symm.le, h_right.le]
  -- Pointwise bound combining power-mean with Gaussian factor.
  -- d * S(x)^m * exp(-2t S(x)) ≤ d^m * ∑_i (x i)^{2m} * ∏_j exp(-2t (x j)^2).
  have hexp_factor : ∀ x : Fin d → ℝ,
      Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) =
        ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum]
  -- Pointwise: d * S^m * exp(-2tS) ≤ d^m * ∑_i [(x i)^{2m} * ∏_j exp(-2t (x j)²)]
  have hpw_full : ∀ x : Fin d → ℝ,
      (d : ℝ) * ((∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)) ≤
        (d : ℝ) ^ m * ∑ i : Fin d,
          ((x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) := by
    intro x
    have hexp_pos : 0 < Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) := Real.exp_pos _
    have hexp_nn : 0 ≤ Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) := hexp_pos.le
    have h_pm := hpm x
    -- Multiply hpm by exp(-2tS) ≥ 0:
    have step1 :
      (d : ℝ) * (∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) ≤
        (d : ℝ) ^ m * (∑ i : Fin d, (x i) ^ (2 * m)) *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) :=
      mul_le_mul_of_nonneg_right h_pm hexp_nn
    have step2 :
      ((d : ℝ) ^ m * (∑ i : Fin d, (x i) ^ (2 * m))) *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) =
        (d : ℝ) ^ m * ∑ i : Fin d,
          ((x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) := by
      rw [hexp_factor x]
      rw [mul_assoc, Finset.sum_mul]
    linarith [step1, step2.symm.le, step2.le]
  -- Define I_m and J:
  set Im : ℝ := ∫ x : ℝ, x ^ (2 * m) * Real.exp (-(2 * t) * x ^ 2) with hIm_def
  -- For each i, Fubini gives ∫_{Fin d → ℝ} x_i^{2m} ∏_j exp(-2t x_j²) dx = Im * J^(d-1).
  have hfubini_each : ∀ i : Fin d,
      ∫ x : Fin d → ℝ, (x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2) =
        Im * J ^ (d - 1) := by
    intro i
    classical
    -- Define f j = if j = i then y^{2m}*exp(-2t y²) else exp(-2t y²).
    let f : Fin d → ℝ → ℝ := fun j y =>
      if j = i then y ^ (2 * m) * Real.exp (-(2 * t) * y ^ 2)
      else Real.exp (-(2 * t) * y ^ 2)
    -- Rewrite the integrand as ∏_j f j (x j).
    have hprod_eq : ∀ x : Fin d → ℝ,
        (x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2) =
          ∏ j : Fin d, f j (x j) := by
      intro x
      have hsplit : ∏ j : Fin d, f j (x j) =
          f i (x i) * ∏ j ∈ (Finset.univ.erase i), f j (x j) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsplit]
      have hfi : f i (x i) = (x i) ^ (2 * m) * Real.exp (-(2 * t) * (x i) ^ 2) := by
        simp [f]
      have hfj : ∀ j ∈ Finset.univ.erase i,
          f j (x j) = Real.exp (-(2 * t) * (x j) ^ 2) := by
        intro j hj
        simp only [Finset.mem_erase] at hj
        simp [f, hj.1]
      rw [hfi]
      rw [Finset.prod_congr rfl hfj]
      have hsplit2 : (∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) =
          Real.exp (-(2 * t) * (x i) ^ 2) *
          ∏ j ∈ Finset.univ.erase i, Real.exp (-(2 * t) * (x j) ^ 2) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsplit2]
      ring
    -- Apply integral_fintype_prod_volume_eq_prod
    have hkey :
        ∫ x : Fin d → ℝ, ∏ j : Fin d, f j (x j) = ∏ j : Fin d, ∫ y : ℝ, f j y := by
      exact integral_fintype_prod_volume_eq_prod f
    -- Compute ∫ y : ℝ, f j y for each j.
    have hint_at_i : ∫ y : ℝ, f i y = Im := by
      simp [f, Im]
    have hint_other : ∀ j : Fin d, j ≠ i →
        ∫ y : ℝ, f j y = J := by
      intro j hji
      have : f j = fun y => Real.exp (-(2 * t) * y ^ 2) := by
        funext y; simp [f, hji]
      rw [this]
      have hgauss : ∫ y : ℝ, Real.exp (-(2 * t) * y ^ 2) = Real.sqrt (Real.pi / (2 * t)) :=
        integral_gaussian (2 * t)
      rw [hgauss, hJ_def]
    -- Compute the product.
    have hprod_compute : (∏ j : Fin d, ∫ y : ℝ, f j y) = Im * J ^ (d - 1) := by
      have hsplit_prod : (∏ j : Fin d, ∫ y : ℝ, f j y) =
          (∫ y : ℝ, f i y) * ∏ j ∈ Finset.univ.erase i, ∫ y : ℝ, f j y := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsplit_prod, hint_at_i]
      have hprod_const : ∏ j ∈ (Finset.univ.erase i : Finset (Fin d)), ∫ y : ℝ, f j y =
          J ^ (d - 1) := by
        have hcong : ∀ j ∈ Finset.univ.erase i, (∫ y : ℝ, f j y) = J := by
          intro j hj
          have : j ≠ i := (Finset.mem_erase.mp hj).1
          exact hint_other j this
        rw [Finset.prod_congr rfl hcong]
        rw [Finset.prod_const]
        congr
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp [Finset.card_univ, Fintype.card_fin]
      rw [hprod_const]
    -- Combine: integral of LHS = integral of ∏ f j = ∏ ∫ f j = Im * J^(d-1).
    rw [show
        (fun x : Fin d → ℝ => (x i) ^ (2 * m) *
          ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2))
        = (fun x : Fin d → ℝ => ∏ j : Fin d, f j (x j)) from funext hprod_eq]
    rw [hkey, hprod_compute]
  -- Bound on Im (1D moment): Im ≤ m! / t^m * √(π/t) = m! * √2 / t^m * J.
  have hIm_bound : Im ≤ (m.factorial : ℝ) * Real.sqrt 2 / t ^ m * J := by
    have hraw := integral_pow_mul_exp_neg_mul_sq_le m ht_pos
    -- hraw: Im ≤ (m!/t^m) * √(π/t)
    -- Note √(π/t) = √2 * J.
    have hsqrt_eq : Real.sqrt (Real.pi / t) = Real.sqrt 2 * J := by
      rw [hJ_def]
      have hp_t : 0 < Real.pi / t := div_pos Real.pi_pos ht_pos
      have hp_2t : 0 < Real.pi / (2 * t) := div_pos Real.pi_pos h2t_pos
      have hh : Real.pi / t = 2 * (Real.pi / (2 * t)) := by
        field_simp
      rw [hh]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    calc Im ≤ (m.factorial : ℝ) / t ^ m * Real.sqrt (Real.pi / t) := hraw
      _ = (m.factorial : ℝ) / t ^ m * (Real.sqrt 2 * J) := by rw [hsqrt_eq]
      _ = (m.factorial : ℝ) * Real.sqrt 2 / t ^ m * J := by ring
  -- Combine everything to bound the integral.
  -- First, the integrand is integrable.  We don't need to fully formalize this for the bound;
  -- we use integral_mono with proper integrability.
  -- The integrand: g(x) := (∑ x_i²)^m * exp(-2t ∑ x_i²) on Fin d → ℝ.
  -- Bound by h(x) := d^{m-1} * ∑_i [(x i)^{2m} * ∏_j exp(-2t (x j)²)] / d ... wait better
  -- pointwise:  g ≤ d^{m-1} * ∑_i (x i)^{2m} ∏_j exp(-2t (x j)^2) when m ≥ 1, else equal.
  -- Easier: use d * g(x) ≤ d^m * (∑_i ...).
  -- We'll show: ∫ d * g ≤ ∫ d^m * (...), and then divide by d.
  -- Integrability:
  -- 1) Each (x i)^{2m} * ∏_j exp(-2t (x j)²) is integrable (Fubini).
  -- 2) The full integrand g is bounded by exp(-2t ∑ x_j²) up to const, integrable.
  -- We'll combine carefully.
  -- The product ∏_j exp(-2t x_j²) integrated equals J^d.
  have hprod_gauss_int :
      ∫ x : Fin d → ℝ, ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2) = J ^ d := by
    have := integral_fintype_prod_volume_eq_pow (ι := Fin d) (E := ℝ)
      (fun y : ℝ => Real.exp (-(2 * t) * y ^ 2))
    rw [this]
    rw [integral_gaussian (2 * t)]
    rw [hJ_def]
    simp [Fintype.card_fin]
  -- Integrability of the product Gaussian:
  have hint_prod_gauss : Integrable (fun x : Fin d → ℝ =>
      ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) := by
    exact MeasureTheory.Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq h2t_pos)
  -- Integrability of (x i)^{2m} * ∏_j exp:
  -- The product equals (factor_i (x i)) * (∏ j ≠ i, exp(-2t (x j)²)) where factor_i(y) = y^{2m} * exp(-2t y²).
  -- This is integrable by .fintype_prod with f i replaced.
  have hint_xi_prod : ∀ i : Fin d, Integrable (fun x : Fin d → ℝ =>
      (x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) := by
    intro i
    classical
    let f : Fin d → ℝ → ℝ := fun j y =>
      if j = i then y ^ (2 * m) * Real.exp (-(2 * t) * y ^ 2)
      else Real.exp (-(2 * t) * y ^ 2)
    have hf_int : ∀ j, Integrable (f j) := by
      intro j
      by_cases hj : j = i
      · subst hj
        have : f j = fun y => y ^ (2 * m) * Real.exp (-(2 * t) * y ^ 2) := by
          funext y; simp [f]
        rw [this]
        exact integrable_pow_mul_exp_neg_mul_sq m h2t_pos
      · have : f j = fun y => Real.exp (-(2 * t) * y ^ 2) := by
          funext y; simp [f, hj]
        rw [this]
        exact integrable_exp_neg_mul_sq h2t_pos
    have hp := MeasureTheory.Integrable.fintype_prod (μ := fun _ => (volume : Measure ℝ)) hf_int
    -- hp : Integrable (fun x => ∏ j, f j (x j)).
    -- We need: Integrable (fun x => (x i)^{2m} * ∏_j exp(-2t (x j)²)).
    have heq : (fun x : Fin d → ℝ => (x i) ^ (2 * m) *
        ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) =
        (fun x : Fin d → ℝ => ∏ j : Fin d, f j (x j)) := by
      funext x
      have hsplit : ∏ j : Fin d, f j (x j) =
          f i (x i) * ∏ j ∈ (Finset.univ.erase i), f j (x j) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsplit]
      have hfi : f i (x i) = (x i) ^ (2 * m) * Real.exp (-(2 * t) * (x i) ^ 2) := by
        simp [f]
      have hfj : ∀ j ∈ Finset.univ.erase i,
          f j (x j) = Real.exp (-(2 * t) * (x j) ^ 2) := by
        intro j hj
        simp only [Finset.mem_erase] at hj
        simp [f, hj.1]
      rw [hfi]
      rw [Finset.prod_congr rfl hfj]
      have hsplit2 : (∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) =
          Real.exp (-(2 * t) * (x i) ^ 2) *
          ∏ j ∈ Finset.univ.erase i, Real.exp (-(2 * t) * (x j) ^ 2) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsplit2]
      ring
    rw [heq]
    exact hp
  -- Now integrate hpw_full to get:
  -- d * ∫ g ≤ d^m * ∑_i ∫ [(x i)^{2m} * ∏ j exp(...)] = d^m * d * Im * J^(d-1) = d^{m+1} * Im * J^{d-1}.
  -- So ∫ g ≤ d^m * Im * J^{d-1}.
  -- Integrability of g (the LHS integrand of the original goal after substitution):
  have hint_g_bound : ∀ x : Fin d → ℝ, 0 ≤ (∑ i : Fin d, (x i) ^ 2) ^ m *
      Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) := by
    intro x
    apply mul_nonneg
    · exact pow_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) m
    · exact (Real.exp_pos _).le
  have hsum_eq_d_Im_Jd1 :
      ∫ x : Fin d → ℝ, ∑ i : Fin d,
          ((x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) =
        (d : ℝ) * (Im * J ^ (d - 1)) := by
    rw [integral_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => hint_xi_prod i)]
    rw [Finset.sum_congr rfl (fun i _ => hfubini_each i)]
    rw [Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin]
  -- Integrability of the RHS pointwise function in hpw_full:
  have hint_rhs : Integrable (fun x : Fin d → ℝ =>
      (d : ℝ) ^ m * ∑ i : Fin d,
        ((x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2))) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ (fun i _ => hint_xi_prod i)
  -- Integrability of g (the LHS): bound by const * RHS Gaussian.
  -- g(x) = (∑x²)^m * exp(-2tS).  Use hpm + bound or direct bound by hpw_full.
  -- Actually, since 0 ≤ g(x) and d*g(x) ≤ d^m * h(x), so g(x) ≤ d^{m-1} * h(x).
  -- For integrability: we use the same bound.  Let's bound differently:
  -- Use the simpler bound g(x) ≤ (m!/t^m)^? · exp(-tS) ... actually let me just use comparison.
  -- (∑x²)^m * exp(-2tS) ≤ c * exp(-tS) where c = (m!/t^m) (since (tS)^m exp(-tS) ≤ m!).
  have hg_simple_bound : ∀ x : Fin d → ℝ,
      (∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) ≤
        (m.factorial : ℝ) / t ^ m *
          Real.exp (-t * ∑ i : Fin d, (x i) ^ 2) := by
    intro x
    set S : ℝ := ∑ i : Fin d, (x i) ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have htm : (0 : ℝ) < t ^ m := pow_pos ht_pos m
    have htSm : 0 ≤ (t * S) ^ m := pow_nonneg (mul_nonneg ht_pos.le hS_nn) m
    -- (tS)^m exp(-tS) ≤ m!:
    have hbound := pow_mul_exp_neg_le_factorial m (mul_nonneg ht_pos.le hS_nn)
    -- (tS)^m exp(-tS) = t^m * S^m * exp(-tS)
    have hexpand : (t * S) ^ m * Real.exp (-(t * S)) = t ^ m * S ^ m * Real.exp (-(t * S)) := by
      rw [mul_pow]
    rw [hexpand] at hbound
    -- t^m * S^m * exp(-tS) ≤ m!.
    -- So S^m * exp(-tS) ≤ m! / t^m.
    have hS_exp : S ^ m * Real.exp (-(t * S)) ≤ (m.factorial : ℝ) / t ^ m := by
      rw [le_div_iff₀ htm]
      nlinarith [hbound, Real.exp_nonneg (-(t * S))]
    -- Multiply both sides by exp(-(t S)) ≥ 0:
    have step :
        S ^ m * Real.exp (-(t * S)) * Real.exp (-(t * S)) ≤
          (m.factorial : ℝ) / t ^ m * Real.exp (-(t * S)) :=
      mul_le_mul_of_nonneg_right hS_exp (Real.exp_nonneg _)
    have hexpsplit : Real.exp (-(2 * t) * S) =
        Real.exp (-(t * S)) * Real.exp (-(t * S)) := by
      rw [← Real.exp_add]; congr 1; ring
    have htneg : Real.exp (-t * S) = Real.exp (-(t * S)) := by congr 1; ring
    rw [hexpsplit, htneg]
    calc S ^ m * (Real.exp (-(t * S)) * Real.exp (-(t * S)))
        = S ^ m * Real.exp (-(t * S)) * Real.exp (-(t * S)) := by ring
      _ ≤ (m.factorial : ℝ) / t ^ m * Real.exp (-(t * S)) := step
  -- Integrability of (m!/t^m) * exp(-t * ∑ x_j²):
  have hint_simple : Integrable (fun x : Fin d → ℝ =>
      (m.factorial : ℝ) / t ^ m *
        Real.exp (-t * ∑ i : Fin d, (x i) ^ 2)) := by
    refine Integrable.const_mul ?_ _
    -- exp(-t ∑ x_j²) = ∏_j exp(-t x_j²)
    have heq : (fun x : Fin d → ℝ => Real.exp (-t * ∑ i : Fin d, (x i) ^ 2)) =
        (fun x : Fin d → ℝ => ∏ j : Fin d, Real.exp (-t * (x j) ^ 2)) := by
      funext x
      rw [Finset.mul_sum, Real.exp_sum]
    rw [heq]
    exact MeasureTheory.Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq ht_pos)
  -- Integrability of g = (∑ x²)^m * exp(-2t ∑ x²):
  have hint_g : Integrable (fun x : Fin d → ℝ =>
      (∑ i : Fin d, (x i) ^ 2) ^ m *
        Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)) := by
    -- Comparison via hg_simple_bound.
    refine Integrable.mono' hint_simple ?_ ?_
    · -- AEStronglyMeasurable
      apply Continuous.aestronglyMeasurable
      have hcsum : Continuous (fun x : Fin d → ℝ => ∑ i : Fin d, (x i) ^ 2) := by
        exact continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)
      exact (hcsum.pow m).mul (Real.continuous_exp.comp (by fun_prop))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hg_nn := hint_g_bound x
      rw [Real.norm_eq_abs, abs_of_nonneg hg_nn]
      exact hg_simple_bound x
  -- Now integrate hpw_full:
  have hint_lhs_with_d : Integrable (fun x : Fin d → ℝ =>
      (d : ℝ) * ((∑ i : Fin d, (x i) ^ 2) ^ m *
        Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2))) :=
    hint_g.const_mul _
  have hmono_int :
      ∫ x : Fin d → ℝ, (d : ℝ) * ((∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)) ≤
        ∫ x : Fin d → ℝ, (d : ℝ) ^ m * ∑ i : Fin d,
          ((x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) := by
    apply integral_mono hint_lhs_with_d hint_rhs
    exact hpw_full
  -- Simplify both integrals.
  have hlhs_eq :
      ∫ x : Fin d → ℝ, (d : ℝ) * ((∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)) =
        (d : ℝ) * ∫ x : Fin d → ℝ, (∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) := by
    rw [integral_const_mul]
  have hrhs_eq :
      ∫ x : Fin d → ℝ, (d : ℝ) ^ m * ∑ i : Fin d,
          ((x i) ^ (2 * m) * ∏ j : Fin d, Real.exp (-(2 * t) * (x j) ^ 2)) =
        (d : ℝ) ^ m * ((d : ℝ) * (Im * J ^ (d - 1))) := by
    rw [integral_const_mul, hsum_eq_d_Im_Jd1]
  rw [hlhs_eq, hrhs_eq] at hmono_int
  -- Divide by d > 0:
  have h_g_int_le : ∫ x : Fin d → ℝ, (∑ i : Fin d, (x i) ^ 2) ^ m *
        Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) ≤
      (d : ℝ) ^ m * (Im * J ^ (d - 1)) := by
    have := hmono_int
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_real_pos
    have hkey : (d : ℝ) * ∫ x : Fin d → ℝ, (∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2) ≤
        (d : ℝ) * ((d : ℝ) ^ m * (Im * J ^ (d - 1))) := by
      calc (d : ℝ) * ∫ x : Fin d → ℝ, (∑ i : Fin d, (x i) ^ 2) ^ m *
              Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)
          ≤ (d : ℝ) ^ m * ((d : ℝ) * (Im * J ^ (d - 1))) := this
        _ = (d : ℝ) * ((d : ℝ) ^ m * (Im * J ^ (d - 1))) := by ring
    exact le_of_mul_le_mul_left hkey hd_real_pos
  -- Now apply the bound on Im:
  -- Im ≤ m! √2 / t^m * J.
  -- So d^m * (Im * J^(d-1)) ≤ d^m * (m! √2 / t^m) * J * J^(d-1) = m! √2 * (d/t)^m * J^d.
  have hIm_nn : 0 ≤ Im := by
    -- Im = ∫ x^{2m} * exp(-2t x²); integrand ≥ 0.
    apply integral_nonneg
    intro x
    exact mul_nonneg (even_two_mul m |>.pow_nonneg _) (Real.exp_pos _).le
  have hJd1_nn : 0 ≤ J ^ (d - 1) := pow_nonneg hJ_nn _
  have hIm_step :
      (d : ℝ) ^ m * (Im * J ^ (d - 1)) ≤
        (d : ℝ) ^ m * ((m.factorial : ℝ) * Real.sqrt 2 / t ^ m * J * J ^ (d - 1)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hd_real_pos.le m)
    apply mul_le_mul_of_nonneg_right hIm_bound hJd1_nn
  -- Combine J * J^(d-1) = J^d.
  have hJ_pow : J * J ^ (d - 1) = J ^ d := by
    have h : 1 + (d - 1) = d := by omega
    rw [show J * J ^ (d - 1) = J ^ 1 * J ^ (d - 1) from by rw [pow_one]]
    rw [← pow_add, h]
  have hStep_simplified :
      (d : ℝ) ^ m * ((m.factorial : ℝ) * Real.sqrt 2 / t ^ m * J * J ^ (d - 1)) =
        Real.sqrt 2 * (m.factorial : ℝ) * ((d : ℝ) / t) ^ m * J ^ d := by
    have htm_ne : (t : ℝ) ^ m ≠ 0 := ne_of_gt (pow_pos ht_pos m)
    have : (d : ℝ) ^ m / t ^ m = ((d : ℝ) / t) ^ m := by
      rw [div_pow]
    calc (d : ℝ) ^ m * ((m.factorial : ℝ) * Real.sqrt 2 / t ^ m * J * J ^ (d - 1))
        = (m.factorial : ℝ) * Real.sqrt 2 * ((d : ℝ) ^ m / t ^ m) * (J * J ^ (d - 1)) := by ring
      _ = (m.factorial : ℝ) * Real.sqrt 2 * ((d : ℝ) / t) ^ m * J ^ d := by
          rw [hJ_pow, this]
      _ = Real.sqrt 2 * (m.factorial : ℝ) * ((d : ℝ) / t) ^ m * J ^ d := by ring
  -- Convert J^d to (π/(2t))^(d/2):
  have hJd_eq : J ^ d = (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by
    have hpos : 0 ≤ Real.pi / (2 * t) := (div_pos Real.pi_pos h2t_pos).le
    rw [hJ_def]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast ((Real.pi / (2 * t)) ^ ((1 : ℝ) / 2)) d]
    rw [← Real.rpow_mul hpos]
    congr 1; ring
  -- Final assembly:
  calc ∫ x : Fin d → ℝ, (∑ i : Fin d, (x i) ^ 2) ^ m *
          Real.exp (-(2 * t) * ∑ i : Fin d, (x i) ^ 2)
      ≤ (d : ℝ) ^ m * (Im * J ^ (d - 1)) := h_g_int_le
    _ ≤ (d : ℝ) ^ m * ((m.factorial : ℝ) * Real.sqrt 2 / t ^ m * J * J ^ (d - 1)) := hIm_step
    _ = Real.sqrt 2 * (m.factorial : ℝ) * ((d : ℝ) / t) ^ m * J ^ d := hStep_simplified
    _ = Real.sqrt 2 * (m.factorial : ℝ) *
          ((d : ℝ) / t) ^ m * (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) := by rw [hJd_eq]

end LeaHadamard.Hadamard
