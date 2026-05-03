import Mathlib

open MeasureTheory Real Set Finset Complex
open scoped BigOperators

namespace LeaHadamard.Hadamard

/-! ## Positivity of `Re ψ`

We formalize the lemma:
> With `ψ` as in the cosine-product bound and `s(λ) := ∑_e λ_e²`, if
> `s(λ) ≤ 1/2`, then `Re ψ(λ) ∈ [3/4, 1]`.
-/

/-- The Rademacher sign attached to a Boolean: `false ↦ -1`, `true ↦ 1`. -/
@[simp] noncomputable def rad (b : Bool) : ℝ := if b then 1 else -1

lemma rad_sq (b : Bool) : rad b * rad b = 1 := by cases b <;> simp [rad]

lemma rad_not (b : Bool) : rad (!b) = - rad b := by cases b <;> simp [rad]

/-- The bilinear form `X_λ(ξ) = ∑_e λ_e · rad(ξ_{p e .1}) · rad(ξ_{p e .2})`. -/
noncomputable def Xform {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) (ξ : Fin n → Bool) : ℝ :=
  ∑ e, lam e * rad (ξ (p e).1) * rad (ξ (p e).2)

/-- The cosine-product `ψ`. -/
noncomputable def psi {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) : ℂ :=
  ((1 : ℝ) / (2 : ℝ)^n : ℝ) * ∑ ξ : Fin n → Bool,
    Complex.exp (Complex.I * (Xform p lam ξ : ℂ))

/-- The "energy" `s(λ) := ∑_e λ_e²`. -/
noncomputable def sval {E : Type*} [Fintype E] (lam : E → ℝ) : ℝ :=
  ∑ e, (lam e) ^ 2

/-! ### Re ψ as an average of cosines -/

lemma re_psi_eq_avg_cos {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) :
    (psi p lam).re =
      ((1 : ℝ) / (2 : ℝ)^n) * ∑ ξ : Fin n → Bool, Real.cos (Xform p lam ξ) := by
  unfold psi
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.re_sum (s := (Finset.univ : Finset (Fin n → Bool)))
      (f := fun ξ => Complex.exp (Complex.I * (Xform p lam ξ : ℂ)))]
  congr 1
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  have h1 : Complex.exp (Complex.I * (Xform p lam ξ : ℂ)) =
      Complex.cos (Xform p lam ξ) + Complex.sin (Xform p lam ξ) * Complex.I := by
    rw [show (Complex.I * (Xform p lam ξ : ℂ)) = (Xform p lam ξ : ℂ) * Complex.I from by ring]
    exact Complex.exp_mul_I _
  rw [h1]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]

/-! ### Upper bound: Re ψ ≤ 1 -/

lemma re_psi_le_one {n : ℕ} {E : Type*} [Fintype E]
    (p : E → Fin n × Fin n) (lam : E → ℝ) :
    (psi p lam).re ≤ 1 := by
  rw [re_psi_eq_avg_cos]
  have hpow : (0 : ℝ) < (2 : ℝ)^n := by positivity
  have hsum : ∑ ξ : Fin n → Bool, Real.cos (Xform p lam ξ) ≤
      ∑ _ξ : Fin n → Bool, (1 : ℝ) :=
    Finset.sum_le_sum (fun ξ _ => Real.cos_le_one _)
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2^n := by
    rw [Finset.card_univ]; simp
  calc ((1 : ℝ) / (2 : ℝ)^n) * ∑ ξ : Fin n → Bool, Real.cos (Xform p lam ξ)
      ≤ ((1 : ℝ) / (2 : ℝ)^n) * ∑ _ξ : Fin n → Bool, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((1 : ℝ) / (2 : ℝ)^n) * (Finset.univ.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((1 : ℝ) / (2 : ℝ)^n) * (2^n : ℝ) := by rw [hcard]; norm_cast
    _ = 1 := by field_simp

/-! ### Moment computation via flip-involution -/

/-- Flip the value of `ξ : Fin n → Bool` at coordinate `i₀`. -/
private def flipAt {n : ℕ} (i₀ : Fin n) (ξ : Fin n → Bool) : Fin n → Bool :=
  Function.update ξ i₀ (! ξ i₀)

private lemma flipAt_apply_eq {n : ℕ} (i₀ : Fin n) (ξ : Fin n → Bool) :
    flipAt i₀ ξ i₀ = ! ξ i₀ := by
  simp [flipAt]

private lemma flipAt_apply_ne {n : ℕ} (i₀ : Fin n) (ξ : Fin n → Bool) {k : Fin n}
    (hk : k ≠ i₀) : flipAt i₀ ξ k = ξ k := by
  simp [flipAt, Function.update_of_ne hk]

private lemma flipAt_involutive {n : ℕ} (i₀ : Fin n) (ξ : Fin n → Bool) :
    flipAt i₀ (flipAt i₀ ξ) = ξ := by
  funext k
  by_cases hk : k = i₀
  · subst hk; simp [flipAt]
  · rw [flipAt_apply_ne _ _ hk, flipAt_apply_ne _ _ hk]

private lemma flipAt_ne {n : ℕ} (i₀ : Fin n) (ξ : Fin n → Bool) :
    flipAt i₀ ξ ≠ ξ := by
  intro h
  have := congr_fun h i₀
  rw [flipAt_apply_eq] at this
  cases ξ i₀ <;> simp_all

/-- If a coordinate `i₀` appears with multiplicity 1 or 3 in `(a,b,c,d)`, the average
of `rad(ξ_a)·rad(ξ_b)·rad(ξ_c)·rad(ξ_d)` over `ξ` is zero, by pairing each `ξ` with its
flip at `i₀`. -/
lemma sum_rad_quadruple_eq_zero_of_unique {n : ℕ} (a b c d : Fin n) (i₀ : Fin n)
    (ha : a = i₀) (hb : b ≠ i₀) (hc : c ≠ i₀) (hd : d ≠ i₀) :
    ∑ ξ : Fin n → Bool, rad (ξ a) * rad (ξ b) * rad (ξ c) * rad (ξ d) = 0 := by
  classical
  refine Finset.sum_involution
    (g := fun ξ _ => flipAt i₀ ξ)
    (hg₁ := ?_)
    (hg₃ := ?_)
    (g_mem := fun _ _ => Finset.mem_univ _)
    (hg₄ := fun ξ _ => flipAt_involutive i₀ ξ)
  · -- f(ξ) + f(flipAt i₀ ξ) = 0
    intro ξ _
    -- Compute the rad factors after flipping.
    have h_a : rad (flipAt i₀ ξ a) = - rad (ξ a) := by
      rw [ha, flipAt_apply_eq, rad_not]
    have h_b : rad (flipAt i₀ ξ b) = rad (ξ b) := by
      rw [flipAt_apply_ne _ _ hb]
    have h_c : rad (flipAt i₀ ξ c) = rad (ξ c) := by
      rw [flipAt_apply_ne _ _ hc]
    have h_d : rad (flipAt i₀ ξ d) = rad (ξ d) := by
      rw [flipAt_apply_ne _ _ hd]
    rw [h_a, h_b, h_c, h_d]
    ring
  · -- flipAt i₀ ξ ≠ ξ
    intro ξ _ _
    exact flipAt_ne i₀ ξ

/-- Same as above but with `b = i₀` instead of `a = i₀`. -/
lemma sum_rad_quadruple_eq_zero_of_unique' {n : ℕ} (a b c d : Fin n) (i₀ : Fin n)
    (ha : a ≠ i₀) (hb : b = i₀) (hc : c ≠ i₀) (hd : d ≠ i₀) :
    ∑ ξ : Fin n → Bool, rad (ξ a) * rad (ξ b) * rad (ξ c) * rad (ξ d) = 0 := by
  classical
  refine Finset.sum_involution
    (g := fun ξ _ => flipAt i₀ ξ)
    (hg₁ := ?_)
    (hg₃ := ?_)
    (g_mem := fun _ _ => Finset.mem_univ _)
    (hg₄ := fun ξ _ => flipAt_involutive i₀ ξ)
  · intro ξ _
    have h_a : rad (flipAt i₀ ξ a) = rad (ξ a) := by
      rw [flipAt_apply_ne _ _ ha]
    have h_b : rad (flipAt i₀ ξ b) = - rad (ξ b) := by
      rw [hb, flipAt_apply_eq, rad_not]
    have h_c : rad (flipAt i₀ ξ c) = rad (ξ c) := by
      rw [flipAt_apply_ne _ _ hc]
    have h_d : rad (flipAt i₀ ξ d) = rad (ξ d) := by
      rw [flipAt_apply_ne _ _ hd]
    rw [h_a, h_b, h_c, h_d]
    ring
  · intro ξ _ _
    exact flipAt_ne i₀ ξ

/-- Off-diagonal sum is zero (the main case analysis). -/
lemma sum_rad_quadruple_off_diag {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) :
    ∑ ξ : Fin n → Bool, rad (ξ a) * rad (ξ b) * rad (ξ c) * rad (ξ d) = 0 := by
  classical
  -- We pick i₀ to be either `a` or `b` whichever appears uniquely.
  by_cases h_a_in_cd : a = c ∨ a = d
  · -- `a` is in {c, d}. Then we use `b` (which appears once).
    -- Need: a ≠ b, b ≠ a, b ≠ c, b ≠ d.
    have hab' : a ≠ b := ne_of_lt hab
    rcases h_a_in_cd with hac | had
    · -- a = c. Then since (a,b) ≠ (c,d) = (a,d), b ≠ d. Also b ≠ c = a.
      have hbd : b ≠ d := fun h => hne (by rw [hac, h])
      have hbc : b ≠ c := by rw [← hac]; exact hab'.symm
      apply sum_rad_quadruple_eq_zero_of_unique' (i₀ := b)
      · exact hab'
      · rfl
      · exact hbc.symm
      · exact hbd.symm
    · -- a = d. Then c < d = a < b, so b > a > c, so b ≠ c, b ≠ d = a, b ≠ a.
      have hbc : b ≠ c := by
        intro h; rw [h] at hab
        have : c < a := had ▸ hcd
        exact absurd (lt_trans hab this) (lt_irrefl _)
      have hbd : b ≠ d := by rw [← had]; exact hab'.symm
      apply sum_rad_quadruple_eq_zero_of_unique' (i₀ := b)
      · exact hab'
      · rfl
      · exact hbc.symm
      · exact hbd.symm
  · -- `a` is NOT in {c, d}, so a ≠ c, a ≠ d. Also a ≠ b. Use a.
    push_neg at h_a_in_cd
    obtain ⟨hac, had⟩ := h_a_in_cd
    have hab' : a ≠ b := ne_of_lt hab
    apply sum_rad_quadruple_eq_zero_of_unique (i₀ := a)
    · rfl
    · exact hab'.symm
    · exact hac.symm
    · exact had.symm

/-- Diagonal case: `e = e'`. -/
lemma sum_rad_quadruple_diag {n : ℕ} (a b : Fin n) :
    ∑ ξ : Fin n → Bool, rad (ξ a) * rad (ξ b) * rad (ξ a) * rad (ξ b) = (2 : ℝ)^n := by
  classical
  have hsimp : ∀ ξ : Fin n → Bool,
      rad (ξ a) * rad (ξ b) * rad (ξ a) * rad (ξ b) = 1 := by
    intro ξ
    have h1 := rad_sq (ξ a)
    have h2 := rad_sq (ξ b)
    nlinarith [h1, h2]
  simp_rw [hsimp]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ]
  simp

/-! ### Moment identity -/

lemma avg_Xform_sq_eq {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → Fin n × Fin n)
    (hp_lt : ∀ e, (p e).1 < (p e).2)
    (hp_inj : Function.Injective p)
    (lam : E → ℝ) :
    ((1 : ℝ) / (2 : ℝ)^n) * ∑ ξ : Fin n → Bool, (Xform p lam ξ)^2 = sval lam := by
  classical
  have hpow : (0 : ℝ) < (2 : ℝ)^n := by positivity
  have hexpand : ∀ ξ : Fin n → Bool, (Xform p lam ξ)^2 =
      ∑ e, ∑ e',
        (lam e * lam e') *
        (rad (ξ (p e).1) * rad (ξ (p e).2) * rad (ξ (p e').1) * rad (ξ (p e').2)) := by
    intro ξ
    unfold Xform
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun e' _ => ?_))
    ring
  have hsum_swap :
      ∑ ξ : Fin n → Bool, (Xform p lam ξ)^2 =
        ∑ e, ∑ e', (lam e * lam e') *
          ∑ ξ : Fin n → Bool,
            (rad (ξ (p e).1) * rad (ξ (p e).2) * rad (ξ (p e').1) * rad (ξ (p e').2)) := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [← Finset.mul_sum]
  rw [hsum_swap]
  have hinner : ∀ e e' : E,
      ∑ ξ : Fin n → Bool,
        (rad (ξ (p e).1) * rad (ξ (p e).2) * rad (ξ (p e').1) * rad (ξ (p e').2)) =
      if e = e' then (2 : ℝ)^n else 0 := by
    intro e e'
    by_cases h : e = e'
    · subst h
      rw [if_pos rfl]
      exact sum_rad_quadruple_diag (p e).1 (p e).2
    · rw [if_neg h]
      apply sum_rad_quadruple_off_diag _ _ _ _ (hp_lt e) (hp_lt e')
      intro heq
      apply h
      apply hp_inj
      rw [Prod.mk.injEq] at heq
      exact Prod.ext heq.1 heq.2
  simp_rw [hinner]
  -- Now sum over e, e' with most terms vanishing.
  rw [Finset.mul_sum]
  unfold sval
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single e
        (fun e' _ hne => by rw [if_neg (Ne.symm hne)]; ring)
        (fun h => absurd (Finset.mem_univ e) h)]
  rw [if_pos rfl]
  field_simp

/-- The main theorem. -/
theorem re_psi_taylor4_decomposition {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → Fin n × Fin n)
    (hp_lt : ∀ e, (p e).1 < (p e).2)
    (hp_inj : Function.Injective p)
    (lam : E → ℝ) (hs : sval lam ≤ 1 / 2) :
    3 / 4 ≤ (psi p lam).re ∧ (psi p lam).re ≤ 1 := by
  refine ⟨?_, re_psi_le_one p lam⟩
  rw [re_psi_eq_avg_cos]
  have hpow : (0 : ℝ) < (2 : ℝ)^n := by positivity
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2^n := by
    rw [Finset.card_univ]; simp
  have hcos : ∀ ξ, (1 : ℝ) - (Xform p lam ξ)^2 / 2 ≤ Real.cos (Xform p lam ξ) :=
    fun _ => Real.one_sub_sq_div_two_le_cos
  have hsum_lb : ∑ ξ : Fin n → Bool, ((1 : ℝ) - (Xform p lam ξ)^2 / 2) ≤
      ∑ ξ : Fin n → Bool, Real.cos (Xform p lam ξ) :=
    Finset.sum_le_sum (fun ξ _ => hcos ξ)
  have hsplit : ∑ ξ : Fin n → Bool, ((1 : ℝ) - (Xform p lam ξ)^2 / 2) =
      (2 : ℝ)^n - (1/2) * ∑ ξ : Fin n → Bool, (Xform p lam ξ)^2 := by
    rw [show (fun ξ : Fin n → Bool => (1 : ℝ) - (Xform p lam ξ)^2 / 2)
            = (fun ξ => (1 : ℝ) - (1/2) * (Xform p lam ξ)^2) from by funext; ring]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]
    push_cast; ring
  have hmom := avg_Xform_sq_eq p hp_lt hp_inj lam
  have hlb : ((1 : ℝ) / (2 : ℝ)^n) *
      ∑ ξ : Fin n → Bool, ((1 : ℝ) - (Xform p lam ξ)^2 / 2) ≤
      ((1 : ℝ) / (2 : ℝ)^n) * ∑ ξ : Fin n → Bool, Real.cos (Xform p lam ξ) :=
    mul_le_mul_of_nonneg_left hsum_lb (by positivity)
  have hclosed : ((1 : ℝ) / (2 : ℝ)^n) *
      ∑ ξ : Fin n → Bool, ((1 : ℝ) - (Xform p lam ξ)^2 / 2) =
      1 - (1/2) * ((1 / (2:ℝ)^n) * ∑ ξ : Fin n → Bool, (Xform p lam ξ)^2) := by
    rw [hsplit]; field_simp
  rw [hclosed, hmom] at hlb
  linarith

end LeaHadamard.Hadamard
