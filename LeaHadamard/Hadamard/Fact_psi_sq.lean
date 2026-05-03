import Mathlib

open scoped BigOperators
open Complex Real

namespace LeaHadamard.Hadamard

/-! ## Cosine-product bound on `|ψ(γ)|²` -/

/-- A Rademacher sign at index `i`. -/
private def rad {n : ℕ} (ξ : Fin n → Bool) (i : Fin n) : ℝ :=
  if ξ i then 1 else -1

private lemma rad_sq {n : ℕ} (ξ : Fin n → Bool) (i : Fin n) :
    rad ξ i * rad ξ i = 1 := by
  unfold rad; cases ξ i <;> simp

private lemma rad_mul_self {n : ℕ} (ξ : Fin n → Bool) (i : Fin n) :
    (rad ξ i)^2 = 1 := by
  rw [sq, rad_sq]

private lemma abs_rad {n : ℕ} (ξ : Fin n → Bool) (i : Fin n) :
    |rad ξ i| = 1 := by
  unfold rad; cases ξ i <;> simp

private lemma rad_update_ne {n : ℕ} (ξ : Fin n → Bool) (k : Fin n) (b : Bool)
    {i : Fin n} (h : i ≠ k) : rad (Function.update ξ k b) i = rad ξ i := by
  unfold rad
  rw [Function.update_of_ne h]

private lemma rad_update_self_true {n : ℕ} (ξ : Fin n → Bool) (k : Fin n) :
    rad (Function.update ξ k true) k = 1 := by
  unfold rad; simp

private lemma rad_update_self_false {n : ℕ} (ξ : Fin n → Bool) (k : Fin n) :
    rad (Function.update ξ k false) k = -1 := by
  unfold rad; simp

/-- The "edge weight" between two distinct indices, picking the canonical
ordering `(min, max)` so that the result is symmetric. -/
private def edge {n : ℕ} (γ : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  if i < j then γ i j else if j < i then γ j i else 0

private lemma edge_diag {n : ℕ} (γ : Fin n → Fin n → ℝ) (i : Fin n) :
    edge γ i i = 0 := by
  unfold edge; simp

private lemma edge_symm {n : ℕ} (γ : Fin n → Fin n → ℝ) (i j : Fin n) :
    edge γ i j = edge γ j i := by
  unfold edge
  rcases lt_trichotomy i j with h | h | h
  · simp [h, asymm h]
  · subst h; simp
  · simp [h, asymm h]

/-- The phase function `Φ(ξ) = ∑_{i<j} γ_{ij} ξ_i ξ_j`,
    written symmetrically via `(1/2) ∑_{i,j} edge(i,j) ξ_i ξ_j`. -/
private noncomputable def phase {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) : ℝ :=
  (1/2) * ∑ i : Fin n, ∑ j : Fin n, edge γ i j * rad ξ i * rad ξ j

/-- The "k-linear" coefficient `L_k(ξ_{≠k}) = ∑_{i ≠ k} γ_{ik} ξ_i`. -/
private noncomputable def Lcoef {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) (k : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase k, edge γ i k * rad ξ i

/-- The "k-quadratic" coefficient `Q_k(ξ_{≠k}) = ∑_{i<j, i,j≠k} γ_{ij} ξ_i ξ_j`. -/
private noncomputable def Qcoef {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) (k : Fin n) : ℝ :=
  (1/2) *
    ∑ i ∈ Finset.univ.erase k, ∑ j ∈ Finset.univ.erase k,
      edge γ i j * rad ξ i * rad ξ j

/-- Splitting the phase by extracting the index `k`:
`Φ(ξ) = ξ_k · L_k(ξ_{≠k}) + Q_k(ξ_{≠k})`, where the `≠k` part doesn't see ξ_k. -/
private lemma phase_split {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) (k : Fin n) :
    phase γ ξ = rad ξ k * Lcoef γ ξ k + Qcoef γ ξ k := by
  unfold phase Lcoef Qcoef
  -- Split outer sum by i = k vs i ≠ k.
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  -- Split each inner sum (over j) into j ≠ k and j = k.
  have hinner : ∀ i : Fin n,
      (∑ j : Fin n, edge γ i j * rad ξ i * rad ξ j) =
        (∑ j ∈ Finset.univ.erase k, edge γ i j * rad ξ i * rad ξ j) +
          edge γ i k * rad ξ i * rad ξ k := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  -- Apply the splitting to the outer-erase sum and to the i=k term.
  conv_lhs =>
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [hinner k]
  rw [edge_diag]
  simp only [zero_mul]
  rw [add_zero]
  -- Distribute the outer sum over the pair `(j ≠ k sum) + edge_ik`.
  rw [Finset.sum_add_distrib]
  -- Identify the linear-in-ξ_k piece: rewrite `edge γ i k * rad ξ i * rad ξ k`
  -- as `rad ξ k * (edge γ i k * rad ξ i)`, factor `rad ξ k` out, getting `rad ξ k * Lcoef`.
  have hsym2 : ∀ i ∈ Finset.univ.erase k,
      edge γ i k * rad ξ i * rad ξ k = rad ξ k * (edge γ i k * rad ξ i) := by
    intro i _; ring
  rw [Finset.sum_congr rfl hsym2, ← Finset.mul_sum]
  -- The i = k inner-sum has all terms involving `rad ξ k` and `edge γ k j`.
  have hsym1 : ∀ j ∈ Finset.univ.erase k,
      edge γ k j * rad ξ k * rad ξ j = rad ξ k * (edge γ j k * rad ξ j) := by
    intro j _
    rw [edge_symm]; ring
  rw [Finset.sum_congr rfl hsym1, ← Finset.mul_sum]
  ring

/-- `L_k` and `Q_k` don't depend on `ξ k`. -/
private lemma Lcoef_update {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) (k : Fin n) (b : Bool) :
    Lcoef γ (Function.update ξ k b) k = Lcoef γ ξ k := by
  unfold Lcoef
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [rad_update_ne ξ k b (Finset.mem_erase.mp hi).1]

private lemma Qcoef_update {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) (k : Fin n) (b : Bool) :
    Qcoef γ (Function.update ξ k b) k = Qcoef γ ξ k := by
  unfold Qcoef
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [rad_update_ne ξ k b (Finset.mem_erase.mp hi).1,
      rad_update_ne ξ k b (Finset.mem_erase.mp hj).1]

/-- Pairing: averaging `exp(iΦ)` over `ξ_k ∈ {±1}` gives `cos(L_k) exp(iQ_k)`. -/
private lemma exp_phase_average {n : ℕ} (γ : Fin n → Fin n → ℝ)
    (ξ : Fin n → Bool) (k : Fin n) :
    Complex.exp (Complex.I * (phase γ (Function.update ξ k true) : ℂ)) +
      Complex.exp (Complex.I * (phase γ (Function.update ξ k false) : ℂ)) =
    2 * Real.cos (Lcoef γ ξ k) *
      Complex.exp (Complex.I * (Qcoef γ ξ k : ℂ)) := by
  rw [phase_split γ (Function.update ξ k true) k,
      phase_split γ (Function.update ξ k false) k,
      Lcoef_update, Qcoef_update,
      Lcoef_update, Qcoef_update,
      rad_update_self_true, rad_update_self_false]
  set L : ℝ := Lcoef γ ξ k
  set Q : ℝ := Qcoef γ ξ k
  -- LHS = exp(I*(L + Q)) + exp(I*(-L + Q)) = exp(I*Q)(exp(I*L) + exp(-I*L)) = 2 cos(L) exp(I*Q)
  have hLHS :
      Complex.exp (Complex.I * ((1 * L + Q : ℝ) : ℂ)) +
        Complex.exp (Complex.I * ((-1 * L + Q : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (Q : ℂ)) *
        (Complex.exp (Complex.I * (L : ℂ)) +
          Complex.exp (-(Complex.I * (L : ℂ)))) := by
    push_cast
    rw [show Complex.I * (1 * (L : ℂ) + (Q : ℂ)) =
          Complex.I * (Q : ℂ) + Complex.I * (L : ℂ) from by ring,
        show Complex.I * (-1 * (L : ℂ) + (Q : ℂ)) =
          Complex.I * (Q : ℂ) + -(Complex.I * (L : ℂ)) from by ring,
        Complex.exp_add, Complex.exp_add, mul_add]
  rw [hLHS]
  -- exp(I L) + exp(-I L) = 2 cos L (with cos as Complex.cos, then convert)
  have hcos : Complex.exp (Complex.I * (L : ℂ)) +
                Complex.exp (-(Complex.I * (L : ℂ))) =
              2 * (Real.cos L : ℂ) := by
    rw [show Complex.I * (L : ℂ) = (L : ℂ) * Complex.I from by ring,
        show -(((L : ℂ)) * Complex.I) = ((-L : ℝ) : ℂ) * Complex.I from by push_cast; ring,
        Complex.exp_mul_I, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hcos]
  ring

/-- The characteristic function `ψ(γ)`. -/
private noncomputable def psi {n : ℕ} (γ : Fin n → Fin n → ℝ) : ℂ :=
  ((1 : ℝ) / (2 ^ n : ℝ) : ℂ) *
    ∑ ξ : Fin n → Bool, Complex.exp (Complex.I * (phase γ ξ : ℂ))

/-- A reformulation of `ψ` using the splitting at index `k`:
`Σ_ξ exp(iΦ) = 2 · Σ_η cos(L_k(η)) exp(iQ_k(η))`,
where the outer sum is over `η : Fin n → Bool` (the value at `k` is irrelevant).

Concretely, we use the equivalence `(Fin n → Bool) ≃ Bool × ({i // i ≠ k} → Bool)`
to split the sum over `ξ` into `(b : Bool)` and the values at indices `≠ k`. -/
private lemma sum_exp_phase_eq {n : ℕ} (γ : Fin n → Fin n → ℝ) (k : Fin n) :
    (∑ ξ : Fin n → Bool, Complex.exp (Complex.I * (phase γ ξ : ℂ))) =
      2 * ∑ η : {i : Fin n // i ≠ k} → Bool,
        ((Real.cos (Lcoef γ
            (Function.update (fun i : Fin n => if h : i = k then false else η ⟨i, h⟩) k false)
            k) : ℂ) *
          Complex.exp (Complex.I *
            (Qcoef γ
              (Function.update (fun i : Fin n => if h : i = k then false else η ⟨i, h⟩) k false)
              k : ℂ))) := by
  -- Use the equivalence (Fin n → Bool) ≃ Bool × ({i // i ≠ k} → Bool).
  let e : (Fin n → Bool) ≃ Bool × ({i // i ≠ k} → Bool) := Equiv.funSplitAt k Bool
  -- Σ_ξ f(ξ) = Σ_p f(e.symm p) using Fintype.sum_equiv with the equiv `e`.
  have hreindex :
      (∑ ξ : Fin n → Bool, Complex.exp (Complex.I * (phase γ ξ : ℂ))) =
      ∑ p : Bool × ({i : Fin n // i ≠ k} → Bool),
          Complex.exp (Complex.I * (phase γ (e.symm p) : ℂ)) := by
    refine Fintype.sum_equiv e
        (fun ξ => Complex.exp (Complex.I * (phase γ ξ : ℂ)))
        (fun p => Complex.exp (Complex.I * (phase γ (e.symm p) : ℂ))) ?_
    intro ξ
    simp only [e.symm_apply_apply]
  rw [hreindex, Fintype.sum_prod_type]
  rw [show (∑ x : Bool, ∑ y : ({i : Fin n // i ≠ k} → Bool),
              Complex.exp (Complex.I * (phase γ (e.symm (x, y)) : ℂ))) =
            (∑ y : ({i : Fin n // i ≠ k} → Bool), ∑ x : Bool,
              Complex.exp (Complex.I * (phase γ (e.symm (x, y)) : ℂ))) from
        Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro η _
  -- Reconstruct from η.
  set ξ₀ : Fin n → Bool := fun i => if h : i = k then false else η ⟨i, h⟩ with hξ₀
  have h_recon : ∀ b : Bool,
      e.symm (b, η) = Function.update ξ₀ k b := by
    intro b
    funext i
    by_cases hi : i = k
    · subst hi
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update]
    · -- For i ≠ k, both sides reduce to η ⟨i, hi⟩.
      have hξ : ξ₀ i = η ⟨i, hi⟩ := by simp [ξ₀, hi]
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update, hi, hξ]
  rw [show (∑ b : Bool, Complex.exp (Complex.I * (phase γ (e.symm (b, η)) : ℂ))) =
        (Complex.exp (Complex.I * (phase γ (Function.update ξ₀ k true) : ℂ)) +
         Complex.exp (Complex.I * (phase γ (Function.update ξ₀ k false) : ℂ))) by
        rw [show (∑ b : Bool, Complex.exp (Complex.I * (phase γ (e.symm (b, η)) : ℂ))) =
              Complex.exp (Complex.I * (phase γ (e.symm (true, η)) : ℂ)) +
              Complex.exp (Complex.I * (phase γ (e.symm (false, η)) : ℂ)) from by
              rw [Fintype.sum_bool]
            ]
        rw [h_recon true, h_recon false]]
  rw [exp_phase_average γ ξ₀ k]
  rw [Lcoef_update γ ξ₀ k false, Qcoef_update γ ξ₀ k false]
  ring

/-- **The cosine-product bound.**

For any `n : ℕ`, any **symmetric** edge weight `γ : Fin n → Fin n → ℝ`
(i.e. `γ i j = γ j i`), and any index `k : Fin n`,

  `|ψ(γ)|² ≤ 1/2 + 1/2 · ∏_{i ≠ k} cos(2 γ i k)`,

where `ψ(γ) = 𝔼_ξ[exp(i · ∑_{i<j} γ_{ij} ξ_i ξ_j)]` is the Rademacher
characteristic function defined above.  The natural-language statement uses
the unordered-pair notation `γ_{{i,j}}`, which we encode by requiring
`γ` to be symmetric.  No bound on the size of `γ` is needed. -/
theorem universal_magnitude_bound_full
    {n : ℕ} (γ : Fin n → Fin n → ℝ) (hγ : ∀ i j, γ i j = γ j i)
    (k : Fin n) :
    Complex.normSq (psi γ) ≤
      (1 : ℝ) / 2 + (1 : ℝ) / 2 *
        ∏ i ∈ Finset.univ.erase k, Real.cos (2 * γ i k) := by
  -- Abbreviation for the helper "η-functions" type.
  -- The sum-over-ξ representation, factored through the equivalence at index k.
  set IxType := ({i : Fin n // i ≠ k} → Bool)
  -- Define `g : IxType → ℂ` to be `cos(L_k) · exp(i Q_k)` evaluated on the
  -- canonical lift `update (extend η) k false`.
  let lift : IxType → (Fin n → Bool) :=
    fun η => fun i => if h : i = k then false else η ⟨i, h⟩
  let L : IxType → ℝ := fun η => Lcoef γ (lift η) k
  let Q : IxType → ℝ := fun η => Qcoef γ (lift η) k
  let g : IxType → ℂ := fun η => (Real.cos (L η) : ℂ) * Complex.exp (Complex.I * (Q η : ℂ))
  -- Step 1: psi γ = 2 / 2^n · Σ_η g η.
  have hpsi : psi γ = (((2 : ℝ) / (2 ^ n : ℝ) : ℝ) : ℂ) * ∑ η : IxType, g η := by
    unfold psi
    rw [sum_exp_phase_eq γ k]
    -- Adjust the form: the sum_exp_phase_eq uses `Function.update (lift η) k false` inside
    -- L and Q, but they're equal to `Lcoef γ (lift η) k` and `Qcoef γ (lift η) k` by Lcoef_update.
    have : (∑ η : IxType,
            ((Real.cos (Lcoef γ
                (Function.update (lift η) k false) k) : ℂ) *
              Complex.exp (Complex.I *
                (Qcoef γ (Function.update (lift η) k false) k : ℂ)))) =
           ∑ η : IxType, g η := by
      refine Finset.sum_congr rfl ?_
      intro η _
      rw [Lcoef_update γ (lift η) k false, Qcoef_update γ (lift η) k false]
    rw [this]
    push_cast
    ring
  -- Step 2: |Σ g|² ≤ N · Σ |g|² where N = card IxType = 2^(n-1).
  -- And |g η| = |cos(L η)|, so |g η|² = cos²(L η).
  have hg_abs_sq : ∀ η : IxType, Complex.normSq (g η) = (Real.cos (L η))^2 := by
    intro η
    simp only [g]
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    have hexp : Complex.normSq (Complex.exp (Complex.I * (Q η : ℂ))) = 1 := by
      rw [Complex.normSq_eq_norm_sq]
      rw [show Complex.I * (Q η : ℂ) = ((Q η : ℝ) : ℂ) * Complex.I from by ring,
          Complex.norm_exp_ofReal_mul_I]
      norm_num
    rw [hexp, mul_one, sq]
  -- Step 3: compute card(IxType) = 2^(n-1).  Since `k : Fin n`, n ≥ 1.
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun hn0 => by subst hn0; exact (Fin.elim0 k))
  have hcard_sub : (Finset.univ : Finset {i : Fin n // i ≠ k}).card = n - 1 := by
    rw [Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_ofSubsingleton,
        Fintype.card_fin]
  have hcard_ix : Fintype.card IxType = 2 ^ (n - 1) := by
    show Fintype.card ({i : Fin n // i ≠ k} → Bool) = 2 ^ (n - 1)
    rw [Fintype.card_pi]
    simp [Fintype.card_subtype_compl, Fintype.card_fin]
  have hpow : (2 : ℝ)^n = 2 * 2^(n - 1) := by
    have hh : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hh]
    rw [pow_succ]; ring
  -- Step 4: triangle + Cauchy-Schwarz on |Σ g|².
  have htri : Complex.normSq (∑ η : IxType, g η) ≤
      (Fintype.card IxType : ℝ) * ∑ η : IxType, Complex.normSq (g η) := by
    -- |Σ z|² ≤ (Σ |z|)² ≤ N · Σ |z|².
    have h1 : ‖∑ η : IxType, g η‖ ≤ ∑ η : IxType, ‖g η‖ :=
      norm_sum_le _ _
    have hsum_nn : 0 ≤ ∑ η : IxType, ‖g η‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h2 : ‖∑ η : IxType, g η‖^2 ≤ (∑ η : IxType, ‖g η‖)^2 := by
      have hnn : 0 ≤ ‖∑ η : IxType, g η‖ := norm_nonneg _
      exact pow_le_pow_left₀ hnn h1 2
    have h3 : (∑ η : IxType, ‖g η‖)^2 ≤
        (Finset.univ : Finset IxType).card * ∑ η : IxType, ‖g η‖^2 :=
      sq_sum_le_card_mul_sum_sq
    have h4 : ‖∑ η : IxType, g η‖^2 ≤
        (Finset.univ : Finset IxType).card * ∑ η : IxType, ‖g η‖^2 := h2.trans h3
    -- Convert to normSq.
    rw [Complex.normSq_eq_norm_sq]
    have hnSq : ∀ η : IxType, ‖g η‖^2 = Complex.normSq (g η) := by
      intro η; rw [← Complex.normSq_eq_norm_sq]
    simp_rw [hnSq] at h4
    rw [show (Finset.univ : Finset IxType).card = Fintype.card IxType from rfl] at h4
    exact_mod_cast h4
  -- Step 5: combine.
  --   normSq (psi γ)
  -- = (2/2^n)² · normSq (Σ_η g η)
  -- ≤ (2/2^n)² · (Fintype.card IxType : ℝ) · Σ_η cos²(L η)
  -- = (4/4^n) · 2^(n-1) · Σ cos²(L)
  -- = (2/2^n) · Σ cos²(L)
  -- Step 6: Σ cos²(L) = (Σ 1 + Σ cos(2L))/2
  -- Step 7: Σ cos(2 L η) = 2^(n-1) · ∏ cos(2 edge_ik)
  -- Step 8: edge γ i k = γ i k.
  -- Compute normSq (psi γ).
  have hpsi_sq : Complex.normSq (psi γ) =
      (2 / (2 ^ n : ℝ))^2 * Complex.normSq (∑ η : IxType, g η) := by
    rw [hpsi]
    rw [Complex.normSq_mul]
    congr 1
    rw [Complex.normSq_ofReal, sq]
  -- Bound normSq(Σ g η) ≤ 2^(n-1) · Σ cos²(L η).
  have hbound1 : Complex.normSq (∑ η : IxType, g η) ≤
      (2^(n-1) : ℝ) * ∑ η : IxType, (Real.cos (L η))^2 := by
    have htri' := htri
    rw [hcard_ix] at htri'
    have hsum_eq : (∑ η : IxType, Complex.normSq (g η)) =
        ∑ η : IxType, (Real.cos (L η))^2 := by
      refine Finset.sum_congr rfl ?_
      intro η _
      exact hg_abs_sq η
    rw [hsum_eq] at htri'
    push_cast at htri'
    exact htri'
  -- cos²(L η) = 1/2 + (1/2) cos(2 L η).
  have hcos_sq : ∀ η : IxType,
      (Real.cos (L η))^2 = (1/2 : ℝ) + (1/2) * Real.cos (2 * L η) := by
    intro η
    have h := Real.cos_two_mul (L η)
    -- cos(2x) = 2 cos² x - 1, so cos² x = (cos 2x + 1)/2
    linarith
  -- Σ_η cos(2 L η) = 2^(n-1) · ∏_{i≠k} cos(2 edge γ i k).
  have hsum_cos : (∑ η : IxType, Real.cos (2 * L η)) =
      (2^(n-1) : ℝ) * ∏ i ∈ Finset.univ.erase k, Real.cos (2 * edge γ i k) := by
    -- Subtype equivalence: erase k ↔ {i // i ≠ k}.
    have hmem : ∀ x : Fin n, x ∈ Finset.univ.erase k ↔ x ≠ k := by
      intro x; simp [Finset.mem_erase]
    -- Helper: σ b = 1 if b = true, -1 if b = false.
    let σ : Bool → ℝ := fun b => if b = true then 1 else -1
    let σC : Bool → ℂ := fun b => if b = true then 1 else -1
    -- Step 1: rewrite L η as sum over subtype.
    have hL_eq : ∀ η : IxType,
        L η = ∑ p : {i : Fin n // i ≠ k}, edge γ p.val k * σ (η p) := by
      intro η
      simp only [L, Lcoef]
      rw [Finset.sum_subtype (Finset.univ.erase k) hmem
            (fun i => edge γ i k * rad (lift η) i)]
      refine Finset.sum_congr rfl ?_
      intro p _
      simp only [rad, lift, σ]
      have hp : p.val ≠ k := p.property
      simp [hp]
    -- Step 2: in ℂ, Σ_η exp(2i L η) = ∏_p (e^{2i e_p} + e^{-2i e_p}).
    -- Define the per-edge complex coefficient:
    let cw : {i : Fin n // i ≠ k} → ℂ :=
      fun p => Complex.exp (2 * Complex.I * (edge γ p.val k : ℂ)) +
               Complex.exp (-(2 * Complex.I * (edge γ p.val k : ℂ)))
    have hcomplex :
        (∑ η : IxType, Complex.exp (2 * Complex.I * (L η : ℂ))) =
        ∏ p : {i : Fin n // i ≠ k}, cw p := by
      -- exp(2i L η) = ∏_p exp(2i e_p · σ(η p)) where σ(true)=1, σ(false)=-1.
      have hfac : ∀ η : IxType,
          Complex.exp (2 * Complex.I * (L η : ℂ)) =
            ∏ p : {i : Fin n // i ≠ k},
              Complex.exp (2 * Complex.I * (edge γ p.val k : ℂ) * σC (η p)) := by
        intro η
        rw [hL_eq η]
        push_cast
        rw [← Complex.exp_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro p _
        simp only [σ, σC]
        cases η p <;> simp
      simp_rw [hfac]
      -- Σ_η ∏_p f_p(η p) = ∏_p Σ_b f_p(b)  by Fintype.prod_sum.
      rw [← Fintype.prod_sum (κ := fun _ : {i : Fin n // i ≠ k} => Bool)
            (fun p b => Complex.exp (2 * Complex.I * (edge γ p.val k : ℂ) * σC b))]
      refine Finset.prod_congr rfl ?_
      intro p _
      rw [Fintype.sum_bool]
      simp only [cw, σC]
      have h1 : (2 : ℂ) * Complex.I * (edge γ p.val k : ℂ) * (1 : ℂ) =
                2 * Complex.I * (edge γ p.val k : ℂ) := by ring
      have h2 : (2 : ℂ) * Complex.I * (edge γ p.val k : ℂ) * (-1 : ℂ) =
                -(2 * Complex.I * (edge γ p.val k : ℂ)) := by ring
      have hT : (if (True : Prop) then (1 : ℂ) else -1) = 1 := by simp
      have hF : (if false = true then (1 : ℂ) else -1) = -1 := by simp
      rw [hT, hF, h1, h2]
    -- Step 3: each factor equals 2 cos(2 e_p).
    have hfactor : ∀ p : {i : Fin n // i ≠ k},
        cw p = ((2 * Real.cos (2 * edge γ p.val k) : ℝ) : ℂ) := by
      intro p
      simp only [cw]
      rw [show (2 * Complex.I * (edge γ p.val k : ℂ)) =
            ((2 * edge γ p.val k : ℝ) : ℂ) * Complex.I from by push_cast; ring,
          show -(((2 * edge γ p.val k : ℝ) : ℂ) * Complex.I) =
            (((-(2 * edge γ p.val k) : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
          Complex.exp_mul_I, Complex.exp_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    -- Step 4: take real parts.
    -- LHS Re: Σ_η Re(exp(2i L η)) = Σ_η cos(2 L η).
    have hre_exp : ∀ η : IxType,
        (Complex.exp (2 * Complex.I * (L η : ℂ))).re = Real.cos (2 * L η) := by
      intro η
      have heq : (2 * Complex.I * (L η : ℂ)) = ((2 * L η : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [heq, Complex.exp_mul_I, Complex.add_re, Complex.mul_re,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hre_lhs : (∑ η : IxType, Real.cos (2 * L η)) =
        (∑ η : IxType, Complex.exp (2 * Complex.I * (L η : ℂ))).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun η _ => (hre_exp η).symm)
    -- RHS Re: ∏ ((2 cos ...) : ℂ).re = ∏ 2 cos ....
    have hre_rhs :
        (∏ p : {i : Fin n // i ≠ k}, cw p).re =
        ∏ p : {i : Fin n // i ≠ k}, 2 * Real.cos (2 * edge γ p.val k) := by
      rw [show (∏ p : {i : Fin n // i ≠ k}, cw p) =
            ∏ p : {i : Fin n // i ≠ k},
              ((2 * Real.cos (2 * edge γ p.val k) : ℝ) : ℂ) from
        Finset.prod_congr rfl (fun p _ => hfactor p)]
      rw [← Complex.ofReal_prod, Complex.ofReal_re]
    -- Combine:
    rw [hre_lhs, hcomplex, hre_rhs]
    -- ∏ (2 * cos) = 2^N · ∏ cos.
    rw [show (∏ p : {i : Fin n // i ≠ k}, 2 * Real.cos (2 * edge γ p.val k)) =
          (∏ _p : {i : Fin n // i ≠ k}, (2 : ℝ)) *
            ∏ p : {i : Fin n // i ≠ k}, Real.cos (2 * edge γ p.val k) from
        Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_univ]
    -- Card of {i // i ≠ k} = n - 1.
    have hcard_sub' : Fintype.card {i : Fin n // i ≠ k} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin]
    rw [hcard_sub']
    -- Reindex product over subtype back to the erase-k product.
    rw [show (∏ p : {i : Fin n // i ≠ k}, Real.cos (2 * edge γ p.val k)) =
          ∏ i ∈ Finset.univ.erase k, Real.cos (2 * edge γ i k) from
        (Finset.prod_subtype (Finset.univ.erase k) hmem
          (fun i => Real.cos (2 * edge γ i k))).symm]
  -- edge γ i k = γ i k for i ≠ k (by symmetry).
  have hedge : ∀ i ∈ Finset.univ.erase k, edge γ i k = γ i k := by
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    unfold edge
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · simp [hlt]
    · simp only [if_neg (asymm hgt), if_pos hgt]
      exact (hγ k i)
  -- Now assemble.
  rw [hpsi_sq]
  have hpos : (0 : ℝ) ≤ (2 / (2 ^ n : ℝ))^2 := by positivity
  have hprod_eq :
      (∏ i ∈ Finset.univ.erase k, Real.cos (2 * edge γ i k)) =
      (∏ i ∈ Finset.univ.erase k, Real.cos (2 * γ i k)) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [hedge i hi]
  calc (2 / (2 ^ n : ℝ))^2 * Complex.normSq (∑ η : IxType, g η)
      ≤ (2 / (2 ^ n : ℝ))^2 * ((2^(n-1) : ℝ) * ∑ η : IxType, (Real.cos (L η))^2) := by
        gcongr
    _ = (2 / (2 ^ n : ℝ)) * (∑ η : IxType, (Real.cos (L η))^2) := by
        rw [hpow]
        have h2pos : (2 : ℝ)^(n - 1) > 0 := by positivity
        field_simp
    _ = (2 / (2 ^ n : ℝ)) *
          (∑ η : IxType, ((1/2 : ℝ) + (1/2) * Real.cos (2 * L η))) := by
        congr 1
        refine Finset.sum_congr rfl (fun η _ => hcos_sq η)
    _ = (2 / (2 ^ n : ℝ)) *
          ((Fintype.card IxType : ℝ) * (1/2) +
            (1/2) * ∑ η : IxType, Real.cos (2 * L η)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
    _ = (2 / (2 ^ n : ℝ)) *
          ((2^(n-1) : ℝ) * (1/2) +
            (1/2) * ((2^(n-1) : ℝ) *
              ∏ i ∈ Finset.univ.erase k, Real.cos (2 * edge γ i k))) := by
        rw [hcard_ix, hsum_cos]
        push_cast
        ring
    _ = (1 : ℝ) / 2 + (1 : ℝ) / 2 *
          ∏ i ∈ Finset.univ.erase k, Real.cos (2 * edge γ i k) := by
        rw [hpow]
        have h2pos : (2 : ℝ)^(n - 1) > 0 := by positivity
        field_simp
    _ = (1 : ℝ) / 2 + (1 : ℝ) / 2 *
          ∏ i ∈ Finset.univ.erase k, Real.cos (2 * γ i k) := by
        rw [hprod_eq]

end LeaHadamard.Hadamard
