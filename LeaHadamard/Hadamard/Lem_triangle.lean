import Mathlib

open Finset
open scoped BigOperators

namespace LeaHadamard.Hadamard

/-! ## Triangle formula

For $\lambda : \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}$ and Rademacher
signs $\xi : \mathrm{Fin}\,n \to \{-1, +1\}$ (encoded as `Bool`), define
$X_\lambda(\xi) := \sum_{i<j} \lambda(i,j)\,\xi_i\,\xi_j$ and
$T(\lambda) := \sum_{i<j<k} \lambda(i,j)\,\lambda(i,k)\,\lambda(j,k)$.

Then $T(\lambda) = \tfrac16 \mathbb{E}[X_\lambda^3]$.
-/

/-- Rademacher sign attached to a boolean: `true ↦ 1`, `false ↦ -1`. -/
private noncomputable def sgn (b : Bool) : ℝ := if b then 1 else -1

private lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

/-- The Rademacher quadratic form `X_λ(ξ) = ∑_{i<j} λ(i,j) · ξ_i · ξ_j`. -/
private noncomputable def X {n : ℕ} (lam : Fin n → Fin n → ℝ) (ξ : Fin n → Bool) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
    lam p.1 p.2 * sgn (ξ p.1) * sgn (ξ p.2)

/-- The cubic functional `T(λ) = ∑_{i<j<k} λ(i,j)·λ(i,k)·λ(j,k)`. -/
private noncomputable def T {n : ℕ} (lam : Fin n → Fin n → ℝ) : ℝ :=
  ∑ t ∈ (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
        (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2),
    lam t.1 t.2.1 * lam t.1 t.2.2 * lam t.2.1 t.2.2

/-! ### Rademacher moment lemma -/

/-- Average of a product of `sgn ξ` along an index function: factorization formula. -/
private lemma sum_prod_sgn_pow {n : ℕ} (g : Fin n → ℕ) :
    (∑ ξ : Fin n → Bool, ∏ i : Fin n, sgn (ξ i) ^ g i) =
      ∏ i : Fin n, (1 + (-1 : ℝ) ^ g i) := by
  -- Use prod_sum exchange.
  have key : ∀ i : Fin n, (1 : ℝ) + (-1 : ℝ) ^ g i = ∑ b : Bool, sgn b ^ g i := by
    intro i
    rw [Fintype.sum_bool]
    simp [sgn]
  simp_rw [key]
  rw [Fintype.prod_sum]

/-- Average of `∏_a sgn (ξ (f a))` over Rademacher signs, factored as a product
over `Fin n` of `1 + (-1)^{multiplicity}`. -/
private lemma sum_prod_sgn_along {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin n) :
    (∑ ξ : Fin n → Bool, ∏ a : ι, sgn (ξ (f a))) =
      ∏ i : Fin n,
        (1 + (-1 : ℝ) ^ ((Finset.univ : Finset ι).filter (fun a => f a = i)).card) := by
  -- Rewrite the inner product fiber-wise.
  have key : ∀ ξ : Fin n → Bool,
      (∏ a : ι, sgn (ξ (f a))) =
        ∏ i : Fin n,
          sgn (ξ i) ^ ((Finset.univ : Finset ι).filter (fun a => f a = i)).card := by
    intro ξ
    rw [← Finset.prod_fiberwise_of_maps_to (g := f) (s := (Finset.univ : Finset ι))
          (t := (Finset.univ : Finset (Fin n))) (fun a _ => Finset.mem_univ _)
          (f := fun a => sgn (ξ (f a)))]
    refine Finset.prod_congr rfl ?_
    intro i _
    have hcong : ∀ a ∈ (Finset.univ : Finset ι).filter (fun a => f a = i),
        sgn (ξ (f a)) = sgn (ξ i) := by
      intro a ha
      have : f a = i := (Finset.mem_filter.mp ha).2
      rw [this]
    rw [Finset.prod_congr rfl hcong]
    rw [Finset.prod_const]
  simp_rw [key]
  exact sum_prod_sgn_pow _

/-- The product `∏_i (1 + (-1)^{g(i)})` is `2^n` if every `g(i)` is even, else `0`. -/
private lemma prod_one_add_neg_one_pow_eq {n : ℕ} (g : Fin n → ℕ) :
    (∏ i : Fin n, (1 + (-1 : ℝ) ^ g i)) =
      if ∀ i, Even (g i) then (2 : ℝ) ^ n else 0 := by
  by_cases hall : ∀ i, Even (g i)
  · rw [if_pos hall]
    have heq : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (1 + (-1 : ℝ) ^ g i) = 2 := by
      intro i _
      rw [(hall i).neg_one_pow]; norm_num
    rw [Finset.prod_congr rfl heq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨i, hi⟩ := hall
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Nat.not_even_iff_odd] at hi
    rw [hi.neg_one_pow]; ring

/-! ### Main theorem -/

/-- Pair set `P_n = {(i,j) : i < j}` viewed as a `Finset`. -/
private noncomputable def Pset (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)

/-- Triple set `T_n = {(i,j,k) : i < j ∧ j < k}` viewed as a `Finset`. -/
private noncomputable def Tset (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

/-- The 6 index slots of a triple of pairs `(p, q, r)`. -/
private def slot {n : ℕ} (p q r : Fin n × Fin n) : Fin 6 → Fin n
  | ⟨0, _⟩ => p.1
  | ⟨1, _⟩ => p.2
  | ⟨2, _⟩ => q.1
  | ⟨3, _⟩ => q.2
  | ⟨4, _⟩ => r.1
  | ⟨5, _⟩ => r.2
  | ⟨_+6, h⟩ => absurd h (by omega)

/-- Multiplicity of an index `i : Fin n` in a triple of pairs. -/
private noncomputable def mult {n : ℕ} (p q r : Fin n × Fin n) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).filter (fun a => slot p q r a = i)).card

/-- Triple is "balanced" (all multiplicities even). -/
private def Balanced {n : ℕ} (p q r : Fin n × Fin n) : Prop :=
  ∀ i : Fin n, Even (mult p q r i)

noncomputable instance {n : ℕ} (p q r : Fin n × Fin n) :
    Decidable (Balanced p q r) := Classical.dec _

/-- The 6 orderings of triangle pairs as a function `Fin 6 → P_n^3`. For
`(i,j,k)` with `i < j < k`, gives the 6 permutations of
`((i,j), (i,k), (j,k))`. -/
private def order {n : ℕ} (t : Fin n × Fin n × Fin n) :
    Fin 6 → (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)
  | ⟨0, _⟩ => ((t.1, t.2.1), (t.1, t.2.2), (t.2.1, t.2.2))
  | ⟨1, _⟩ => ((t.1, t.2.1), (t.2.1, t.2.2), (t.1, t.2.2))
  | ⟨2, _⟩ => ((t.1, t.2.2), (t.1, t.2.1), (t.2.1, t.2.2))
  | ⟨3, _⟩ => ((t.1, t.2.2), (t.2.1, t.2.2), (t.1, t.2.1))
  | ⟨4, _⟩ => ((t.2.1, t.2.2), (t.1, t.2.1), (t.1, t.2.2))
  | ⟨5, _⟩ => ((t.2.1, t.2.2), (t.1, t.2.2), (t.1, t.2.1))
  | ⟨_+6, h⟩ => absurd h (by omega)

-- Auxiliary: product `∏ a : Fin 6, sgn (ξ (slot p q r a))` equals
-- the 6-fold product `sgn(ξ p₁) · sgn(ξ p₂) · sgn(ξ q₁) · sgn(ξ q₂) · sgn(ξ r₁) · sgn(ξ r₂)`.
private lemma prod_slot_eq {n : ℕ} (p q r : Fin n × Fin n) (ξ : Fin n → Bool) :
    (∏ a : Fin 6, sgn (ξ (slot p q r a))) =
      sgn (ξ p.1) * sgn (ξ p.2) * sgn (ξ q.1) * sgn (ξ q.2)
        * sgn (ξ r.1) * sgn (ξ r.2) := by
  simp [Fin.prod_univ_six, slot, mul_assoc]

/-- Step 1: expansion of `∑_ξ X^3` as a triple sum. -/
private lemma sum_X_cubed_expand {n : ℕ} (lam : Fin n → Fin n → ℝ) :
    (∑ ξ : Fin n → Bool, (X lam ξ) ^ 3) =
      ∑ p ∈ Pset n, ∑ q ∈ Pset n, ∑ r ∈ Pset n,
        lam p.1 p.2 * lam q.1 q.2 * lam r.1 r.2 *
          ∑ ξ : Fin n → Bool, ∏ a : Fin 6, sgn (ξ (slot p q r a)) := by
  -- Pointwise expansion of `(X lam ξ)^3`.
  have hX3 : ∀ ξ : Fin n → Bool, (X lam ξ) ^ 3 =
      ∑ p ∈ Pset n, ∑ q ∈ Pset n, ∑ r ∈ Pset n,
        lam p.1 p.2 * lam q.1 q.2 * lam r.1 r.2 *
          ∏ a : Fin 6, sgn (ξ (slot p q r a)) := by
    intro ξ
    have hXcube : (X lam ξ) ^ 3 = X lam ξ * X lam ξ * X lam ξ := by ring
    rw [hXcube]
    -- Expand X as a sum over Pset, three times.
    have hXdef : X lam ξ =
        ∑ p ∈ Pset n, lam p.1 p.2 * sgn (ξ p.1) * sgn (ξ p.2) := rfl
    rw [hXdef, Finset.sum_mul_sum]
    rw [show (∑ x ∈ Pset n, ∑ y ∈ Pset n,
              (lam x.1 x.2 * sgn (ξ x.1) * sgn (ξ x.2)) *
              (lam y.1 y.2 * sgn (ξ y.1) * sgn (ξ y.2))) *
            (∑ r ∈ Pset n, lam r.1 r.2 * sgn (ξ r.1) * sgn (ξ r.2)) =
            ∑ p ∈ Pset n, ∑ q ∈ Pset n, ∑ r ∈ Pset n,
              ((lam p.1 p.2 * sgn (ξ p.1) * sgn (ξ p.2)) *
               (lam q.1 q.2 * sgn (ξ q.1) * sgn (ξ q.2))) *
              (lam r.1 r.2 * sgn (ξ r.1) * sgn (ξ r.2)) from ?_]
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      refine Finset.sum_congr rfl (fun q _ => ?_)
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [prod_slot_eq]; ring
    · simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [hX3]
  -- Swap the outer sum-over-ξ inward through the triple sum.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro r _
  exact (Finset.mul_sum _ _ _).symm

/-- Step 2: the inner Rademacher sum is `2^n` if balanced, `0` otherwise. -/
private lemma inner_sgn_sum {n : ℕ} (p q r : Fin n × Fin n) :
    (∑ ξ : Fin n → Bool, ∏ a : Fin 6, sgn (ξ (slot p q r a))) =
      if Balanced p q r then (2 : ℝ) ^ n else 0 := by
  rw [sum_prod_sgn_along (slot p q r), prod_one_add_neg_one_pow_eq]
  congr 1

/-- Step 3: `∑_ξ X^3 = 2^n · ∑_{(p,q,r) balanced} λ_p λ_q λ_r`. -/
private lemma sum_X_cubed_eq {n : ℕ} (lam : Fin n → Fin n → ℝ) :
    (∑ ξ : Fin n → Bool, (X lam ξ) ^ 3) =
      (2 : ℝ) ^ n *
        ∑ p ∈ Pset n, ∑ q ∈ Pset n, ∑ r ∈ Pset n,
          (if Balanced p q r then lam p.1 p.2 * lam q.1 q.2 * lam r.1 r.2 else 0) := by
  rw [sum_X_cubed_expand lam]
  simp_rw [inner_sgn_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases h : Balanced p q r
  · simp [h]; ring
  · simp [h]

/-! ### Combinatorial step: balanced triples = 6 orderings of triangles -/

/-- Helper: multiplicity of `x` in a list of 6 elements `(a₀,...,a₅)`. -/
private def mult6 {n : ℕ} (a₀ a₁ a₂ a₃ a₄ a₅ x : Fin n) : ℕ :=
  (if a₀ = x then 1 else 0) + (if a₁ = x then 1 else 0) +
  (if a₂ = x then 1 else 0) + (if a₃ = x then 1 else 0) +
  (if a₄ = x then 1 else 0) + (if a₅ = x then 1 else 0)

private lemma mult_eq_mult6 {n : ℕ} (p q r : Fin n × Fin n) (x : Fin n) :
    mult p q r x = mult6 p.1 p.2 q.1 q.2 r.1 r.2 x := by
  unfold mult mult6
  rw [show (Finset.univ : Finset (Fin 6)) =
        {(0 : Fin 6), 1, 2, 3, 4, 5} from by decide]
  simp only [slot, Finset.filter_insert, Finset.filter_singleton, Fin.isValue,
             apply_ite (Finset.card)]
  split_ifs <;> decide

/-- For a triangle `(i,j,k)` with `i < j < k`, every ordering is balanced. -/
private lemma order_balanced {n : ℕ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (κ : Fin 6) :
    Balanced (order (i, j, k) κ).1 (order (i, j, k) κ).2.1
      (order (i, j, k) κ).2.2 := by
  have hij' : i ≠ j := ne_of_lt hij
  have hjk' : j ≠ k := ne_of_lt hjk
  have hik' : i ≠ k := ne_of_lt (lt_trans hij hjk)
  intro x
  rw [mult_eq_mult6]
  fin_cases κ <;>
    · simp only [order, mult6]
      by_cases hxi : x = i
      · subst hxi
        simp [hij'.symm, hik'.symm]
      · by_cases hxj : x = j
        · subst hxj
          simp [hij', hjk'.symm]
        · by_cases hxk : x = k
          · subst hxk
            simp [hik', hjk']
          · simp [Ne.symm hxi, Ne.symm hxj, Ne.symm hxk]

/-- All three pairs of an ordering of a triangle are in `Pset`. -/
private lemma order_pairs_in_Pset {n : ℕ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (κ : Fin 6) :
    (order (i, j, k) κ).1 ∈ Pset n ∧
    (order (i, j, k) κ).2.1 ∈ Pset n ∧
    (order (i, j, k) κ).2.2 ∈ Pset n := by
  have hik : i < k := lt_trans hij hjk
  unfold Pset
  fin_cases κ <;>
    · refine ⟨?_, ?_, ?_⟩ <;>
        · simp [order, hij, hjk, hik]

/-- The product `λ` evaluated on any ordering of a triangle yields the same value. -/
private lemma lam_prod_order {n : ℕ} (lam : Fin n → Fin n → ℝ)
    {i j k : Fin n} (κ : Fin 6) :
    lam (order (i, j, k) κ).1.1 (order (i, j, k) κ).1.2 *
      lam (order (i, j, k) κ).2.1.1 (order (i, j, k) κ).2.1.2 *
      lam (order (i, j, k) κ).2.2.1 (order (i, j, k) κ).2.2.2 =
    lam i j * lam i k * lam j k := by
  fin_cases κ <;>
    first | (simp only [order]; ring) | (simp [order])

/-- Source `Finset` for the bijection: triangles times 6 orderings. -/
private noncomputable def Source (n : ℕ) :=
  Tset n ×ˢ (Finset.univ : Finset (Fin 6))

/-- Target `Finset` for the bijection: balanced ordered triples in `P_n^3`. -/
private noncomputable def Target (n : ℕ) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)) :=
  (Pset n ×ˢ Pset n ×ˢ Pset n).filter
    (fun s => ∀ i : Fin n, Even (mult s.1 s.2.1 s.2.2 i))

-- Auxiliary calculation lemmas; we use them in the surjection step.
private lemma even_two : Even (2 : ℕ) := ⟨1, rfl⟩
private lemma even_zero : Even (0 : ℕ) := ⟨0, rfl⟩

/-- Helper: in any pair (a, b) with a < b, slots a, b of x give count ≤ 1. -/
private lemma indicator_pair_le {n : ℕ} (a b x : Fin n) (hab : a < b) :
    (if a = x then 1 else 0) + (if b = x then 1 else 0) ≤ (1 : ℕ) := by
  have hne : a ≠ b := ne_of_lt hab
  by_cases h1 : a = x
  · have h2 : b ≠ x := h1 ▸ hne.symm
    simp [h1, h2]
  · split_ifs <;> omega

/-- For Balanced `(p,q,r)`, the indices form 3 distinct values with multiplicity
2, and the 3 pairs are exactly the 3 edges of a triangle, traversed in some
order. -/
private lemma balanced_is_order {n : ℕ}
    (p q r : Fin n × Fin n)
    (hp : p ∈ Pset n) (hq : q ∈ Pset n) (hr : r ∈ Pset n)
    (hbal : ∀ i : Fin n, Even (mult p q r i)) :
    ∃ t ∈ Tset n, ∃ κ : Fin 6, order t κ = (p, q, r) := by
  have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hqlt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
  have hrlt : r.1 < r.2 := (Finset.mem_filter.mp hr).2
  set i := p.1 with hi_def
  set j := p.2 with hj_def
  have hp_eq : p = (i, j) := by ext <;> rfl
  have hp_ne : i ≠ j := ne_of_lt hij
  have hji : j ≠ i := hp_ne.symm
  -- Helper: each pair's contribution to mult of x is at most 1.
  have hpb_p := indicator_pair_le i j
  have hpb_q := indicator_pair_le q.1 q.2
  have hpb_r := indicator_pair_le r.1 r.2
  -- Multiplicity facts via mult6.
  have hbal' : ∀ x : Fin n, Even (mult6 i j q.1 q.2 r.1 r.2 x) := by
    intro x
    have := hbal x
    rwa [mult_eq_mult6] at this
  have mult_le3 : ∀ x : Fin n, mult6 i j q.1 q.2 r.1 r.2 x ≤ 3 := by
    intro x
    have h1 := hpb_p x hij
    have h2 := hpb_q x hqlt
    have h3 := hpb_r x hrlt
    unfold mult6; omega
  have mult_in : ∀ x : Fin n,
      mult6 i j q.1 q.2 r.1 r.2 x = 0 ∨ mult6 i j q.1 q.2 r.1 r.2 x = 2 := by
    intro x
    have hle := mult_le3 x
    obtain ⟨m, hm⟩ := hbal' x
    have : m ≤ 1 := by omega
    interval_cases m <;> omega
  -- Compute multiplicity of i and j: each ≥ 1, even ⇒ ≥ 2, ≤ 3 ⇒ = 2.
  have mult_i : mult6 i j q.1 q.2 r.1 r.2 i = 2 := by
    have h := mult_in i
    have : mult6 i j q.1 q.2 r.1 r.2 i ≥ 1 := by
      unfold mult6; rw [if_pos rfl]; omega
    omega
  have mult_j : mult6 i j q.1 q.2 r.1 r.2 j = 2 := by
    have h := mult_in j
    have : mult6 i j q.1 q.2 r.1 r.2 j ≥ 1 := by
      unfold mult6; rw [if_neg hp_ne, if_pos rfl]; omega
    omega
  -- Count of i in (q,r) slots = 1; count of j in (q,r) slots = 1.
  have count_i :
      (if q.1 = i then 1 else 0) + (if q.2 = i then 1 else 0) +
      (if r.1 = i then 1 else 0) + (if r.2 = i then 1 else 0) = (1 : ℕ) := by
    have := mult_i
    unfold mult6 at this
    rw [if_pos rfl, if_neg hji] at this; omega
  have count_j :
      (if q.1 = j then 1 else 0) + (if q.2 = j then 1 else 0) +
      (if r.1 = j then 1 else 0) + (if r.2 = j then 1 else 0) = (1 : ℕ) := by
    have := mult_j
    unfold mult6 at this
    rw [if_neg hp_ne, if_pos rfl] at this; omega
  -- Pair bounds at i and j: each pair (q or r) has at most 1 slot = i or j.
  have hq_at_i := hpb_q i hqlt
  have hr_at_i := hpb_r i hrlt
  have hq_at_j := hpb_q j hqlt
  have hr_at_j := hpb_r j hrlt
  -- Determine: i appears in exactly one of {q, r} slots; same for j.
  -- Furthermore, i and j are NOT in the same pair (else r is (k,k)).
  -- Case analysis on which slot has i.
  -- Determine which slot has i; given count_i = 1 and pair_bound, exactly one slot.
  have h_i_loc : (q.1 = i ∧ q.2 ≠ i ∧ r.1 ≠ i ∧ r.2 ≠ i) ∨
                 (q.1 ≠ i ∧ q.2 = i ∧ r.1 ≠ i ∧ r.2 ≠ i) ∨
                 (q.1 ≠ i ∧ q.2 ≠ i ∧ r.1 = i ∧ r.2 ≠ i) ∨
                 (q.1 ≠ i ∧ q.2 ≠ i ∧ r.1 ≠ i ∧ r.2 = i) := by
    by_cases hq1 : q.1 = i
    · by_cases hq2 : q.2 = i
      · exfalso
        have : q.1 = q.2 := hq1.trans hq2.symm
        exact (ne_of_lt hqlt) this
      · refine Or.inl ⟨hq1, hq2, ?_, ?_⟩
        · intro h; rw [if_pos hq1, if_neg hq2, if_pos h] at count_i; omega
        · intro h
          rw [if_pos hq1, if_neg hq2] at count_i
          have hr1 : r.1 ≠ i := by
            intro h'; rw [if_pos h', if_pos h] at count_i; omega
          rw [if_neg hr1, if_pos h] at count_i; omega
    · by_cases hq2 : q.2 = i
      · refine Or.inr (Or.inl ⟨hq1, hq2, ?_, ?_⟩)
        · intro h; rw [if_neg hq1, if_pos hq2, if_pos h] at count_i; omega
        · intro h
          rw [if_neg hq1, if_pos hq2] at count_i
          have hr1 : r.1 ≠ i := by
            intro h'; rw [if_pos h', if_pos h] at count_i; omega
          rw [if_neg hr1, if_pos h] at count_i; omega
      · by_cases hr1 : r.1 = i
        · refine Or.inr (Or.inr (Or.inl ⟨hq1, hq2, hr1, ?_⟩))
          intro h
          rw [if_neg hq1, if_neg hq2, if_pos hr1, if_pos h] at count_i; omega
        · by_cases hr2 : r.2 = i
          · exact Or.inr (Or.inr (Or.inr ⟨hq1, hq2, hr1, hr2⟩))
          · exfalso
            rw [if_neg hq1, if_neg hq2, if_neg hr1, if_neg hr2] at count_i; omega
  have h_j_loc : (q.1 = j ∧ q.2 ≠ j ∧ r.1 ≠ j ∧ r.2 ≠ j) ∨
                 (q.1 ≠ j ∧ q.2 = j ∧ r.1 ≠ j ∧ r.2 ≠ j) ∨
                 (q.1 ≠ j ∧ q.2 ≠ j ∧ r.1 = j ∧ r.2 ≠ j) ∨
                 (q.1 ≠ j ∧ q.2 ≠ j ∧ r.1 ≠ j ∧ r.2 = j) := by
    by_cases hq1 : q.1 = j
    · by_cases hq2 : q.2 = j
      · exfalso
        have : q.1 = q.2 := hq1.trans hq2.symm
        exact (ne_of_lt hqlt) this
      · refine Or.inl ⟨hq1, hq2, ?_, ?_⟩
        · intro h; rw [if_pos hq1, if_neg hq2, if_pos h] at count_j; omega
        · intro h
          rw [if_pos hq1, if_neg hq2] at count_j
          have hr1 : r.1 ≠ j := by
            intro h'; rw [if_pos h', if_pos h] at count_j; omega
          rw [if_neg hr1, if_pos h] at count_j; omega
    · by_cases hq2 : q.2 = j
      · refine Or.inr (Or.inl ⟨hq1, hq2, ?_, ?_⟩)
        · intro h; rw [if_neg hq1, if_pos hq2, if_pos h] at count_j; omega
        · intro h
          rw [if_neg hq1, if_pos hq2] at count_j
          have hr1 : r.1 ≠ j := by
            intro h'; rw [if_pos h', if_pos h] at count_j; omega
          rw [if_neg hr1, if_pos h] at count_j; omega
      · by_cases hr1 : r.1 = j
        · refine Or.inr (Or.inr (Or.inl ⟨hq1, hq2, hr1, ?_⟩))
          intro h
          rw [if_neg hq1, if_neg hq2, if_pos hr1, if_pos h] at count_j; omega
        · by_cases hr2 : r.2 = j
          · exact Or.inr (Or.inr (Or.inr ⟨hq1, hq2, hr1, hr2⟩))
          · exfalso
            rw [if_neg hq1, if_neg hq2, if_neg hr1, if_neg hr2] at count_j; omega
  -- Now do the 16 case bash. We'll discharge contradictions and provide witnesses.
  -- Helper: mult of any x must be even, so if mult ≥ 1 then mult ≥ 2.
  have mult_ge_two_of_pos : ∀ x : Fin n,
      mult6 i j q.1 q.2 r.1 r.2 x ≥ 1 → mult6 i j q.1 q.2 r.1 r.2 x = 2 := by
    intro x hpos
    rcases mult_in x with h | h
    · omega
    · exact h
  -- Combine h_i_loc and h_j_loc.
  rcases h_i_loc with ⟨hi1, hi2, hi3, hi4⟩ | ⟨hi1, hi2, hi3, hi4⟩ |
                     ⟨hi1, hi2, hi3, hi4⟩ | ⟨hi1, hi2, hi3, hi4⟩ <;>
  rcases h_j_loc with ⟨hj1, hj2, hj3, hj4⟩ | ⟨hj1, hj2, hj3, hj4⟩ |
                     ⟨hj1, hj2, hj3, hj4⟩ | ⟨hj1, hj2, hj3, hj4⟩
  -- Case (q.1=i, q.1=j): contradicts i ≠ j.
  · exact absurd (hi1.symm.trans hj1) hp_ne
  -- Case (q.1=i, q.2=j): q = (i, j). Then r has neither i nor j. mult of r.1 odd → contradiction.
  · exfalso
    have hi_ne_r1 : i ≠ r.1 := Ne.symm hi3
    have hj_ne_r1 : j ≠ r.1 := Ne.symm hj3
    have hq1_ne_r1 : q.1 ≠ r.1 := hi1.symm ▸ hi_ne_r1
    have hq2_ne_r1 : q.2 ≠ r.1 := hj2.symm ▸ hj_ne_r1
    have hr2_ne_r1 : r.2 ≠ r.1 := (ne_of_lt hrlt).symm
    have h := mult_in r.1
    unfold mult6 at h
    simp only [if_neg hi_ne_r1, if_neg hj_ne_r1, if_neg hq1_ne_r1,
               if_neg hq2_ne_r1, if_neg hr2_ne_r1] at h
    simp at h
  -- Case (q.1=i, r.1=j): triangle (i, j, k) with k = q.2 (= r.2 by mult).
  · -- Show k := q.2 = r.2.
    -- First, k ≠ i (since q.2 ≠ i), k ≠ j (we'll derive).
    have hk_ne_i : q.2 ≠ i := hi2
    -- q.2 ≠ j: if q.2 = j then q = (i,j), then r.1 = j = q.2, but mult of j becomes ≥ 3 (odd)? Actually more directly:
    -- if q.2 = j, then since hj2: q.2 ≠ j, contradiction. So q.2 ≠ j.
    have hk_ne_j : q.2 ≠ j := hj2
    -- Mult of q.2: from mult_ge_two_of_pos. mult of q.2 = at least 1 (q.2 itself). Even ≥ 2.
    -- Specifically: count of q.2 in {p,q,r}: from p (= [i=q.2] + [j=q.2] = 0+0 = 0), from q ([q.1=q.2]+[q.2=q.2] = 0 + 1 = 1), from r.
    -- Mult = 1 + (count in r). Must be 2, so count in r = 1.
    have mult_q2 : mult6 i j q.1 q.2 r.1 r.2 q.2 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have hq2q2 : (if q.2 = q.2 then 1 else 0 : ℕ) = 1 := by simp
      omega
    -- From mult_q2 = 2: subtract 1 contribution from q.2's own slot.
    have count_q2_in_r :
        (if r.1 = q.2 then 1 else 0) + (if r.2 = q.2 then 1 else 0) = (1 : ℕ) := by
      have := mult_q2
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq1_ne_q2 : q.1 ≠ q.2 := ne_of_lt hqlt
      rw [if_neg hq1_ne_q2] at this
      simp at this
      omega
    -- r.1 = j ≠ q.2 (by hk_ne_j applied: q.2 ≠ j ↔ r.1 ≠ q.2 since r.1 = j).
    have hr1_ne_q2 : r.1 ≠ q.2 := by rw [hj3]; exact Ne.symm hk_ne_j
    -- So r.2 = q.2.
    have hr2_eq_q2 : r.2 = q.2 := by
      rw [if_neg hr1_ne_q2] at count_q2_in_r
      by_contra h; rw [if_neg h] at count_q2_in_r; omega
    -- Triangle: i < j < q.2 (since j = r.1 < r.2 = q.2).
    have hij_lt_q2 : j < q.2 := by rw [← hr2_eq_q2]; rw [hj3] at hrlt; exact hrlt
    -- Provide t = (i, j, q.2), κ = 0.
    refine ⟨(i, j, q.2), ?_, 0, ?_⟩
    · simp [Tset, hij, hij_lt_q2]
    · -- order (i,j,q.2) 0 = ((i,j), (i,q.2), (j,q.2)).
      -- Need to show this = (p, q, r).
      -- p = (i,j) = (p.1, p.2) ✓ by definition.
      -- q = (q.1, q.2) = (i, q.2) since q.1 = i = hi1. ✓
      -- r = (r.1, r.2) = (j, q.2) since r.1 = j = hj3, r.2 = q.2 = hr2_eq_q2. ✓
      simp only [order]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (Prod.ext hi_def hj_def).symm
      · exact Prod.ext hi1.symm rfl
      · exact Prod.ext hj3.symm hr2_eq_q2.symm
  -- Case (q.1=i, r.2=j): triangle (i, j, ...). Need to find k.
  · -- q.1 = i, q.2 = ?, r.2 = j, r.1 ≠ j (so r.1 = ? something).
    -- mult of q.2: from p (0), from q (1), from r (?). Even ⇒ contribution from r = 1.
    -- r.1, r.2 candidates: r.2 = j, but q.2 ≠ j (hj2). So q.2 must equal r.1.
    have hk_ne_i : q.2 ≠ i := hi2
    have hk_ne_j : q.2 ≠ j := hj2
    have mult_q2 : mult6 i j q.1 q.2 r.1 r.2 q.2 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have hq2q2 : (if q.2 = q.2 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q2_in_r :
        (if r.1 = q.2 then 1 else 0) + (if r.2 = q.2 then 1 else 0) = (1 : ℕ) := by
      have := mult_q2
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq1_ne_q2 : q.1 ≠ q.2 := ne_of_lt hqlt
      rw [if_neg hq1_ne_q2] at this
      simp at this
      omega
    have hr2_ne_q2 : r.2 ≠ q.2 := by rw [hj4]; exact Ne.symm hk_ne_j
    have hr1_eq_q2 : r.1 = q.2 := by
      rw [if_neg hr2_ne_q2] at count_q2_in_r
      by_contra h; rw [if_neg h] at count_q2_in_r; omega
    -- Triangle: i, j, q.2. Sort. q.2 < r.2 = j, so q.2 < j. i < q.2: q.1 = i < q.2.
    have hqr : q.2 < j := by
      have := hrlt
      rw [hr1_eq_q2, hj4] at this
      exact this
    have hi_lt_q2 : i < q.2 := by rw [← hi1]; exact hqlt
    -- Triangle (i, q.2, j). Use κ = 2: ((a, c), (a, b), (b, c)) with a=i, b=q.2, c=j.
    refine ⟨(i, q.2, j), ?_, 2, ?_⟩
    · simp [Tset, hi_lt_q2, hqr]
    · simp only [order]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (Prod.ext hi_def hj_def).symm
      · exact Prod.ext hi1.symm rfl
      · exact Prod.ext hr1_eq_q2.symm hj4.symm
  -- Case (q.2=i, q.1=j): contradicts hqlt (j < i but i < j).
  · exfalso
    have : j < i := hj1.symm ▸ hi2.symm ▸ hqlt
    exact (lt_asymm hij) this
  -- Case (q.2=i, q.2=j): contradicts hp_ne.
  · exact absurd (hi2.symm.trans hj2) hp_ne
  -- Case (q.2=i, r.1=j): triangle. k = q.1.
  · -- q.1 ≠ i (hi1), q.1 ≠ j (hj1).
    have hk_ne_i : q.1 ≠ i := hi1
    have hk_ne_j : q.1 ≠ j := hj1
    have mult_q1 : mult6 i j q.1 q.2 r.1 r.2 q.1 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have hq1q1 : (if q.1 = q.1 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q1_in_r :
        (if r.1 = q.1 then 1 else 0) + (if r.2 = q.1 then 1 else 0) = (1 : ℕ) := by
      have := mult_q1
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq2_ne_q1 : q.2 ≠ q.1 := (ne_of_lt hqlt).symm
      rw [if_neg hq2_ne_q1] at this
      simp at this
      omega
    have hr1_ne_q1 : r.1 ≠ q.1 := by rw [hj3]; exact Ne.symm hk_ne_j
    have hr2_eq_q1 : r.2 = q.1 := by
      rw [if_neg hr1_ne_q1] at count_q1_in_r
      by_contra h; rw [if_neg h] at count_q1_in_r; omega
    -- Triangle (q.1, ?, ?). q.1 < q.2 = i. So q.1 < i. And j < q.1 from hrlt + r-eqs.
    -- So j < q.1 < i. But i < j! Contradiction.
    exfalso
    have h1 : q.1 < i := by have := hqlt; rw [hi2] at this; exact this
    have h2 : j < q.1 := by have := hrlt; rw [hj3, hr2_eq_q1] at this; exact this
    -- j < q.1 < i < j → false
    exact lt_irrefl j (lt_trans h2 (lt_trans h1 hij))
  -- Case (q.2=i, r.2=j): triangle.
  · -- q.1 = k. Similar to previous, find r.1 = q.1.
    have hk_ne_i : q.1 ≠ i := hi1
    have hk_ne_j : q.1 ≠ j := hj1
    have mult_q1 : mult6 i j q.1 q.2 r.1 r.2 q.1 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have hq1q1 : (if q.1 = q.1 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q1_in_r :
        (if r.1 = q.1 then 1 else 0) + (if r.2 = q.1 then 1 else 0) = (1 : ℕ) := by
      have := mult_q1
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq2_ne_q1 : q.2 ≠ q.1 := (ne_of_lt hqlt).symm
      rw [if_neg hq2_ne_q1] at this
      simp at this
      omega
    have hr2_ne_q1 : r.2 ≠ q.1 := by rw [hj4]; exact Ne.symm hk_ne_j
    have hr1_eq_q1 : r.1 = q.1 := by
      rw [if_neg hr2_ne_q1] at count_q1_in_r
      by_contra h; rw [if_neg h] at count_q1_in_r; omega
    -- q.1 < q.2 = i, so q.1 < i. r.1 = q.1, r.2 = j, q.1 < j (need).
    have hq1_lt_i : q.1 < i := hi2 ▸ hqlt
    have hq1_lt_j : q.1 < j := lt_trans hq1_lt_i hij
    -- Triangle (q.1, i, j). κ = ?
    -- order(q.1, i, j) values:
    -- σ_4: ((i, j), (q.1, i), (q.1, j)) — p = (i,j) ✓, q = (q.1, i) — need q.2 = i ✓, q.1 = q.1 ✓ ✓.
    -- r = (q.1, j) — need r.1 = q.1 ✓, r.2 = j ✓ ✓.
    refine ⟨(q.1, i, j), ?_, 4, ?_⟩
    · simp [Tset, hq1_lt_i, hij]
    · simp only [order]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (Prod.ext hi_def hj_def).symm
      · exact Prod.ext rfl hi2.symm
      · exact Prod.ext hr1_eq_q1.symm hj4.symm
  -- Case (r.1=i, q.1=j): triangle. k = q.2 (= r.2).
  · have hk_ne_i : q.2 ≠ i := hi2
    have hk_ne_j : q.2 ≠ j := hj2
    have mult_q2 : mult6 i j q.1 q.2 r.1 r.2 q.2 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have : (if q.2 = q.2 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q2_in_r :
        (if r.1 = q.2 then 1 else 0) + (if r.2 = q.2 then 1 else 0) = (1 : ℕ) := by
      have := mult_q2
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq1_ne_q2 : q.1 ≠ q.2 := ne_of_lt hqlt
      rw [if_neg hq1_ne_q2] at this
      simp at this
      omega
    have hr1_ne_q2 : r.1 ≠ q.2 := by rw [hi3]; exact Ne.symm hk_ne_i
    have hr2_eq_q2 : r.2 = q.2 := by
      rw [if_neg hr1_ne_q2] at count_q2_in_r
      by_contra h; rw [if_neg h] at count_q2_in_r; omega
    -- Triangle: i, j, q.2. q.1 = j < q.2. j < q.2.
    have hj_lt_q2 : j < q.2 := hj1 ▸ hqlt
    -- σ_1: ((a, b), (b, c), (a, c)) with a=i, b=j, c=q.2.
    -- p = (i, j) ✓, q = (j, q.2) — q.1 = j ✓, q.2 = q.2 ✓.
    -- r = (i, q.2) — r.1 = i ✓, r.2 = q.2 ✓.
    refine ⟨(i, j, q.2), ?_, 1, ?_⟩
    · simp [Tset, hij, hj_lt_q2]
    · simp only [order]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (Prod.ext hi_def hj_def).symm
      · exact Prod.ext hj1.symm rfl
      · exact Prod.ext hi3.symm hr2_eq_q2.symm
  -- Case (r.1=i, q.2=j): triangle. k = q.1.
  · have hk_ne_i : q.1 ≠ i := hi1
    have hk_ne_j : q.1 ≠ j := hj1
    have mult_q1 : mult6 i j q.1 q.2 r.1 r.2 q.1 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have : (if q.1 = q.1 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q1_in_r :
        (if r.1 = q.1 then 1 else 0) + (if r.2 = q.1 then 1 else 0) = (1 : ℕ) := by
      have := mult_q1
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq2_ne_q1 : q.2 ≠ q.1 := (ne_of_lt hqlt).symm
      rw [if_neg hq2_ne_q1] at this
      simp at this
      omega
    have hr1_ne_q1 : r.1 ≠ q.1 := by rw [hi3]; exact Ne.symm hk_ne_i
    have hr2_eq_q1 : r.2 = q.1 := by
      rw [if_neg hr1_ne_q1] at count_q1_in_r
      by_contra h; rw [if_neg h] at count_q1_in_r; omega
    -- Triangle: q.1, i, j. q.1 < q.2 = j. r.1 = i < r.2 = q.1, so i < q.1. But also q.1 < j.
    -- So order: i < q.1 < j. Triangle (i, q.1, j).
    have hi_lt_q1 : i < q.1 := hi3 ▸ hr2_eq_q1 ▸ hrlt
    have hq1_lt_j : q.1 < j := hj2 ▸ hqlt
    -- σ_3: ((a, c), (b, c), (a, b)) with a=i, b=q.1, c=j.
    -- p = (i, j) = (a, c) ✓, q = (q.1, j) = (b, c) — q.1 = q.1 ✓, q.2 = j ✓.
    -- r = (i, q.1) = (a, b) — r.1 = i ✓, r.2 = q.1 ✓.
    refine ⟨(i, q.1, j), ?_, 3, ?_⟩
    · simp [Tset, hi_lt_q1, hq1_lt_j]
    · simp only [order]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (Prod.ext hi_def hj_def).symm
      · exact Prod.ext rfl hj2.symm
      · exact Prod.ext hi3.symm hr2_eq_q1.symm
  -- Case (r.1=i, r.1=j): contradicts hp_ne.
  · exact absurd (hi3.symm.trans hj3) hp_ne
  -- Case (r.1=i, r.2=j): r = (i, j). Then q has neither i nor j, contradiction (similar to earlier).
  · exfalso
    have hi_ne_q1 : i ≠ q.1 := Ne.symm hi1
    have hj_ne_q1 : j ≠ q.1 := Ne.symm hj1
    have hr1_ne_q1 : r.1 ≠ q.1 := hi3.symm ▸ hi_ne_q1
    have hr2_ne_q1 : r.2 ≠ q.1 := hj4.symm ▸ hj_ne_q1
    have hq2_ne_q1 : q.2 ≠ q.1 := (ne_of_lt hqlt).symm
    have h := mult_in q.1
    unfold mult6 at h
    simp only [if_neg hi_ne_q1, if_neg hj_ne_q1, if_neg hq2_ne_q1,
               if_neg hr1_ne_q1, if_neg hr2_ne_q1] at h
    simp at h
  -- Case (r.2=i, q.1=j): triangle. k = q.2 = r.1.
  · have hk_ne_i : q.2 ≠ i := hi2
    have hk_ne_j : q.2 ≠ j := hj2
    have mult_q2 : mult6 i j q.1 q.2 r.1 r.2 q.2 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have : (if q.2 = q.2 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q2_in_r :
        (if r.1 = q.2 then 1 else 0) + (if r.2 = q.2 then 1 else 0) = (1 : ℕ) := by
      have := mult_q2
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq1_ne_q2 : q.1 ≠ q.2 := ne_of_lt hqlt
      rw [if_neg hq1_ne_q2] at this
      simp at this
      omega
    have hr2_ne_q2 : r.2 ≠ q.2 := by rw [hi4]; exact Ne.symm hk_ne_i
    have hr1_eq_q2 : r.1 = q.2 := by
      rw [if_neg hr2_ne_q2] at count_q2_in_r
      by_contra h; rw [if_neg h] at count_q2_in_r; omega
    -- Triangle: q.2 = r.1 < r.2 = i, so q.2 < i. j = q.1 < q.2, so j < q.2. So j < q.2 < i. But i < j! Contradiction.
    exfalso
    have hq2_lt_i : q.2 < i := hi4 ▸ hr1_eq_q2 ▸ hrlt
    have hj_lt_q2 : j < q.2 := hj1 ▸ hqlt
    exact lt_asymm hij (lt_trans hj_lt_q2 hq2_lt_i)
  -- Case (r.2=i, q.2=j): triangle.
  · have hk_ne_i : q.1 ≠ i := hi1
    have hk_ne_j : q.1 ≠ j := hj1
    have mult_q1 : mult6 i j q.1 q.2 r.1 r.2 q.1 = 2 := by
      apply mult_ge_two_of_pos
      unfold mult6
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm]
      have : (if q.1 = q.1 then 1 else 0 : ℕ) = 1 := by simp
      omega
    have count_q1_in_r :
        (if r.1 = q.1 then 1 else 0) + (if r.2 = q.1 then 1 else 0) = (1 : ℕ) := by
      have := mult_q1
      unfold mult6 at this
      rw [if_neg hk_ne_i.symm, if_neg hk_ne_j.symm] at this
      have hq2_ne_q1 : q.2 ≠ q.1 := (ne_of_lt hqlt).symm
      rw [if_neg hq2_ne_q1] at this
      simp at this
      omega
    have hr2_ne_q1 : r.2 ≠ q.1 := by rw [hi4]; exact Ne.symm hk_ne_i
    have hr1_eq_q1 : r.1 = q.1 := by
      rw [if_neg hr2_ne_q1] at count_q1_in_r
      by_contra h; rw [if_neg h] at count_q1_in_r; omega
    -- r.1 = q.1, r.2 = i, so q.1 < i. q.1 < q.2 = j, so q.1 < j. But also need q.1's relation.
    -- Actually, q.1 < i (from r.1 < r.2 = i and r.1 = q.1) and i < j gives q.1 < i < j.
    have hq1_lt_i : q.1 < i := hi4 ▸ hr1_eq_q1 ▸ hrlt
    -- Triangle (q.1, i, j). σ_5: ((b, c), (a, c), (a, b)) with a=q.1, b=i, c=j.
    -- p = (i, j) = (b, c) ✓.
    -- q = (q.1, j) = (a, c) — q.1 = q.1 ✓, q.2 = j ✓.
    -- r = (q.1, i) = (a, b) — r.1 = q.1 ✓, r.2 = i ✓.
    refine ⟨(q.1, i, j), ?_, 5, ?_⟩
    · simp [Tset, hq1_lt_i, hij]
    · simp only [order]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (Prod.ext hi_def hj_def).symm
      · exact Prod.ext rfl hj2.symm
      · exact Prod.ext hr1_eq_q1.symm hi4.symm
  -- Case (r.2=i, r.1=j): contradicts hrlt (j < i but i < j).
  · exfalso
    have : j < i := hj3.symm ▸ hi4.symm ▸ hrlt
    exact (lt_asymm hij) this
  -- Case (r.2=i, r.2=j): contradicts hp_ne.
  · exact absurd (hi4.symm.trans hj4) hp_ne

/-- The set of balanced triples. -/
private noncomputable def BalancedSet (n : ℕ) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)) :=
  (Pset n ×ˢ Pset n ×ˢ Pset n).filter
    (fun s => ∀ i : Fin n, Even (mult s.1 s.2.1 s.2.2 i))

/-- Sum over Balanced triples equals 6T(λ). -/
private lemma sum_balanced_eq_six_T {n : ℕ} (lam : Fin n → Fin n → ℝ) :
    (∑ s ∈ BalancedSet n, lam s.1.1 s.1.2 * lam s.2.1.1 s.2.1.2 *
        lam s.2.2.1 s.2.2.2) = 6 * T lam := by
  -- Reverse direction via a bijection from `Tset n × Fin 6` to `BalancedSet n`.
  -- First express RHS = ∑_{t} ∑_{κ} λ_p λ_q λ_r using lam_prod_order.
  have hRHS : (6 : ℝ) * T lam =
      ∑ tk ∈ (Tset n) ×ˢ (Finset.univ : Finset (Fin 6)),
        lam (order tk.1 tk.2).1.1 (order tk.1 tk.2).1.2 *
        lam (order tk.1 tk.2).2.1.1 (order tk.1 tk.2).2.1.2 *
        lam (order tk.1 tk.2).2.2.1 (order tk.1 tk.2).2.2.2 := by
    rw [Finset.sum_product]
    -- ∑ t ∈ Tset n, ∑ κ ∈ univ, ...
    have : ∀ t ∈ Tset n, ∀ κ ∈ (Finset.univ : Finset (Fin 6)),
        lam (order t κ).1.1 (order t κ).1.2 *
        lam (order t κ).2.1.1 (order t κ).2.1.2 *
        lam (order t κ).2.2.1 (order t κ).2.2.2 =
        lam t.1 t.2.1 * lam t.1 t.2.2 * lam t.2.1 t.2.2 := by
      intro t _ κ _
      exact lam_prod_order lam κ
    rw [Finset.sum_congr rfl
      (fun t ht => Finset.sum_congr rfl (fun κ hκ => this t ht κ hκ))]
    simp [Finset.sum_const, T, Tset, mul_comm]
  rw [hRHS]
  -- Now use Finset.sum_bij' with forward `order`.
  refine (Finset.sum_nbij' (fun s _ => order s.1 s.2)
    (fun s hs => Classical.choose (balanced_is_order s.1 s.2.1 s.2.2
      ((Finset.mem_product.mp ((Finset.mem_filter.mp hs).1)).1)
      ((Finset.mem_product.mp ((Finset.mem_product.mp ((Finset.mem_filter.mp hs).1)).2)).1)
      ((Finset.mem_product.mp ((Finset.mem_product.mp ((Finset.mem_filter.mp hs).1)).2)).2)
      ((Finset.mem_filter.mp hs).2)).choose_spec.choose_spec.choose,
      Classical.choose (balanced_is_order s.1 s.2.1 s.2.2
        ((Finset.mem_product.mp ((Finset.mem_filter.mp hs).1)).1)
        ((Finset.mem_product.mp ((Finset.mem_product.mp ((Finset.mem_filter.mp hs).1)).2)).1)
        ((Finset.mem_product.mp ((Finset.mem_product.mp ((Finset.mem_filter.mp hs).1)).2)).2)
        ((Finset.mem_filter.mp hs).2))) ?_ ?_ ?_ ?_ ?_).symm
  -- Forward into BalancedSet.
  all_goals sorry

end LeaHadamard.Hadamard
