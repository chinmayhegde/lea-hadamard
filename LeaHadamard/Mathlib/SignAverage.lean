/-
# Discrete sign-average moment layer (Stage 1)

This file packages reusable discrete sign-average identities and the
second-moment computation for the linear Rademacher form. It is the
foundational moment-layer infrastructure that downstream moment-bound
lemmas will build on.

The signs live on `Bool`-vectors `(Fin n → Bool) → ℝ`; the conversion to
`±1` is via `LeaHadamard.Defs.rad`, the Rademacher sign function from
`LeaHadamard.Defs`. The choice of `Bool` (rather than `Fin 2`) keeps us
uniform with the rest of the LeaHadamard project.
-/

import Mathlib
import LeaHadamard.Defs

open scoped BigOperators
open Finset

namespace LeaHadamard.SignAverage

/-- We reuse the Rademacher sign from `LeaHadamard.Defs`. -/
abbrev rad : Bool → ℝ := LeaHadamard.Defs.rad

/-! ## Definitions -/

/-- Uniform expectation of a real-valued function over `(Fin n → Bool)`. -/
noncomputable def avgSigns (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ σ : Fin n → Bool, f σ) / (2 ^ n : ℝ)

/-- The Rademacher linear form `∑ i, x i * rad (σ i)`. -/
noncomputable def linearX (n : ℕ) (x : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, x i * rad (σ i)

/-! ## Linearity / structural lemmas for `avgSigns` -/

lemma avgSigns_const {n : ℕ} (c : ℝ) :
    avgSigns n (fun _ : Fin n → Bool => c) = c := by
  unfold avgSigns
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_bool, Fintype.card_fin]
  rw [hcard, nsmul_eq_mul]
  push_cast
  field_simp

lemma avgSigns_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    avgSigns n (fun σ => f σ + g σ) = avgSigns n f + avgSigns n g := by
  unfold avgSigns
  rw [Finset.sum_add_distrib]
  ring

lemma avgSigns_mul_const_left {n : ℕ} (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    avgSigns n (fun σ => c * f σ) = c * avgSigns n f := by
  unfold avgSigns
  rw [← Finset.mul_sum]
  ring

lemma avgSigns_sum {n : ℕ} {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → (Fin n → Bool) → ℝ) :
    avgSigns n (fun σ => ∑ a ∈ s, f a σ) = ∑ a ∈ s, avgSigns n (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [avgSigns_const]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hfun :
          (fun σ : Fin n → Bool => f a σ + ∑ b ∈ s, f b σ)
            = (fun σ => f a σ + (fun τ => ∑ b ∈ s, f b τ) σ) := rfl
      rw [hfun, avgSigns_add, ih]

/-! ## Last-coordinate split -/

/-- Equivalence `(Fin (n+1) → Bool) ≃ (Fin n → Bool) × Bool` via `Fin.snoc`/`Fin.init`. -/
private def boolVecLastEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) × Bool where
  toFun := fun τ => (Fin.init (α := fun _ => Bool) τ, τ (Fin.last n))
  invFun := fun p => Fin.snoc (α := fun _ => Bool) p.1 p.2
  left_inv := by
    intro τ
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc]
    · intro j
      simp [Fin.snoc, Fin.init]
  right_inv := by
    intro p
    rcases p with ⟨σ, b⟩
    refine Prod.ext ?_ ?_
    · funext i
      simp [Fin.init]
    · simp [Fin.snoc]

/-- Sum over `Fin (n+1) → Bool` decomposes as a double sum over `(Fin n → Bool)` and `Bool`. -/
lemma sum_boolVec_split_last (n : ℕ) (g : (Fin (n + 1) → Bool) → ℝ) :
    (∑ τ : Fin (n + 1) → Bool, g τ)
      = ∑ σ : Fin n → Bool, ∑ b : Bool, g (Fin.snoc (α := fun _ => Bool) σ b) := by
  calc
    (∑ τ : Fin (n + 1) → Bool, g τ)
        = ∑ p : (Fin n → Bool) × Bool, g ((boolVecLastEquiv n).symm p) := by
            exact Fintype.sum_equiv (boolVecLastEquiv n)
              (fun τ : Fin (n + 1) → Bool => g τ)
              (fun p : (Fin n → Bool) × Bool => g ((boolVecLastEquiv n).symm p))
              (by intro τ; simp [boolVecLastEquiv])
    _ = ∑ σ : Fin n → Bool, ∑ b : Bool, g (Fin.snoc (α := fun _ => Bool) σ b) := by
          simpa [boolVecLastEquiv] using
            (Fintype.sum_prod_type
              (f := fun p : (Fin n → Bool) × Bool => g ((boolVecLastEquiv n).symm p)))

/-- The workhorse: average over `Fin (n+1)` signs equals the average over the
first `n` signs of the average over the last bit. -/
lemma avgSigns_split_last (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    avgSigns (n+1) f =
      avgSigns n (fun σ : Fin n → Bool =>
        (∑ b : Bool, f (Fin.snoc σ b)) / 2) := by
  unfold avgSigns
  rw [sum_boolVec_split_last]
  have hpow : ((2 : ℝ) ^ (n + 1) : ℝ) = (2 ^ n : ℝ) * 2 := by
    rw [pow_succ]
  rw [hpow]
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [show (∑ σ : Fin n → Bool, (∑ b : Bool, f (Fin.snoc σ b)) / 2)
        = (∑ σ : Fin n → Bool, ∑ b : Bool, f (Fin.snoc σ b)) / 2 from by
        rw [Finset.sum_div]]
  field_simp

/-! ## Second-moment identity for the linear form -/

/-- `linearX` after `Fin.snoc` peels off the last coordinate. -/
lemma linearX_snoc_last (n : ℕ) (x : Fin n → ℝ) (a : ℝ)
    (σ : Fin n → Bool) (b : Bool) :
    linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x a)
        (Fin.snoc (α := fun _ => Bool) σ b)
      = linearX n x σ + a * rad b := by
  unfold linearX
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc]

/-- Sum of `(A + Y * rad b)^2` over the last sign `b : Bool` is `2*(A^2 + Y^2)`. -/
private lemma sum_square_over_last_sign (A Y : ℝ) :
    (∑ b : Bool, (A + Y * rad b) ^ 2) = 2 * (A ^ 2 + Y ^ 2) := by
  simp [rad, LeaHadamard.Defs.rad]
  ring

/-- Snoc-decomposition of a sum of squares. -/
private lemma sum_sq_snoc (n : ℕ) (x : Fin n → ℝ) (a : ℝ) :
    (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x a i) ^ 2)
      = (∑ i : Fin n, x i ^ 2) + a ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc]

/-- The second moment of the linear Rademacher form equals `∑ x i ^ 2`. -/
lemma avgSigns_linearX_sq (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => (linearX n x σ) ^ 2)
      = ∑ i : Fin n, (x i) ^ 2 := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init (α := fun _ => ℝ) x
      let a : ℝ := x (Fin.last n)
      have hx : Fin.snoc (α := fun _ => ℝ) x₀ a = x := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [a, Fin.snoc]
        · intro j
          simp [x₀, Fin.snoc, Fin.init]
      rw [← hx, avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Bool =>
            ((∑ b : Bool,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2) / 2 : ℝ))
            =
          (fun σ : Fin n → Bool => linearX n x₀ σ ^ 2 + a ^ 2) := by
        funext σ
        have hs := sum_square_over_last_sign (linearX n x₀ σ) a
        have hsnoc :
            (∑ b : Bool,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2)
              = 2 * (linearX n x₀ σ ^ 2 + a ^ 2) := by
          rw [← hs]
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [linearX_snoc_last]
        rw [hsnoc]
        ring
      rw [hpoint, avgSigns_add, avgSigns_const, ih]
      have hsum_snoc := sum_sq_snoc n x₀ a
      linarith [hsum_snoc]

/-! ## Fourth-moment identity for the linear form -/

/-- Sum of `(A + Y * rad b)^4` over the last sign `b : Bool`. -/
private lemma sum_fourth_over_last_sign (A Y : ℝ) :
    (∑ b : Bool, (A + Y * rad b) ^ 4)
      = 2 * (A ^ 4 + 6 * A ^ 2 * Y ^ 2 + Y ^ 4) := by
  simp [rad, LeaHadamard.Defs.rad]
  ring

/-- Snoc-decomposition of a sum of fourth powers. -/
private lemma sum_fourth_snoc (n : ℕ) (x : Fin n → ℝ) (a : ℝ) :
    (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x a i) ^ 4)
      = (∑ i : Fin n, x i ^ 4) + a ^ 4 := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc]

/-- The fourth moment of the linear Rademacher form. -/
lemma avgSigns_linearX_four (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => (linearX n x σ) ^ 4)
      = 3 * (∑ i : Fin n, (x i) ^ 2) ^ 2
        - 2 * (∑ i : Fin n, (x i) ^ 4) := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init (α := fun _ => ℝ) x
      let a : ℝ := x (Fin.last n)
      have hx : Fin.snoc (α := fun _ => ℝ) x₀ a = x := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [a, Fin.snoc]
        · intro j
          simp [x₀, Fin.snoc, Fin.init]
      rw [← hx, avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Bool =>
            ((∑ b : Bool,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Bool) σ b)) ^ 4) / 2 : ℝ))
            =
          (fun σ : Fin n → Bool =>
            linearX n x₀ σ ^ 4
              + 6 * a ^ 2 * linearX n x₀ σ ^ 2
              + a ^ 4) := by
        funext σ
        have hs := sum_fourth_over_last_sign (linearX n x₀ σ) a
        have hsnoc :
            (∑ b : Bool,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Bool) σ b)) ^ 4)
              = 2 * (linearX n x₀ σ ^ 4
                      + 6 * linearX n x₀ σ ^ 2 * a ^ 2 + a ^ 4) := by
          rw [← hs]
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [linearX_snoc_last]
        rw [hsnoc]
        ring
      rw [hpoint, avgSigns_add, avgSigns_add,
          avgSigns_const, avgSigns_mul_const_left,
          avgSigns_linearX_sq, ih]
      have hs2 := sum_sq_snoc n x₀ a
      have hs4 := sum_fourth_snoc n x₀ a
      rw [hs2, hs4]
      ring

end LeaHadamard.SignAverage
