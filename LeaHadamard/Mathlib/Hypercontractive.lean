/-
# Hypercontractive inequality for Rademacher polynomials of degree ≤ 2 (Stage 5)

This file builds on:

* `LeaHadamard/Mathlib/SignAverage.lean` (uniform sign-averages,
  `linearX`, second/fourth moment identities for the Rademacher linear
  form);

* `LeaHadamard/Mathlib/BonamiTwoPoint.lean` (Bonami's two-point base
  case in its various forms);

and adds:

* `WalshDeg2 n` — an explicit data structure for a Walsh polynomial of
  degree ≤ 2 in `n` Rademacher variables (constant + linear + symmetric
  quadratic part with vanishing diagonal);

* `eval` and an L²-norm identity `avgSigns_walshDeg2_sq` (orthogonality
  of Walsh characters);

* `hc_degree2_fourth` — the headline degree-2 hypercontractive estimate

  `E[p^4] ≤ 81 · (E[p^2])^2`,

  i.e. `‖p‖₄ ≤ 3 · ‖p‖₂`. The constant `81 = 3^4` matches Bonami-Beckner
  with `(q-1)^{p/2}` at `(p,q)=(4,2)` for degree 2.

The proof is the standard inductive tensorization on `n`. We peel off the
last Rademacher variable: a degree-2 polynomial `p` in `n+1` variables
becomes `p(σ, b) = g(σ) + rad(b) · h(σ)` with `g` of degree ≤ 2 in the
first `n` variables and `h` of degree ≤ 1 in the first `n` variables.
Conditional on the last bit averaging out:

  `E[p^2] = E[g^2] + E[h^2]` and
  `E[p^4] = E[g^4] + 6·E[g^2 h^2] + E[h^4]`.

The cross term is controlled by Cauchy–Schwarz:

  `E[g^2 h^2] ≤ √(E[g^4] · E[h^4]) ≤ √(81·9) · E[g^2]·E[h^2]
              = 27·E[g^2]·E[h^2]`.

Combined with the inductive hypothesis `E[g^4] ≤ 81·(E[g^2])^2` and the
linear case `E[h^4] ≤ 9·(E[h^2])^2`, this yields
`E[p^4] ≤ 81·(E[g^2]+E[h^2])^2 = 81·(E[p^2])^2`. -/

import Mathlib
import LeaHadamard.Defs
import LeaHadamard.Mathlib.SignAverage
import LeaHadamard.Mathlib.BonamiTwoPoint

open scoped BigOperators
open Finset
open LeaHadamard.SignAverage

namespace LeaHadamard.Hypercontractive

/-! ## Degree-1 polynomials -/

/-- A Walsh polynomial of degree ≤ 1 in `n` Rademacher variables: a
constant plus a linear form. -/
structure WalshDeg1 (n : ℕ) where
  const   : ℝ
  linCoeff : Fin n → ℝ

/-- Evaluation of a degree-1 Walsh polynomial. -/
noncomputable def evalDeg1 {n : ℕ} (h : WalshDeg1 n) (σ : Fin n → Bool) : ℝ :=
  h.const + linearX n h.linCoeff σ

/-! ## Degree-2 polynomials -/

/-- A Walsh polynomial of degree ≤ 2 in `n` Rademacher variables: a
constant, a linear form, and a symmetric quadratic part with vanishing
diagonal. The factor `1/2` in `eval` makes the symmetric coefficients
`quadCoeff i j` (for `i ≠ j`) the natural objects under orthogonality. -/
structure WalshDeg2 (n : ℕ) where
  const     : ℝ
  linCoeff  : Fin n → ℝ
  quadCoeff : Fin n → Fin n → ℝ
  symm      : ∀ i j, quadCoeff i j = quadCoeff j i
  diag_zero : ∀ i, quadCoeff i i = 0

/-- Evaluation of a degree-2 Walsh polynomial. -/
noncomputable def eval {n : ℕ} (p : WalshDeg2 n) (σ : Fin n → Bool) : ℝ :=
  p.const + (∑ i, p.linCoeff i * rad (σ i))
    + (1 / 2) * ∑ i, ∑ j, p.quadCoeff i j * rad (σ i) * rad (σ j)

/-! ## Restriction to the first `n` variables -/

/-- Restrict a degree-1 polynomial in `n+1` variables to the first `n`
variables, given the value of the last bit. The result is degree ≤ 1
in the first `n` variables (just absorb the last Rademacher value
`rad b` into the constant). -/
noncomputable def WalshDeg1.restrictLast {n : ℕ}
    (h : WalshDeg1 (n + 1)) (b : Bool) : WalshDeg1 n where
  const :=
    h.const + h.linCoeff (Fin.last n) * rad b
  linCoeff := fun i => h.linCoeff (Fin.castSucc i)

/-- The "tail" of a degree-2 polynomial in `n+1` variables: the part
that does NOT depend on the last Rademacher variable, viewed as a
degree-2 polynomial in the first `n` variables. -/
noncomputable def WalshDeg2.tail {n : ℕ} (p : WalshDeg2 (n + 1)) : WalshDeg2 n where
  const     := p.const
  linCoeff  := fun i => p.linCoeff (Fin.castSucc i)
  quadCoeff := fun i j => p.quadCoeff (Fin.castSucc i) (Fin.castSucc j)
  symm      := fun _ _ => p.symm _ _
  diag_zero := fun _ => p.diag_zero _

/-- The "last-coordinate slice" of a degree-2 polynomial in `n+1`
variables: the coefficient vector of `rad σ_{n+1}` is itself a degree-1
polynomial in the first `n` variables (constant from `linCoeff (last n)`
plus the off-diagonal interactions with the last coordinate). -/
noncomputable def WalshDeg2.lastSlice {n : ℕ}
    (p : WalshDeg2 (n + 1)) : WalshDeg1 n where
  const := p.linCoeff (Fin.last n)
  linCoeff := fun i => p.quadCoeff (Fin.castSucc i) (Fin.last n)

/-! ## Helper: averages of pure Rademacher monomials -/

/-- The single-coordinate Rademacher sign averages to `0`. Use the
linear-form second-moment identity at the standard basis vector
`e_i`: even though we want the *first* moment, we exploit the fact
that `(rad b)² = 1` and average via `avgSigns_split_last`. -/
lemma avgSigns_rad_eq_zero {n : ℕ} (i : Fin n) :
    avgSigns n (fun σ : Fin n → Bool => rad (σ i)) = 0 := by
  -- We prove this by induction on `n` using `avgSigns_split_last`.
  -- The key observation: `∑ b : Bool, rad b = 0`.
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      -- Two cases: either i is the last coordinate, or it isn't.
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · -- i = i'.castSucc: peel off last bit; the value doesn't depend on it.
        rw [avgSigns_split_last]
        have hpoint :
            (fun σ : Fin n → Bool =>
              ((∑ b : Bool, rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc i'))) / 2 : ℝ))
              = (fun σ : Fin n → Bool => rad (σ i')) := by
          funext σ
          have :
              (∑ b : Bool,
                  rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc i')))
                = 2 * rad (σ i') := by
            simp [Fin.snoc_castSucc]
          rw [this]; ring
        rw [hpoint]
        exact ih i'
      · -- i = Fin.last n: peel off last bit; here it's exactly the last bit.
        rw [avgSigns_split_last]
        have hpoint :
            (fun σ : Fin n → Bool =>
              ((∑ b : Bool, rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.last n))) / 2 : ℝ))
              = (fun _ : Fin n → Bool => (0 : ℝ)) := by
          funext σ
          simp [Fin.snoc_last, LeaHadamard.Defs.rad]
        rw [hpoint, avgSigns_const]

/-- The product of two distinct-coordinate Rademacher signs averages to `0`. -/
lemma avgSigns_rad_mul_rad_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    avgSigns n (fun σ : Fin n → Bool => rad (σ i) * rad (σ j)) = 0 := by
  -- By induction on `n`, peeling off the last variable.
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', hi'⟩ | hi'
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', hj'⟩ | hj'
        · -- both castSucc: reduce to ih, since i' ≠ j'.
          subst hi'; subst hj'
          have hij' : i' ≠ j' := by
            intro h; apply hij; rw [h]
          rw [avgSigns_split_last]
          have hpoint :
              (fun σ : Fin n → Bool =>
                ((∑ b : Bool,
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc i')) *
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc j'))) / 2 : ℝ))
                = (fun σ : Fin n → Bool => rad (σ i') * rad (σ j')) := by
            funext σ
            have :
                (∑ b : Bool,
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc i')) *
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc j')))
                  = 2 * (rad (σ i') * rad (σ j')) := by
              simp [Fin.snoc_castSucc]
            rw [this]; ring
          rw [hpoint]
          exact ih hij'
        · -- i = castSucc i', j = last: cross term, average = 0.
          subst hi'; subst hj'
          rw [avgSigns_split_last]
          have hpoint :
              (fun σ : Fin n → Bool =>
                ((∑ b : Bool,
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc i')) *
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.last n))) / 2 : ℝ))
                = (fun _ : Fin n → Bool => (0 : ℝ)) := by
            funext σ
            simp [Fin.snoc_castSucc, Fin.snoc_last, LeaHadamard.Defs.rad]
          rw [hpoint, avgSigns_const]
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', hj'⟩ | hj'
        · -- i = last, j = castSucc j': cross term, average = 0.
          subst hi'; subst hj'
          rw [avgSigns_split_last]
          have hpoint :
              (fun σ : Fin n → Bool =>
                ((∑ b : Bool,
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.last n)) *
                    rad ((Fin.snoc σ b : Fin (n + 1) → Bool) (Fin.castSucc j'))) / 2 : ℝ))
                = (fun _ : Fin n → Bool => (0 : ℝ)) := by
            funext σ
            simp [Fin.snoc_castSucc, Fin.snoc_last, LeaHadamard.Defs.rad]
          rw [hpoint, avgSigns_const]
        · -- both last: contradiction with i ≠ j.
          subst hi'; subst hj'; exact (hij rfl).elim

/-! ## L² identity for degree-1 polynomials -/

/-- Linearity push of `linearX` through `avgSigns`: the linear form
averages to zero. -/
lemma avgSigns_linearX_eq_zero {n : ℕ} (a : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n a σ) = 0 := by
  classical
  unfold linearX
  rw [show (fun σ : Fin n → Bool => ∑ i, a i * rad (σ i))
        = (fun σ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (fun (i : Fin n) (τ : Fin n → Bool) => a i * rad (τ i)) i σ)
      from rfl,
      avgSigns_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (fun (τ : Fin n → Bool) => a i * rad (τ i))
        = (fun τ => a i * (fun ρ : Fin n → Bool => rad (ρ i)) τ) from rfl,
      avgSigns_mul_const_left, avgSigns_rad_eq_zero]
  ring

/-- The L² identity for a degree-1 polynomial. -/
lemma avgSigns_evalDeg1_sq {n : ℕ} (h : WalshDeg1 n) :
    avgSigns n (fun σ => (evalDeg1 h σ) ^ 2)
      = h.const ^ 2 + ∑ i, (h.linCoeff i) ^ 2 := by
  unfold evalDeg1
  have hexpand :
      (fun σ : Fin n → Bool => (h.const + linearX n h.linCoeff σ) ^ 2)
        = (fun σ => h.const ^ 2 + (2 * h.const) * linearX n h.linCoeff σ
                      + (linearX n h.linCoeff σ) ^ 2) := by
    funext σ; ring
  rw [hexpand]
  rw [show (fun σ : Fin n → Bool =>
              h.const ^ 2 + 2 * h.const * linearX n h.linCoeff σ
                + linearX n h.linCoeff σ ^ 2)
        = (fun σ : Fin n → Bool =>
              (h.const ^ 2 + 2 * h.const * linearX n h.linCoeff σ)
                + linearX n h.linCoeff σ ^ 2) from rfl,
      avgSigns_add,
      show (fun σ : Fin n → Bool =>
              h.const ^ 2 + 2 * h.const * linearX n h.linCoeff σ)
        = (fun σ : Fin n → Bool =>
              (fun _ : Fin n → Bool => (h.const : ℝ) ^ 2) σ
                + 2 * h.const * linearX n h.linCoeff σ) from rfl,
      avgSigns_add, avgSigns_const, avgSigns_mul_const_left,
      avgSigns_linearX_eq_zero, avgSigns_linearX_sq]
  ring

/-! ## Snoc / split decomposition of `eval` -/

/-- Evaluating a degree-2 polynomial `p : WalshDeg2 (n+1)` at
`Fin.snoc σ b` decomposes as
`eval (tail p) σ + rad b · evalDeg1 (lastSlice p) σ`. -/
lemma eval_snoc_decomp {n : ℕ} (p : WalshDeg2 (n + 1))
    (σ : Fin n → Bool) (b : Bool) :
    eval p (Fin.snoc (α := fun _ => Bool) σ b)
      = eval p.tail σ + rad b * evalDeg1 p.lastSlice σ := by
  classical
  unfold eval evalDeg1 linearX
  -- Linear part split.
  have hLin :
      (∑ i : Fin (n + 1),
          p.linCoeff i * rad ((Fin.snoc (α := fun _ => Bool) σ b) i))
        = (∑ i : Fin n, p.linCoeff (Fin.castSucc i) * rad (σ i))
          + p.linCoeff (Fin.last n) * rad b := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  -- Quadratic part split.
  have hQuad :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          p.quadCoeff i j *
            rad ((Fin.snoc (α := fun _ => Bool) σ b) i) *
              rad ((Fin.snoc (α := fun _ => Bool) σ b) j))
        =
          (∑ i : Fin n, ∑ j : Fin n,
              p.quadCoeff (Fin.castSucc i) (Fin.castSucc j) *
                rad (σ i) * rad (σ j))
          + 2 * (∑ i : Fin n,
              p.quadCoeff (Fin.castSucc i) (Fin.last n) *
                rad (σ i) * rad b) := by
    rw [Fin.sum_univ_castSucc]
    -- The outer sum is split into i = castSucc i₀ and i = last n.
    -- For each i, split the inner sum the same way.
    have hCast :
        ∀ i : Fin n,
          (∑ j : Fin (n + 1),
              p.quadCoeff (Fin.castSucc i) j *
                rad ((Fin.snoc (α := fun _ => Bool) σ b) (Fin.castSucc i)) *
                  rad ((Fin.snoc (α := fun _ => Bool) σ b) j))
            = (∑ j : Fin n,
                p.quadCoeff (Fin.castSucc i) (Fin.castSucc j) *
                  rad (σ i) * rad (σ j))
              + p.quadCoeff (Fin.castSucc i) (Fin.last n) *
                  rad (σ i) * rad b := by
      intro i
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have hLast :
        (∑ j : Fin (n + 1),
            p.quadCoeff (Fin.last n) j *
              rad ((Fin.snoc (α := fun _ => Bool) σ b) (Fin.last n)) *
                rad ((Fin.snoc (α := fun _ => Bool) σ b) j))
          = (∑ j : Fin n,
              p.quadCoeff (Fin.last n) (Fin.castSucc j) *
                rad b * rad (σ j))
            + p.quadCoeff (Fin.last n) (Fin.last n) *
                rad b * rad b := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    -- diag is zero.
    have hdiag : p.quadCoeff (Fin.last n) (Fin.last n) = 0 := p.diag_zero _
    -- Symmetry rewrite.
    have hsymR :
        ∀ i : Fin n,
          p.quadCoeff (Fin.last n) (Fin.castSucc i)
            = p.quadCoeff (Fin.castSucc i) (Fin.last n) := fun i => p.symm _ _
    -- Now assemble.
    rw [show (∑ i : Fin n,
                ∑ j : Fin (n + 1),
                  p.quadCoeff (Fin.castSucc i) j *
                    rad ((Fin.snoc (α := fun _ => Bool) σ b) (Fin.castSucc i)) *
                      rad ((Fin.snoc (α := fun _ => Bool) σ b) j))
          = ∑ i : Fin n,
              ((∑ j : Fin n,
                  p.quadCoeff (Fin.castSucc i) (Fin.castSucc j) *
                    rad (σ i) * rad (σ j))
                + p.quadCoeff (Fin.castSucc i) (Fin.last n) *
                    rad (σ i) * rad b) from
        Finset.sum_congr rfl (fun i _ => hCast i),
        hLast, hdiag,
        Finset.sum_add_distrib]
    -- Simplify the last-summand row.
    have hRowSum :
        (∑ j : Fin n,
            p.quadCoeff (Fin.last n) (Fin.castSucc j) * rad b * rad (σ j))
          = ∑ j : Fin n,
              p.quadCoeff (Fin.castSucc j) (Fin.last n) * rad (σ j) * rad b := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hsymR j]; ring
    rw [hRowSum]
    ring
  rw [hLin, hQuad]
  -- Pull the `rad b` factor into the sum on the RHS.
  have hpull :
      rad b * (p.linCoeff (Fin.last n)
          + ∑ i : Fin n,
              p.quadCoeff (Fin.castSucc i) (Fin.last n) * rad (σ i))
        = rad b * p.linCoeff (Fin.last n)
          + ∑ i : Fin n,
              p.quadCoeff (Fin.castSucc i) (Fin.last n) *
                rad (σ i) * rad b := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => by ring)
  -- The RHS uses `tail` and `lastSlice` definitions; unfold them.
  show p.const +
      ((∑ i : Fin n, p.linCoeff (Fin.castSucc i) * rad (σ i))
        + p.linCoeff (Fin.last n) * rad b) +
      (1 / 2) * ((∑ i : Fin n, ∑ j : Fin n,
          p.quadCoeff (Fin.castSucc i) (Fin.castSucc j) *
            rad (σ i) * rad (σ j))
        + 2 * (∑ i : Fin n,
            p.quadCoeff (Fin.castSucc i) (Fin.last n) *
              rad (σ i) * rad b))
      = (p.const + (∑ i : Fin n,
            p.linCoeff (Fin.castSucc i) * rad (σ i))
          + (1 / 2) * ∑ i : Fin n, ∑ j : Fin n,
              p.quadCoeff (Fin.castSucc i) (Fin.castSucc j) *
                rad (σ i) * rad (σ j))
        + rad b * (p.linCoeff (Fin.last n)
            + ∑ i : Fin n,
                p.quadCoeff (Fin.castSucc i) (Fin.last n) * rad (σ i))
  rw [hpull]
  ring

/-! ## L² identity for `WalshDeg2`, by induction on `n` -/

lemma avgSigns_walshDeg2_sq {n : ℕ} (p : WalshDeg2 n) :
    avgSigns n (fun σ => (eval p σ) ^ 2)
      = p.const ^ 2 + (∑ i, (p.linCoeff i) ^ 2)
        + (1 / 2) * ∑ i, ∑ j, (p.quadCoeff i j) ^ 2 := by
  induction n with
  | zero =>
      -- All sums are empty; eval p σ = p.const.
      simp [avgSigns, eval]
  | succ n ih =>
      -- Peel off the last bit using eval_snoc_decomp.
      rw [avgSigns_split_last]
      -- Compute the inner average over b of (g + rad b * h)².
      have hpoint :
          (fun σ : Fin n → Bool =>
            ((∑ b : Bool,
                (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2) / 2 : ℝ))
            = (fun σ : Fin n → Bool =>
                (eval p.tail σ) ^ 2 + (evalDeg1 p.lastSlice σ) ^ 2) := by
        funext σ
        have hb :
            ∀ b : Bool,
              (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2
                = (eval p.tail σ + rad b * evalDeg1 p.lastSlice σ) ^ 2 := by
          intro b; rw [eval_snoc_decomp]
        rw [show (∑ b : Bool,
                  (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2)
              = ∑ b : Bool,
                  (eval p.tail σ + rad b * evalDeg1 p.lastSlice σ) ^ 2 from
              Finset.sum_congr rfl (fun b _ => hb b)]
        -- Now this is the standard sum over b ∈ {true, false}.
        simp [LeaHadamard.Defs.rad]
        ring
      rw [hpoint, avgSigns_add, ih, avgSigns_evalDeg1_sq]
      -- Now expand `tail` and `lastSlice` definitions and reassemble.
      show
        (p.tail.const ^ 2 + ∑ i : Fin n, (p.tail.linCoeff i) ^ 2
            + (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, (p.tail.quadCoeff i j) ^ 2)
          + (p.lastSlice.const ^ 2 + ∑ i : Fin n, (p.lastSlice.linCoeff i) ^ 2)
          = p.const ^ 2 + (∑ i : Fin (n + 1), (p.linCoeff i) ^ 2)
            + (1 / 2) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (p.quadCoeff i j) ^ 2
      -- Unfold `tail` / `lastSlice`.
      show
        (p.const ^ 2 + ∑ i : Fin n, (p.linCoeff (Fin.castSucc i)) ^ 2
            + (1 / 2) * ∑ i : Fin n, ∑ j : Fin n,
                (p.quadCoeff (Fin.castSucc i) (Fin.castSucc j)) ^ 2)
          + ((p.linCoeff (Fin.last n)) ^ 2
              + ∑ i : Fin n, (p.quadCoeff (Fin.castSucc i) (Fin.last n)) ^ 2)
          = p.const ^ 2 + (∑ i : Fin (n + 1), (p.linCoeff i) ^ 2)
            + (1 / 2) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (p.quadCoeff i j) ^ 2
      -- Linear identity.
      have hLinSq :
          (∑ i : Fin (n + 1), (p.linCoeff i) ^ 2)
            = (∑ i : Fin n, (p.linCoeff (Fin.castSucc i)) ^ 2)
              + (p.linCoeff (Fin.last n)) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
      -- Quadratic identity: split the outer i then the inner j; use diag_zero/symm.
      have hQuadSq :
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (p.quadCoeff i j) ^ 2)
            = (∑ i : Fin n, ∑ j : Fin n,
                (p.quadCoeff (Fin.castSucc i) (Fin.castSucc j)) ^ 2)
              + 2 * ∑ i : Fin n,
                  (p.quadCoeff (Fin.castSucc i) (Fin.last n)) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        -- Inner-row split.
        have hRow :
            ∀ i : Fin (n + 1),
              (∑ j : Fin (n + 1), (p.quadCoeff i j) ^ 2)
                = (∑ j : Fin n, (p.quadCoeff i (Fin.castSucc j)) ^ 2)
                  + (p.quadCoeff i (Fin.last n)) ^ 2 := by
          intro i
          rw [Fin.sum_univ_castSucc]
        -- Apply hRow at castSucc i and last; use diag_zero and symm.
        have hCastRow :
            ∀ i : Fin n,
              (∑ j : Fin (n + 1), (p.quadCoeff (Fin.castSucc i) j) ^ 2)
                = (∑ j : Fin n,
                    (p.quadCoeff (Fin.castSucc i) (Fin.castSucc j)) ^ 2)
                  + (p.quadCoeff (Fin.castSucc i) (Fin.last n)) ^ 2 := fun i =>
          hRow (Fin.castSucc i)
        have hLastRow :
            (∑ j : Fin (n + 1), (p.quadCoeff (Fin.last n) j) ^ 2)
              = (∑ j : Fin n,
                  (p.quadCoeff (Fin.last n) (Fin.castSucc j)) ^ 2)
                + (p.quadCoeff (Fin.last n) (Fin.last n)) ^ 2 := hRow (Fin.last n)
        have hdiag : p.quadCoeff (Fin.last n) (Fin.last n) = 0 := p.diag_zero _
        have hsymR :
            ∀ i : Fin n,
              (p.quadCoeff (Fin.last n) (Fin.castSucc i)) ^ 2
                = (p.quadCoeff (Fin.castSucc i) (Fin.last n)) ^ 2 := by
          intro i; rw [p.symm]
        rw [show (∑ i : Fin n,
                    ∑ j : Fin (n + 1), (p.quadCoeff (Fin.castSucc i) j) ^ 2)
              = ∑ i : Fin n,
                  ((∑ j : Fin n,
                      (p.quadCoeff (Fin.castSucc i) (Fin.castSucc j)) ^ 2)
                    + (p.quadCoeff (Fin.castSucc i) (Fin.last n)) ^ 2) from
            Finset.sum_congr rfl (fun i _ => hCastRow i),
          hLastRow, hdiag,
          show (∑ j : Fin n, (p.quadCoeff (Fin.last n) (Fin.castSucc j)) ^ 2)
              = ∑ j : Fin n, (p.quadCoeff (Fin.castSucc j) (Fin.last n)) ^ 2 from
            Finset.sum_congr rfl (fun j _ => hsymR j),
          Finset.sum_add_distrib]
        ring
      rw [hLinSq, hQuadSq]
      ring

/-! ## Odd moments of the linear form vanish (flip-all-bits involution) -/

/-- Flipping every coordinate negates the linear form. -/
private lemma linearX_flipAll {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) :
    linearX n a (fun i => Bool.not (σ i)) = - linearX n a σ := by
  unfold linearX
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hrad : rad (Bool.not (σ i)) = - rad (σ i) := LeaHadamard.Defs.rad_not (σ i)
  rw [show (fun i => Bool.not (σ i)) i = Bool.not (σ i) from rfl, hrad]
  ring

/-- The flip-all-bits map as an equivalence on `Fin n → Bool`. -/
private def flipAllEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ := fun i => Bool.not (σ i)
  invFun σ := fun i => Bool.not (σ i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

/-- The third moment of a linear Rademacher form is `0` (odd-moment vanishing
by the flip-all involution). -/
lemma avgSigns_linearX_cube (n : ℕ) (a : Fin n → ℝ) :
    avgSigns n (fun σ => (linearX n a σ) ^ 3) = 0 := by
  classical
  unfold avgSigns
  have hsum : (∑ σ : Fin n → Bool, (linearX n a σ) ^ 3) = 0 := by
    have hflip :
        (∑ σ : Fin n → Bool, (linearX n a σ) ^ 3)
          = ∑ σ : Fin n → Bool,
              (linearX n a ((flipAllEquiv n) σ)) ^ 3 := by
      exact (Fintype.sum_equiv (flipAllEquiv n)
        (fun σ : Fin n → Bool => (linearX n a ((flipAllEquiv n) σ)) ^ 3)
        (fun σ : Fin n → Bool => (linearX n a σ) ^ 3)
        (by intro σ; rfl)).symm
    have hneg :
        (∑ σ : Fin n → Bool, (linearX n a ((flipAllEquiv n) σ)) ^ 3)
          = - (∑ σ : Fin n → Bool, (linearX n a σ) ^ 3) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro σ _
      have hflip := linearX_flipAll a σ
      have hsubst : linearX n a ((flipAllEquiv n) σ) = - linearX n a σ := hflip
      rw [hsubst]
      ring
    have heq :
        (∑ σ : Fin n → Bool, (linearX n a σ) ^ 3)
          = - (∑ σ : Fin n → Bool, (linearX n a σ) ^ 3) := hflip.trans hneg
    linarith
  rw [hsum]; simp

/-! ## Hypercontractive bound for degree-1 polynomials -/

/-- The L⁴-vs-(L²)² bound for a degree-1 polynomial: constant 9 = 3². -/
lemma hc_degree1_fourth {n : ℕ} (h : WalshDeg1 n) :
    avgSigns n (fun σ => (evalDeg1 h σ) ^ 4)
      ≤ 9 * (avgSigns n (fun σ => (evalDeg1 h σ) ^ 2)) ^ 2 := by
  -- Set c = h.const, a = h.linCoeff. Compute moments.
  set c := h.const
  set a := h.linCoeff
  set S := ∑ i : Fin n, (a i) ^ 2 with hSdef
  -- E[L²] = S, E[L⁴] ≤ 3·S² (already established).
  have hE2 : avgSigns n (fun σ => (linearX n a σ) ^ 2) = S := by
    rw [hSdef]; exact avgSigns_linearX_sq n a
  have hE4 :
      avgSigns n (fun σ => (linearX n a σ) ^ 4) ≤ 3 * S ^ 2 := by
    have := LeaHadamard.BonamiTwoPoint.avgSigns_linearX_fourth_le_three_sq_second_sq n a
    rw [hE2] at this
    exact this
  have hE1 : avgSigns n (fun σ => linearX n a σ) = 0 := avgSigns_linearX_eq_zero a
  have hE3 : avgSigns n (fun σ => (linearX n a σ) ^ 3) = 0 :=
    avgSigns_linearX_cube n a
  -- Expand E[(c+L)²] = c² + S.
  have hSq :
      avgSigns n (fun σ => (evalDeg1 h σ) ^ 2) = c ^ 2 + S := by
    have := avgSigns_evalDeg1_sq h
    show avgSigns n (fun σ => (evalDeg1 h σ) ^ 2) = c ^ 2 + S
    rw [this]
  -- Expand (c+L)⁴ = c⁴ + 4c³L + 6c²L² + 4cL³ + L⁴.
  have hExpand :
      (fun σ : Fin n → Bool => (evalDeg1 h σ) ^ 4)
        = (fun σ : Fin n → Bool =>
            c ^ 4 + 4 * c ^ 3 * linearX n a σ + 6 * c ^ 2 * (linearX n a σ) ^ 2
              + 4 * c * (linearX n a σ) ^ 3 + (linearX n a σ) ^ 4) := by
    funext σ
    show (c + linearX n a σ) ^ 4 = _
    ring
  -- Compute E[(c+L)⁴] using linearity.
  have hE4cL :
      avgSigns n (fun σ => (evalDeg1 h σ) ^ 4)
        = c ^ 4 + 6 * c ^ 2 * S
          + avgSigns n (fun σ => (linearX n a σ) ^ 4) := by
    rw [hExpand]
    -- Pull each term through avgSigns_add and avgSigns_const/mul.
    have step :
        avgSigns n (fun σ : Fin n → Bool =>
              c ^ 4 + 4 * c ^ 3 * linearX n a σ
                + 6 * c ^ 2 * (linearX n a σ) ^ 2
                + 4 * c * (linearX n a σ) ^ 3
                + (linearX n a σ) ^ 4)
          = c ^ 4
            + 4 * c ^ 3 * avgSigns n (fun σ => linearX n a σ)
            + 6 * c ^ 2 * avgSigns n (fun σ => (linearX n a σ) ^ 2)
            + 4 * c * avgSigns n (fun σ => (linearX n a σ) ^ 3)
            + avgSigns n (fun σ => (linearX n a σ) ^ 4) := by
      -- Strategy: rewrite the function as a series of additions and apply
      -- avgSigns_add / avgSigns_const / avgSigns_mul_const_left.
      have key :
          (fun σ : Fin n → Bool =>
              c ^ 4 + 4 * c ^ 3 * linearX n a σ
                + 6 * c ^ 2 * (linearX n a σ) ^ 2
                + 4 * c * (linearX n a σ) ^ 3
                + (linearX n a σ) ^ 4)
            = (fun σ : Fin n → Bool =>
                ((((fun _ : Fin n → Bool => (c : ℝ) ^ 4) σ
                  + (4 * c ^ 3) * linearX n a σ)
                  + (6 * c ^ 2) * (linearX n a σ) ^ 2)
                  + (4 * c) * (linearX n a σ) ^ 3)
                  + (linearX n a σ) ^ 4) := by
        funext σ; ring
      rw [key]
      rw [avgSigns_add, avgSigns_add, avgSigns_add, avgSigns_add,
          avgSigns_const, avgSigns_mul_const_left, avgSigns_mul_const_left,
          avgSigns_mul_const_left]
    rw [step, hE1, hE2, hE3]
    ring
  rw [hE4cL, hSq]
  -- Goal: c⁴ + 6c²S + E[L⁴] ≤ 9·(c²+S)².
  have h9 : 9 * (c ^ 2 + S) ^ 2 = 9 * c ^ 4 + 18 * c ^ 2 * S + 9 * S ^ 2 := by ring
  rw [h9]
  -- We have E[L⁴] ≤ 3 S². Show c⁴ + 6c²S + 3S² ≤ 9c⁴ + 18c²S + 9S².
  have hSnn : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [hE4, sq_nonneg c, sq_nonneg S, sq_nonneg (c ^ 2 - S), sq_nonneg (c ^ 2 + S)]

/-! ## Hypercontractive bound for degree-2 polynomials -/

/-- The Cauchy–Schwarz inequality for `avgSigns`: a uniform-measure
specialization of the standard finite-sum Cauchy–Schwarz. -/
lemma avgSigns_mul_sq_le {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    (avgSigns n (fun σ => f σ * g σ)) ^ 2
      ≤ avgSigns n (fun σ => (f σ) ^ 2) * avgSigns n (fun σ => (g σ) ^ 2) := by
  -- Apply the Cauchy–Schwarz `sum_mul_sq_le_sq_mul_sq` and divide by `(2^n)^2`.
  unfold avgSigns
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have h2nnn : (0 : ℝ) ≤ ((2 : ℝ) ^ n) := by positivity
  have hCS :
      (∑ σ : Fin n → Bool, f σ * g σ) ^ 2
        ≤ (∑ σ : Fin n → Bool, (f σ) ^ 2)
          * ∑ σ : Fin n → Bool, (g σ) ^ 2 := by
    exact sum_mul_sq_le_sq_mul_sq _ f g
  -- Goal: ((∑ fg)/2^n)² ≤ ((∑ f²)/2^n) · ((∑ g²)/2^n).
  rw [div_pow, div_mul_div_comm]
  have h2n2 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 2 := by positivity
  have h2nn : (0 : ℝ) < ((2 : ℝ) ^ n) * ((2 : ℝ) ^ n) := by positivity
  rw [div_le_div_iff₀ h2n2 h2nn]
  have h22nn : (0 : ℝ) ≤ ((2 : ℝ) ^ n) * ((2 : ℝ) ^ n) := by positivity
  calc (∑ σ : Fin n → Bool, f σ * g σ) ^ 2 * ((2 : ℝ) ^ n * 2 ^ n)
      ≤ ((∑ σ : Fin n → Bool, (f σ) ^ 2)
          * ∑ σ : Fin n → Bool, (g σ) ^ 2) * ((2 : ℝ) ^ n * 2 ^ n) :=
            mul_le_mul_of_nonneg_right hCS h22nn
    _ = ((∑ σ : Fin n → Bool, (f σ) ^ 2)
          * ∑ σ : Fin n → Bool, (g σ) ^ 2) * (2 ^ n) ^ 2 := by ring

/-- The L⁴-vs-(L²)² bound for a Walsh polynomial of degree ≤ 2: constant
81 = 3⁴. The proof is by induction on `n`, peeling off the last variable
and combining: (a) the inductive hypothesis on the `tail` (degree-2 in `n`
variables); (b) the linear-form bound on the `lastSlice` (degree-1 in `n`
variables); (c) Cauchy–Schwarz on the cross term. -/
theorem hc_degree2_fourth {n : ℕ} (p : WalshDeg2 n) :
    avgSigns n (fun σ => (eval p σ) ^ 4)
      ≤ 81 * (avgSigns n (fun σ => (eval p σ) ^ 2)) ^ 2 := by
  induction n with
  | zero =>
      -- eval p σ = p.const for all σ.
      have hev : ∀ σ : Fin 0 → Bool, eval p σ = p.const := by
        intro σ
        show p.const + (∑ i : Fin 0, p.linCoeff i * rad (σ i))
              + (1 / 2) * ∑ i : Fin 0, ∑ j : Fin 0,
                  p.quadCoeff i j * rad (σ i) * rad (σ j) = p.const
        simp
      have hL2 :
          avgSigns 0 (fun σ => (eval p σ) ^ 2) = p.const ^ 2 := by
        have : (fun σ : Fin 0 → Bool => (eval p σ) ^ 2)
                = fun _ => p.const ^ 2 := by funext σ; rw [hev]
        rw [this, avgSigns_const]
      have hL4 :
          avgSigns 0 (fun σ => (eval p σ) ^ 4) = p.const ^ 4 := by
        have : (fun σ : Fin 0 → Bool => (eval p σ) ^ 4)
                = fun _ => p.const ^ 4 := by funext σ; rw [hev]
        rw [this, avgSigns_const]
      rw [hL2, hL4]
      nlinarith [sq_nonneg p.const, sq_nonneg (p.const ^ 2)]
  | succ n ih =>
      -- Abbreviations.
      set G := fun σ : Fin n → Bool => eval p.tail σ with hGdef
      set H := fun σ : Fin n → Bool => evalDeg1 p.lastSlice σ with hHdef
      set EG2 := avgSigns n (fun σ => (G σ) ^ 2)
      set EH2 := avgSigns n (fun σ => (H σ) ^ 2)
      set EG4 := avgSigns n (fun σ => (G σ) ^ 4)
      set EH4 := avgSigns n (fun σ => (H σ) ^ 4)
      set EGH := avgSigns n (fun σ => (G σ) ^ 2 * (H σ) ^ 2)
      -- Nonnegativity (small helper to avoid repetition).
      have avgNn : ∀ φ : (Fin n → Bool) → ℝ,
          (∀ σ, 0 ≤ φ σ) → 0 ≤ avgSigns n φ := by
        intro φ hφ
        unfold avgSigns
        apply div_nonneg
        · exact Finset.sum_nonneg (fun σ _ => hφ σ)
        · positivity
      have hEG2_nn : 0 ≤ EG2 :=
        avgNn _ (fun σ => sq_nonneg _)
      have hEH2_nn : 0 ≤ EH2 :=
        avgNn _ (fun σ => sq_nonneg _)
      have hEG4_nn : 0 ≤ EG4 := by
        refine avgNn _ (fun σ => ?_)
        have h4 : (G σ) ^ 4 = ((G σ) ^ 2) ^ 2 := by ring
        rw [h4]; exact sq_nonneg _
      have hEH4_nn : 0 ≤ EH4 := by
        refine avgNn _ (fun σ => ?_)
        have h4 : (H σ) ^ 4 = ((H σ) ^ 2) ^ 2 := by ring
        rw [h4]; exact sq_nonneg _
      have hEGH_nn : 0 ≤ EGH := by
        refine avgNn _ (fun σ => ?_); positivity
      -- Compute E[(eval p)²] over n+1 vars in terms of EG2, EH2.
      have hL2 :
          avgSigns (n + 1) (fun τ => (eval p τ) ^ 2) = EG2 + EH2 := by
        rw [avgSigns_split_last]
        have hpoint :
            (fun σ : Fin n → Bool =>
              ((∑ b : Bool,
                  (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2) / 2 : ℝ))
              = (fun σ : Fin n → Bool => (G σ) ^ 2 + (H σ) ^ 2) := by
          funext σ
          have hb :
              ∀ b : Bool,
                (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2
                  = (G σ + rad b * H σ) ^ 2 := by
            intro b; rw [eval_snoc_decomp]
          rw [show (∑ b : Bool,
                    (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 2)
                = ∑ b : Bool, (G σ + rad b * H σ) ^ 2 from
              Finset.sum_congr rfl (fun b _ => hb b)]
          simp [LeaHadamard.Defs.rad]; ring
        rw [hpoint, avgSigns_add]
      -- Compute E[(eval p)⁴] over n+1 vars in terms of EG4, EGH, EH4.
      have hL4 :
          avgSigns (n + 1) (fun τ => (eval p τ) ^ 4) = EG4 + 6 * EGH + EH4 := by
        rw [avgSigns_split_last]
        have hpoint :
            (fun σ : Fin n → Bool =>
              ((∑ b : Bool,
                  (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 4) / 2 : ℝ))
              = (fun σ : Fin n → Bool =>
                  (G σ) ^ 4 + 6 * ((G σ) ^ 2 * (H σ) ^ 2) + (H σ) ^ 4) := by
          funext σ
          have hb :
              ∀ b : Bool,
                (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 4
                  = (G σ + rad b * H σ) ^ 4 := by
            intro b; rw [eval_snoc_decomp]
          rw [show (∑ b : Bool,
                    (eval p (Fin.snoc (α := fun _ => Bool) σ b)) ^ 4)
                = ∑ b : Bool, (G σ + rad b * H σ) ^ 4 from
              Finset.sum_congr rfl (fun b _ => hb b)]
          simp [LeaHadamard.Defs.rad]; ring
        rw [hpoint]
        -- Linearity.
        rw [show (fun σ : Fin n → Bool =>
                    (G σ) ^ 4 + 6 * ((G σ) ^ 2 * (H σ) ^ 2) + (H σ) ^ 4)
              = (fun σ : Fin n → Bool =>
                  ((G σ) ^ 4 + 6 * ((G σ) ^ 2 * (H σ) ^ 2)) + (H σ) ^ 4) from rfl,
            avgSigns_add,
            show (fun σ : Fin n → Bool =>
                    (G σ) ^ 4 + 6 * ((G σ) ^ 2 * (H σ) ^ 2))
              = (fun σ : Fin n → Bool =>
                  (G σ) ^ 4 + (fun τ => 6 * ((G τ) ^ 2 * (H τ) ^ 2)) σ) from rfl,
            avgSigns_add, avgSigns_mul_const_left]
      -- Inductive bound on G (degree-2 in n vars).
      have hG : EG4 ≤ 81 * EG2 ^ 2 := ih p.tail
      -- Linear bound on H (degree-1 in n vars).
      have hH : EH4 ≤ 9 * EH2 ^ 2 := hc_degree1_fourth p.lastSlice
      -- Cauchy–Schwarz on (G²)·(H²).
      have hCS_raw :
          EGH ^ 2 ≤ EG4 * EH4 := by
        have := avgSigns_mul_sq_le (fun σ : Fin n → Bool => (G σ) ^ 2)
          (fun σ : Fin n → Bool => (H σ) ^ 2)
        -- This gives: (avg of G²·H²)² ≤ (avg of G⁴) · (avg of H⁴).
        have hG4eq :
            avgSigns n (fun σ : Fin n → Bool => ((G σ) ^ 2) ^ 2)
              = EG4 := by
          show avgSigns n (fun σ : Fin n → Bool => ((G σ) ^ 2) ^ 2) = EG4
          have : (fun σ : Fin n → Bool => ((G σ) ^ 2) ^ 2)
                  = (fun σ => (G σ) ^ 4) := by funext σ; ring
          rw [this]
        have hH4eq :
            avgSigns n (fun σ : Fin n → Bool => ((H σ) ^ 2) ^ 2)
              = EH4 := by
          have : (fun σ : Fin n → Bool => ((H σ) ^ 2) ^ 2)
                  = (fun σ => (H σ) ^ 4) := by funext σ; ring
          rw [this]
        rw [hG4eq, hH4eq] at this
        exact this
      -- From `EGH² ≤ EG4·EH4 ≤ 81·EG2² · 9·EH2² = 729·(EG2·EH2)²`,
      -- and `EGH ≥ 0`, we get `EGH ≤ 27·EG2·EH2`.
      have hEG2EH2_nn : 0 ≤ EG2 * EH2 := mul_nonneg hEG2_nn hEH2_nn
      have hProdBound : EG4 * EH4 ≤ 729 * (EG2 * EH2) ^ 2 := by
        have h1 : EG4 * EH4 ≤ (81 * EG2 ^ 2) * EH4 :=
          mul_le_mul_of_nonneg_right hG hEH4_nn
        have hC2 : 0 ≤ 81 * EG2 ^ 2 := by positivity
        have h2 : (81 * EG2 ^ 2) * EH4 ≤ (81 * EG2 ^ 2) * (9 * EH2 ^ 2) :=
          mul_le_mul_of_nonneg_left hH hC2
        have h3 : (81 * EG2 ^ 2) * (9 * EH2 ^ 2) = 729 * (EG2 * EH2) ^ 2 := by ring
        linarith
      have hEGH_bound : EGH ≤ 27 * (EG2 * EH2) := by
        -- From EGH² ≤ 729 (EG2 EH2)² = (27 EG2 EH2)² and both nonneg.
        have h1 : EGH ^ 2 ≤ (27 * (EG2 * EH2)) ^ 2 := by
          have : (27 * (EG2 * EH2)) ^ 2 = 729 * (EG2 * EH2) ^ 2 := by ring
          rw [this]; linarith
        have h27 : 0 ≤ 27 * (EG2 * EH2) := by positivity
        exact abs_le_of_sq_le_sq' h1 h27 |>.2
      -- Now combine: E[p⁴] = EG4 + 6·EGH + EH4
      --   ≤ 81·EG2² + 6·27·EG2·EH2 + 9·EH2²
      --   ≤ 81·EG2² + 162·EG2·EH2 + 81·EH2²
      --   = 81·(EG2 + EH2)²
      --   = 81·(E[p²])².
      rw [hL2, hL4]
      have hCombine :
          EG4 + 6 * EGH + EH4 ≤ 81 * (EG2 + EH2) ^ 2 := by
        nlinarith [hG, hH, hEGH_bound, sq_nonneg (EG2 - EH2),
                   sq_nonneg EG2, sq_nonneg EH2, hEG2_nn, hEH2_nn,
                   mul_nonneg hEG2_nn hEH2_nn]
      exact hCombine

end LeaHadamard.Hypercontractive
