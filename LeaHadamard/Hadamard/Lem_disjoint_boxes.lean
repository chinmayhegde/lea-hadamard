/-
# Disjointness of Λ-translated boxes

For each `λ ∈ Λ ⊂ Λ₀`, embedded into `(Edge n → ℝ)` via
`Lambda_0.toReal`, the open box `λ + (-δ, δ)^d` (taken mod `2π` in
each coordinate) of radius `0 < δ < π/4` are pairwise disjoint as
subsets of the torus `𝕋^d = (ℝ/2πℤ)^Edge`.

This is a leaf-node fact: it does not depend on any earlier
project lemma, only on the lattice values being multiples of `π/2`
in `{0, π/2, π, 3π/2}`.
-/

import Mathlib
import LeaHadamard.Defs
import LeaHadamard.Hadamard.Lambda

open scoped BigOperators
open Finset Real

namespace LeaHadamard.Hadamard

/-- The (open) δ-box around a `Λ₀`-point `λ`, taken in the torus
`𝕋^d = (ℝ/2πℤ)^Edge`. A point `x : Edge n → ℝ` lies in the box iff,
for every edge `e`, some integer translate `x e − 2π k` is within
`δ` of the embedded coordinate `(λ_e : ℕ)·π/2`. -/
def edgeBox (n : ℕ) (delta : ℝ) (lam : Lambda_0 n) : Set (Edge n → ℝ) :=
  {x | ∀ e : Edge n, ∃ k : ℤ, |x e - Lambda_0.toReal lam e - 2 * Real.pi * k| < delta}

/-! ## A lattice-spacing lemma.

If `a, b ∈ {0,1,2,3}` are distinct, then `|a·π/2 − b·π/2 − 2π·k| ≥ π/2`
for every integer `k`. -/

private lemma lattice_gap (a b : Fin 4) (hab : a ≠ b) (k : ℤ) :
    Real.pi / 2 ≤
      |((a : ℕ) : ℝ) * (Real.pi / 2) - ((b : ℕ) : ℝ) * (Real.pi / 2)
        - 2 * Real.pi * k| := by
  -- Write everything in terms of the integer `m := (a : ℤ) - (b : ℤ) - 4*k`.
  set α : ℝ := ((a : ℕ) : ℝ) * (Real.pi / 2) - ((b : ℕ) : ℝ) * (Real.pi / 2)
                - 2 * Real.pi * k with hα
  -- Key algebraic identity: α = (π/2) * ((a : ℤ) - (b : ℤ) - 4*k).
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ2_pos : (0 : ℝ) < Real.pi / 2 := by positivity
  -- m as a real number
  set m : ℤ := (a : ℤ) - (b : ℤ) - 4 * k with hm_def
  have hα_eq : α = (Real.pi / 2) * (m : ℝ) := by
    simp only [hα, hm_def]
    push_cast
    ring
  rw [hα_eq, abs_mul, abs_of_pos hπ2_pos]
  -- Need: π/2 ≤ (π/2) * |m|, i.e., 1 ≤ |m|.
  have hm_ne : m ≠ 0 := by
    intro h0
    -- m = 0 ⇒ (a : ℤ) - (b : ℤ) = 4*k.
    have h1 : (a : ℤ) - (b : ℤ) = 4 * k := by
      have := h0
      simp [hm_def] at this
      linarith
    -- But (a : ℤ), (b : ℤ) ∈ [0,4) so |a - b| ≤ 3 < 4.
    have ha : (a : ℤ) < 4 := by exact_mod_cast a.isLt
    have hb : (b : ℤ) < 4 := by exact_mod_cast b.isLt
    have ha' : (0 : ℤ) ≤ (a : ℤ) := by positivity
    have hb' : (0 : ℤ) ≤ (b : ℤ) := by positivity
    -- So 4*k ∈ (-4, 4), hence k = 0, hence a = b, contradiction.
    have hk0 : k = 0 := by
      have h2 : -4 < 4 * k := by linarith
      have h3 : 4 * k < 4 := by linarith
      omega
    subst hk0
    have : (a : ℤ) = (b : ℤ) := by linarith
    have : a = b := Fin.ext (by exact_mod_cast this)
    exact hab this
  have hm_abs : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    have h2 : ((|m| : ℤ) : ℝ) = |(m : ℝ)| := by push_cast; rfl
    have h3 : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
    linarith [h3, h2.symm ▸ h3]
  -- Conclude.
  calc Real.pi / 2
      = Real.pi / 2 * 1 := by ring
    _ ≤ Real.pi / 2 * |(m : ℝ)| := by
        exact mul_le_mul_of_nonneg_left hm_abs (le_of_lt hπ2_pos)

/-- **Disjointness of Λ-translated boxes.** For `0 < δ < π/4`, the
family `{edgeBox n δ λ}_{λ ∈ Λ n}` is pairwise disjoint. -/
theorem translated_edgeBoxes_disjoint
    {n : ℕ} {delta : ℝ} (_hδ_pos : 0 < delta) (hδ_lt : delta < Real.pi / 4)
    {lam lam' : Lambda_0 n}
    (_hlam : lam ∈ Lambda n) (_hlam' : lam' ∈ Lambda n)
    (hne : lam ≠ lam') :
    edgeBox n delta lam ∩ edgeBox n delta lam' = ∅ := by
  -- Pick a witness edge where `lam` and `lam'` differ.
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  -- Find an edge where the two lattice points differ.
  have : ∃ e : Edge n, lam e ≠ lam' e := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨e, he⟩ := this
  -- Extract translation integers k, k' from membership.
  obtain ⟨k, hk⟩ := hx1 e
  obtain ⟨k', hk'⟩ := hx2 e
  -- Combine: |2π(k − k') − ((a − b)·π/2)| < 2δ < π/2, contradicting `lattice_gap`.
  -- We will bound `|α|` where α := a·π/2 − b·π/2 − 2π·(k' − k).
  have habs :
      |((lam e : ℕ) : ℝ) * (Real.pi / 2) - ((lam' e : ℕ) : ℝ) * (Real.pi / 2)
          - 2 * Real.pi * ((k' - k : ℤ) : ℝ)| < 2 * delta := by
    -- Cast the integer `k' − k`.
    have hcast : ((k' - k : ℤ) : ℝ) = (k' : ℝ) - (k : ℝ) := by push_cast; rfl
    rw [hcast]
    -- Triangle inequality with a clean sign.
    have key :
        -(((lam e : ℕ) : ℝ) * (Real.pi / 2) - ((lam' e : ℕ) : ℝ) * (Real.pi / 2)
            - 2 * Real.pi * ((k' : ℝ) - (k : ℝ))) =
          (x e - ((lam e : ℕ) : ℝ) * (Real.pi / 2) - 2 * Real.pi * k)
            - (x e - ((lam' e : ℕ) : ℝ) * (Real.pi / 2) - 2 * Real.pi * k') := by
      ring
    have step :
        |((lam e : ℕ) : ℝ) * (Real.pi / 2) - ((lam' e : ℕ) : ℝ) * (Real.pi / 2)
            - 2 * Real.pi * ((k' : ℝ) - (k : ℝ))|
          ≤ |x e - ((lam e : ℕ) : ℝ) * (Real.pi / 2) - 2 * Real.pi * k|
            + |x e - ((lam' e : ℕ) : ℝ) * (Real.pi / 2) - 2 * Real.pi * k'| := by
      rw [show |((lam e : ℕ) : ℝ) * (Real.pi / 2) - ((lam' e : ℕ) : ℝ) * (Real.pi / 2)
            - 2 * Real.pi * ((k' : ℝ) - (k : ℝ))|
          = |-((((lam e : ℕ) : ℝ) * (Real.pi / 2) - ((lam' e : ℕ) : ℝ) * (Real.pi / 2)
              - 2 * Real.pi * ((k' : ℝ) - (k : ℝ))))| from (abs_neg _).symm,
            key]
      exact abs_sub _ _
    -- Note: `Lambda_0.toReal lam e = (lam e : ℕ) · (π/2)`.
    have eq1 : Lambda_0.toReal lam e = ((lam e : ℕ) : ℝ) * (Real.pi / 2) := rfl
    have eq2 : Lambda_0.toReal lam' e = ((lam' e : ℕ) : ℝ) * (Real.pi / 2) := rfl
    rw [eq1] at hk
    rw [eq2] at hk'
    linarith
  -- Combine with the lattice gap lemma at `k' − k`.
  have hgap := lattice_gap (lam e) (lam' e) he (k' - k)
  have h2δ_lt : 2 * delta < Real.pi / 2 := by linarith
  linarith

end LeaHadamard.Hadamard
