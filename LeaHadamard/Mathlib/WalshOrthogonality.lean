/-
# Walsh-monomial orthogonality at general degree (Stage 8a)

This file extends the moment-layer infrastructure with general-degree
Walsh-monomial orthogonality:

* `chi S σ = ∏_{i ∈ S} rad (σ i)` — the Walsh character indexed by a
  finset `S ⊆ Fin n`;
* `avgSigns_chi_eq_zero_of_nonempty` — the first moment vanishes for
  non-empty `S` (proved via the bit-flip involution at any chosen index
  `i ∈ S`);
* `chi_mul_chi` — the product of two Walsh characters is the Walsh
  character of their symmetric difference (using `rad b * rad b = 1`);
* `avgSigns_chi_mul_chi` — orthogonality:
  `avgSigns n (χ_S · χ_T) = if S = T then 1 else 0`;
* `avgSigns_rad_four_*` — four specializations of the four-index product
  needed for `lem:ordered-cycle` (`fourth_cumulant_identity`).

This file is purely additive: it does not modify
`LeaHadamard/Mathlib/Hypercontractive.lean`.
-/

import Mathlib
import LeaHadamard.Defs
import LeaHadamard.Mathlib.SignAverage

open scoped BigOperators
open Finset

namespace LeaHadamard.WalshOrthogonality

/-- Local abbreviation: use `LeaHadamard.Defs.rad` as the Rademacher sign.
We do not open `LeaHadamard.Defs` or `LeaHadamard.SignAverage` to avoid the
ambiguous-`rad` clash (both modules expose a `rad` symbol). -/
private abbrev rad : Bool → ℝ := LeaHadamard.Defs.rad

/-- Local abbreviation for `avgSigns`. -/
private noncomputable abbrev avgSigns (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  LeaHadamard.SignAverage.avgSigns n f

/-! ## The Walsh character -/

/-- The Walsh character indexed by a finset `S ⊆ Fin n`:
`χ S σ = ∏_{i ∈ S} rad (σ i)`. -/
noncomputable def chi {n : ℕ} (S : Finset (Fin n)) (σ : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, rad (σ i)

@[simp] lemma chi_empty {n : ℕ} (σ : Fin n → Bool) :
    chi (∅ : Finset (Fin n)) σ = 1 := by
  simp [chi]

/-! ## Bit-flip involution -/

/-- Flip the `i`-th coordinate of a Boolean vector. -/
noncomputable def flipBit {n : ℕ} (i : Fin n) (σ : Fin n → Bool) : Fin n → Bool :=
  Function.update σ i (! σ i)

lemma flipBit_apply_self {n : ℕ} (i : Fin n) (σ : Fin n → Bool) :
    flipBit i σ i = ! σ i := by
  unfold flipBit
  simp

lemma flipBit_apply_ne {n : ℕ} (i : Fin n) (σ : Fin n → Bool)
    {j : Fin n} (hj : j ≠ i) : flipBit i σ j = σ j := by
  unfold flipBit
  rw [Function.update_of_ne hj]

lemma flipBit_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (flipBit i) := by
  intro σ
  funext j
  by_cases hj : j = i
  · subst hj
    rw [flipBit_apply_self, flipBit_apply_self, Bool.not_not]
  · rw [flipBit_apply_ne i (flipBit i σ) hj, flipBit_apply_ne i σ hj]

/-- The bit-flip involution as an equivalence on `Fin n → Bool`. -/
noncomputable def flipBitEquiv {n : ℕ} (i : Fin n) :
    (Fin n → Bool) ≃ (Fin n → Bool) :=
  Function.Involutive.toPerm (flipBit i) (flipBit_involutive i)

@[simp] lemma flipBitEquiv_apply {n : ℕ} (i : Fin n) (σ : Fin n → Bool) :
    flipBitEquiv i σ = flipBit i σ := rfl

/-! ## How `chi` transforms under the bit-flip -/

lemma chi_flipBit_of_mem {n : ℕ} (S : Finset (Fin n)) {i : Fin n}
    (hi : i ∈ S) (σ : Fin n → Bool) :
    chi S (flipBit i σ) = - chi S σ := by
  classical
  unfold chi
  -- Split off the factor at `i`. Use `prod_erase_mul`.
  have h1 :
      (∏ j ∈ S, rad (flipBit i σ j))
        = (∏ j ∈ S.erase i, rad (flipBit i σ j))
            * rad (flipBit i σ i) := by
    rw [Finset.prod_erase_mul S _ hi]
  have h2 :
      (∏ j ∈ S, rad (σ j))
        = (∏ j ∈ S.erase i, rad (σ j)) * rad (σ i) := by
    rw [Finset.prod_erase_mul S _ hi]
  -- Outside `i`, flipBit acts as identity.
  have hOut :
      (∏ j ∈ S.erase i, rad (flipBit i σ j))
        = ∏ j ∈ S.erase i, rad (σ j) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [flipBit_apply_ne i σ hj']
  -- At `i`, flipBit toggles the sign.
  have hAt : rad (flipBit i σ i) = - rad (σ i) := by
    rw [flipBit_apply_self]
    exact LeaHadamard.Defs.rad_not (σ i)
  rw [h1, h2, hOut, hAt]
  ring

/-! ## Vanishing first moment for non-empty `S` -/

/-- The Walsh character with non-empty index set has zero average over
uniform Rademacher signs. -/
lemma avgSigns_chi_eq_zero_of_nonempty {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    avgSigns n (chi S) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hS
  -- Reindex the sum by the involution and use chi (flip) = -chi.
  show LeaHadamard.SignAverage.avgSigns n (chi S) = 0
  unfold LeaHadamard.SignAverage.avgSigns
  have hsum : (∑ σ : Fin n → Bool, chi S σ) = 0 := by
    have hreindex :
        (∑ σ : Fin n → Bool, chi S σ)
          = ∑ σ : Fin n → Bool, chi S ((flipBitEquiv i) σ) := by
      exact (Fintype.sum_equiv (flipBitEquiv i)
        (fun σ : Fin n → Bool => chi S ((flipBitEquiv i) σ))
        (fun σ : Fin n → Bool => chi S σ)
        (by intro σ; rfl)).symm
    have hneg :
        (∑ σ : Fin n → Bool, chi S ((flipBitEquiv i) σ))
          = - (∑ σ : Fin n → Bool, chi S σ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro σ _
      rw [flipBitEquiv_apply, chi_flipBit_of_mem S hi σ]
    have heq : (∑ σ : Fin n → Bool, chi S σ)
        = - (∑ σ : Fin n → Bool, chi S σ) := hreindex.trans hneg
    linarith
  rw [hsum]
  simp

/-! ## Product reduction `chi S · chi T = chi (S △ T)` -/

/-- The product of two Walsh characters is the character of the symmetric
difference. The cancellation comes from `rad b * rad b = 1` on shared
indices. -/
lemma chi_mul_chi {n : ℕ} (S T : Finset (Fin n)) (σ : Fin n → Bool) :
    chi S σ * chi T σ = chi (symmDiff S T) σ := by
  classical
  -- Decompose S = (S ∩ T) ∪ (S \ T) and T = (S ∩ T) ∪ (T \ S),
  -- both disjoint unions. Then χ_S · χ_T = (∏_{S ∩ T} rad²) · χ_{S \ T} · χ_{T \ S}
  --                                       = 1 · χ_{S △ T}.
  have hSdec : S = (S ∩ T) ∪ (S \ T) := by
    ext x; constructor
    · intro hx
      by_cases hxT : x ∈ T
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxT⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxT⟩))
    · intro hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_inter.mp h).1
      · exact (Finset.mem_sdiff.mp h).1
  have hSdis : Disjoint (S ∩ T) (S \ T) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hTdec : T = (S ∩ T) ∪ (T \ S) := by
    ext x; constructor
    · intro hx
      by_cases hxS : x ∈ S
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxS, hx⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxS⟩))
    · intro hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_inter.mp h).2
      · exact (Finset.mem_sdiff.mp h).1
  have hTdis : Disjoint (S ∩ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).1
  -- Symmetric-difference decomposition (disjoint union).
  have hSDdec : symmDiff S T = (S \ T) ∪ (T \ S) := by
    rfl
  have hSDdis : Disjoint (S \ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1
  -- Compute each product over the disjoint decomposition.
  have hχS :
      chi S σ
        = (∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ S \ T, rad (σ i) := by
    show (∏ i ∈ S, rad (σ i))
        = (∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ S \ T, rad (σ i)
    conv_lhs => rw [hSdec]
    exact Finset.prod_union hSdis
  have hχT :
      chi T σ
        = (∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ T \ S, rad (σ i) := by
    show (∏ i ∈ T, rad (σ i))
        = (∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ T \ S, rad (σ i)
    conv_lhs => rw [hTdec]
    exact Finset.prod_union hTdis
  have hχSD :
      chi (symmDiff S T) σ
        = (∏ i ∈ S \ T, rad (σ i)) * ∏ i ∈ T \ S, rad (σ i) := by
    show (∏ i ∈ symmDiff S T, rad (σ i))
        = (∏ i ∈ S \ T, rad (σ i)) * ∏ i ∈ T \ S, rad (σ i)
    rw [hSDdec]
    exact Finset.prod_union hSDdis
  -- Cancel the (S ∩ T) factor using rad² = 1.
  have hRadSq :
      (∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ S ∩ T, rad (σ i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    have hpw : ∀ i ∈ S ∩ T, rad (σ i) * rad (σ i) = 1 := by
      intro i _; exact LeaHadamard.Defs.rad_sq (σ i)
    rw [Finset.prod_congr rfl hpw]
    exact Finset.prod_const_one
  -- Now compute.
  rw [hχS, hχT, hχSD]
  calc
    ((∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ S \ T, rad (σ i))
        * ((∏ i ∈ S ∩ T, rad (σ i)) * ∏ i ∈ T \ S, rad (σ i))
        = ((∏ i ∈ S ∩ T, rad (σ i)) * (∏ i ∈ S ∩ T, rad (σ i)))
            * ((∏ i ∈ S \ T, rad (σ i)) * (∏ i ∈ T \ S, rad (σ i))) := by ring
    _ = 1 * ((∏ i ∈ S \ T, rad (σ i)) * (∏ i ∈ T \ S, rad (σ i))) := by
          rw [hRadSq]
    _ = (∏ i ∈ S \ T, rad (σ i)) * (∏ i ∈ T \ S, rad (σ i)) := by ring

/-! ## Orthogonality -/

/-- Orthogonality of Walsh characters under the uniform-sign average. -/
theorem avgSigns_chi_mul_chi {n : ℕ} (S T : Finset (Fin n)) :
    avgSigns n (fun σ => chi S σ * chi T σ)
      = if S = T then 1 else 0 := by
  classical
  -- Rewrite the integrand as `chi (symmDiff S T)`.
  have hfun :
      (fun σ : Fin n → Bool => chi S σ * chi T σ)
        = (fun σ : Fin n → Bool => chi (symmDiff S T) σ) := by
    funext σ; exact chi_mul_chi S T σ
  rw [hfun]
  by_cases hST : S = T
  · -- S = T: symmDiff is empty, integrand is 1.
    subst hST
    have hSD : symmDiff S S = (∅ : Finset (Fin n)) := by
      simp [symmDiff_self]
    rw [hSD]
    have : (fun σ : Fin n → Bool => chi (∅ : Finset (Fin n)) σ)
            = fun _ => (1 : ℝ) := by
      funext σ; exact chi_empty σ
    rw [this]
    show LeaHadamard.SignAverage.avgSigns n (fun _ => (1 : ℝ)) = _
    rw [LeaHadamard.SignAverage.avgSigns_const]
    rw [if_pos rfl]
  · -- S ≠ T: symmDiff is non-empty, integrand averages to 0.
    have hSDne : symmDiff S T ≠ ∅ := by
      intro h
      apply hST
      ext x
      constructor
      · intro hxS
        by_contra hxT
        have hxSD : x ∈ symmDiff S T := by
          rw [Finset.mem_symmDiff]
          exact Or.inl ⟨hxS, hxT⟩
        rw [h] at hxSD
        exact (Finset.notMem_empty _) hxSD
      · intro hxT
        by_contra hxS
        have hxSD : x ∈ symmDiff S T := by
          rw [Finset.mem_symmDiff]
          exact Or.inr ⟨hxT, hxS⟩
        rw [h] at hxSD
        exact (Finset.notMem_empty _) hxSD
    have hSDnempty : (symmDiff S T).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hSDne
    rw [avgSigns_chi_eq_zero_of_nonempty (symmDiff S T) hSDnempty]
    rw [if_neg hST]

/-! ## Specializations of the four-index product -/

/-- Case "all four equal": the average is `1`. -/
lemma avgSigns_rad_four_same {n : ℕ} (i : Fin n) :
    avgSigns n (fun σ : Fin n → Bool =>
      LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
        * LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)) = 1 := by
  -- The integrand is identically 1.
  have hpt : ∀ σ : Fin n → Bool,
      LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
        * LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i) = 1 := by
    intro σ
    have h2 : LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i) = 1 :=
      LeaHadamard.Defs.rad_sq (σ i)
    nlinarith [h2]
  have hfun :
      (fun σ : Fin n → Bool =>
          LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
            * LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i))
        = (fun _ : Fin n → Bool => (1 : ℝ)) := by
    funext σ; exact hpt σ
  rw [hfun]
  show LeaHadamard.SignAverage.avgSigns n (fun _ => (1 : ℝ)) = 1
  exact LeaHadamard.SignAverage.avgSigns_const 1

/-- Case "two distinct pairs": the average is `1`. -/
lemma avgSigns_rad_two_pairs {n : ℕ} (i j : Fin n) (_hij : i ≠ j) :
    avgSigns n (fun σ : Fin n → Bool =>
      LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ j)
        * LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ j)) = 1 := by
  have hpt : ∀ σ : Fin n → Bool,
      LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ j)
        * LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ j) = 1 := by
    intro σ
    have hi2 : LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i) = 1 :=
      LeaHadamard.Defs.rad_sq (σ i)
    have hj2 : LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ j) = 1 :=
      LeaHadamard.Defs.rad_sq (σ j)
    nlinarith [hi2, hj2]
  have hfun :
      (fun σ : Fin n → Bool =>
          LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ j)
            * LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ j))
        = (fun _ : Fin n → Bool => (1 : ℝ)) := by
    funext σ; exact hpt σ
  rw [hfun]
  show LeaHadamard.SignAverage.avgSigns n (fun _ => (1 : ℝ)) = 1
  exact LeaHadamard.SignAverage.avgSigns_const 1

/-! ### Helper: reduce a product of `rad`s to `chi` of the appropriate finset. -/

/-- The 4-fold product `rad σ_a · rad σ_b · rad σ_c · rad σ_d` equals
`chi {a, b, c, d}` evaluated at `σ` *whenever* all four indices are
distinct (so the finset has cardinality 4). -/
private lemma rad_four_eq_chi_of_distinct {n : ℕ}
    (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (σ : Fin n → Bool) :
    LeaHadamard.Defs.rad (σ a) * LeaHadamard.Defs.rad (σ b)
      * LeaHadamard.Defs.rad (σ c) * LeaHadamard.Defs.rad (σ d)
      = chi ({a, b, c, d} : Finset (Fin n)) σ := by
  classical
  -- Build {a,b,c,d} as iterated insert with explicit nonmembership facts.
  show LeaHadamard.Defs.rad (σ a) * LeaHadamard.Defs.rad (σ b)
        * LeaHadamard.Defs.rad (σ c) * LeaHadamard.Defs.rad (σ d)
        = ∏ i ∈ ({a, b, c, d} : Finset (Fin n)), rad (σ i)
  -- Compute ∏ over {d}.
  have step1 : (∏ i ∈ ({d} : Finset (Fin n)), rad (σ i))
                  = rad (σ d) := by
    simp
  -- Now insert c into {d}.
  have hc_notin_d : c ∉ ({d} : Finset (Fin n)) := by
    intro h; rw [Finset.mem_singleton] at h; exact hcd h
  have step2 : (∏ i ∈ (insert c ({d} : Finset (Fin n))), rad (σ i))
                  = rad (σ c) * rad (σ d) := by
    rw [Finset.prod_insert hc_notin_d, step1]
  -- Now insert b into {c, d}.
  have hb_notin_cd : b ∉ (insert c ({d} : Finset (Fin n))) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hbc h
    · rw [Finset.mem_singleton] at h; exact hbd h
  have step3 : (∏ i ∈ (insert b (insert c ({d} : Finset (Fin n)))), rad (σ i))
                  = rad (σ b) * (rad (σ c) * rad (σ d)) := by
    rw [Finset.prod_insert hb_notin_cd, step2]
  -- Now insert a into {b, c, d}.
  have ha_notin_bcd : a ∉ (insert b (insert c ({d} : Finset (Fin n)))) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hab h
    rcases Finset.mem_insert.mp h with h | h
    · exact hac h
    · rw [Finset.mem_singleton] at h; exact had h
  have step4 :
      (∏ i ∈ (insert a (insert b (insert c ({d} : Finset (Fin n))))), rad (σ i))
        = rad (σ a) * (rad (σ b) * (rad (σ c) * rad (σ d))) := by
    rw [Finset.prod_insert ha_notin_bcd, step3]
  rw [show ({a, b, c, d} : Finset (Fin n))
        = insert a (insert b (insert c ({d} : Finset (Fin n)))) from rfl,
      step4]
  ring

/-- Case "all distinct": the average is `0`. -/
lemma avgSigns_rad_four_distinct {n : ℕ}
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    avgSigns n (fun σ : Fin n → Bool =>
      LeaHadamard.Defs.rad (σ a) * LeaHadamard.Defs.rad (σ b)
        * LeaHadamard.Defs.rad (σ c) * LeaHadamard.Defs.rad (σ d)) = 0 := by
  classical
  have hfun :
      (fun σ : Fin n → Bool =>
          LeaHadamard.Defs.rad (σ a) * LeaHadamard.Defs.rad (σ b)
            * LeaHadamard.Defs.rad (σ c) * LeaHadamard.Defs.rad (σ d))
        = (fun σ : Fin n → Bool => chi ({a, b, c, d} : Finset (Fin n)) σ) := by
    funext σ
    exact rad_four_eq_chi_of_distinct a b c d hab hac had hbc hbd hcd σ
  rw [hfun]
  have hne : ({a, b, c, d} : Finset (Fin n)).Nonempty := ⟨a, by simp⟩
  exact avgSigns_chi_eq_zero_of_nonempty _ hne

/-! ### Helper for the "one repeated" case -/

/-- When `i, j, k` are pairwise distinct, the product
`rad σ_i · rad σ_i · rad σ_j · rad σ_k` equals `chi {j, k}`,
since `rad σ_i · rad σ_i = 1`. -/
private lemma rad_three_one_match_eq_chi {n : ℕ}
    (i j k : Fin n) (_hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k)
    (σ : Fin n → Bool) :
    LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
      * LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k)
      = chi ({j, k} : Finset (Fin n)) σ := by
  classical
  show LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
        * LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k)
        = ∏ x ∈ ({j, k} : Finset (Fin n)), rad (σ x)
  have step1 : (∏ x ∈ ({k} : Finset (Fin n)), rad (σ x)) = rad (σ k) := by
    simp
  have hj_notin_k : j ∉ ({k} : Finset (Fin n)) := by
    intro h; rw [Finset.mem_singleton] at h; exact hjk h
  have step2 :
      (∏ x ∈ (insert j ({k} : Finset (Fin n))), rad (σ x))
        = rad (σ j) * rad (σ k) := by
    rw [Finset.prod_insert hj_notin_k, step1]
  have hii : LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i) = 1 :=
    LeaHadamard.Defs.rad_sq (σ i)
  rw [show ({j, k} : Finset (Fin n)) = insert j ({k} : Finset (Fin n)) from rfl,
      step2]
  -- (rad i · rad i) · (rad j) · (rad k) = 1 · (rad j · rad k) = rad j · rad k.
  calc
    LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
        * LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k)
        = (LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i))
            * (LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k)) := by ring
    _ = 1 * (LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k)) := by rw [hii]
    _ = LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k) := by ring

/-- Case "one repeated, two distinct": the average is `0`. -/
lemma avgSigns_rad_three_distinct_one_match {n : ℕ}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    avgSigns n (fun σ : Fin n → Bool =>
      LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
        * LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k)) = 0 := by
  classical
  have hfun :
      (fun σ : Fin n → Bool =>
          LeaHadamard.Defs.rad (σ i) * LeaHadamard.Defs.rad (σ i)
            * LeaHadamard.Defs.rad (σ j) * LeaHadamard.Defs.rad (σ k))
        = (fun σ : Fin n → Bool => chi ({j, k} : Finset (Fin n)) σ) := by
    funext σ
    exact rad_three_one_match_eq_chi i j k hij hik hjk σ
  rw [hfun]
  have hne : ({j, k} : Finset (Fin n)).Nonempty := ⟨j, by simp⟩
  exact avgSigns_chi_eq_zero_of_nonempty _ hne

end LeaHadamard.WalshOrthogonality
