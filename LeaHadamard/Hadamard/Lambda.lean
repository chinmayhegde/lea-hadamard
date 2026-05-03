/-
# The half-π lattice Λ₀ and the sublattice Λ

We formalize the lattice objects used in the analysis of ψ at lattice
points (cf. Davis, arXiv:2603.30013; blueprint chapter `lambda_facts`).

## Setup

Let `n ≥ 2` and `d = C(n, 2)`. The edges of `K_n` are the ordered pairs
`Edge n := { (i, j) : Fin n × Fin n // i < j }`. A `Λ₀`-point assigns
each edge a value in `(π/2)·ℤ / (2π·ℤ) ≅ ℤ/4`; we model `Λ₀ n`
combinatorially as `Edge n → Fin 4`. The geometric embedding is
`Lambda_0.toReal : Λ₀ n → (Edge n → ℝ)`, `k ↦ (k : ℕ) · π/2`.

## Mod-2 reduction

For `λ ∈ Λ₀ n`, the *mod-π* reduction `λ^{(2)} : Edge n → Bool` records
`(λ^{(2)})_e = true` iff `(λ_e : Fin 4)` is odd, i.e.
`λ_e (mod 2π) ∈ {π/2, 3π/2}`.

## The sublattice Λ

We define `Λ` by the linear-algebraic *incidence-zero* condition:
the mod-2 incidence sum (in `ZMod 2`) at every vertex vanishes.
The Davis "even-degree" reformulation is proved in
`LeaHadamard.Hadamard.Lem_even_degree`.
-/

import Mathlib
import LeaHadamard.Defs

open scoped BigOperators
open Finset

namespace LeaHadamard.Hadamard

/-! ## Edges of `K_n` -/

/-- An edge of `K_n` is an ordered pair `(i, j)` with `i < j`. -/
abbrev Edge (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

namespace Edge

variable {n : ℕ}

/-- The smaller endpoint of an edge. -/
def fst (e : Edge n) : Fin n := e.1.1

/-- The larger endpoint of an edge. -/
def snd (e : Edge n) : Fin n := e.1.2

lemma fst_lt_snd (e : Edge n) : e.fst < e.snd := e.2

lemma fst_ne_snd (e : Edge n) : e.fst ≠ e.snd := ne_of_lt e.fst_lt_snd

/-- Incidence: an edge is incident to `v` if `v` is one of its endpoints. -/
def Incident (e : Edge n) (v : Fin n) : Prop := e.fst = v ∨ e.snd = v

instance decIncident (e : Edge n) (v : Fin n) : Decidable (e.Incident v) := by
  unfold Incident; exact inferInstance

@[simp] lemma incident_fst (e : Edge n) : e.Incident e.fst := Or.inl rfl
@[simp] lemma incident_snd (e : Edge n) : e.Incident e.snd := Or.inr rfl

end Edge

/-- The (finite) set of edges incident to a vertex `v`. -/
def incidentSet (n : ℕ) (v : Fin n) : Finset (Edge n) :=
  (Finset.univ : Finset (Edge n)).filter (fun e => e.Incident v)

@[simp] lemma mem_incidentSet {n : ℕ} (v : Fin n) (e : Edge n) :
    e ∈ incidentSet n v ↔ e.Incident v := by
  simp [incidentSet]

/-! ## Λ₀: the half-π lattice on the torus -/

/-- The half-π lattice: `λ_e ∈ (π/2)·ℤ / (2π·ℤ) ≅ ℤ/4`, indexed by edges. -/
abbrev Lambda_0 (n : ℕ) : Type := Edge n → Fin 4

/-- The geometric embedding `Λ₀ → ℝ^Edge`: `k ↦ (k : ℕ) · π/2`. -/
noncomputable def Lambda_0.toReal {n : ℕ} (lam : Lambda_0 n) : Edge n → ℝ :=
  fun e => ((lam e : ℕ) : ℝ) * (Real.pi / 2)

/-! ## Mod-2 reduction `λ ↦ λ^{(2)}` -/

/-- Mod-2 reduction on `Fin 4`: `0,2 ↦ false`, `1,3 ↦ true`. -/
def mod2Fin4 (k : Fin 4) : Bool := decide ((k : ℕ) % 2 = 1)

@[simp] lemma mod2Fin4_zero : mod2Fin4 (0 : Fin 4) = false := by decide
@[simp] lemma mod2Fin4_one : mod2Fin4 (1 : Fin 4) = true := by decide
@[simp] lemma mod2Fin4_two : mod2Fin4 (2 : Fin 4) = false := by decide
@[simp] lemma mod2Fin4_three : mod2Fin4 (3 : Fin 4) = true := by decide

lemma mod2Fin4_eq_true_iff (k : Fin 4) : mod2Fin4 k = true ↔ (k : ℕ) % 2 = 1 := by
  simp [mod2Fin4]

lemma mod2Fin4_eq_false_iff (k : Fin 4) : mod2Fin4 k = false ↔ (k : ℕ) % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (k : ℕ) with h | h <;>
    simp [mod2Fin4, h]

/-- The mod-2 reduction `λ^{(2)}` of a `Λ₀`-point as a Boolean edge-indicator. -/
def Lambda_0.parity {n : ℕ} (lam : Lambda_0 n) : Edge n → Bool :=
  fun e => mod2Fin4 (lam e)

/-- The mod-2 reduction as a `ZMod 2`-valued function: `((lam e : ℕ) : ZMod 2)`.
Equals `1` exactly when `lam.parity e = true`. -/
def Lambda_0.parityZ {n : ℕ} (lam : Lambda_0 n) : Edge n → ZMod 2 :=
  fun e => ((lam e : ℕ) : ZMod 2)

/-- A natural number is `0` in `ZMod 2` iff it is even. -/
lemma natCast_zmod2_eq_zero_iff (m : ℕ) : ((m : ℕ) : ZMod 2) = 0 ↔ m % 2 = 0 := by
  rw [CharP.cast_eq_zero_iff (ZMod 2) 2 m, Nat.dvd_iff_mod_eq_zero]

/-- A natural number is `1` in `ZMod 2` iff it is odd. -/
lemma natCast_zmod2_eq_one_iff (m : ℕ) : ((m : ℕ) : ZMod 2) = 1 ↔ m % 2 = 1 := by
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · exfalso
      have h0' : ((m : ℕ) : ZMod 2) = 0 := (natCast_zmod2_eq_zero_iff m).mpr h0
      rw [h0'] at h
      exact (by decide : (0 : ZMod 2) ≠ 1) h
    · exact h1
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    have h2 : (2 : ZMod 2) = 0 := by decide
    have : ((2 * k + 1 : ℕ) : ZMod 2) = (2 : ZMod 2) * (k : ZMod 2) + 1 := by push_cast; ring
    rw [this, h2, zero_mul, zero_add]

@[simp] lemma Lambda_0.parityZ_eq_zero_iff {n : ℕ}
    (lam : Lambda_0 n) (e : Edge n) :
    lam.parityZ e = 0 ↔ lam.parity e = false := by
  unfold Lambda_0.parityZ Lambda_0.parity
  rw [natCast_zmod2_eq_zero_iff, mod2Fin4_eq_false_iff]

@[simp] lemma Lambda_0.parityZ_eq_one_iff {n : ℕ}
    (lam : Lambda_0 n) (e : Edge n) :
    lam.parityZ e = 1 ↔ lam.parity e = true := by
  unfold Lambda_0.parityZ Lambda_0.parity
  rw [natCast_zmod2_eq_one_iff, mod2Fin4_eq_true_iff]

/-- Compatibility: the two reductions agree under the canonical
`Bool ↔ ZMod 2` correspondence. -/
lemma Lambda_0.parityZ_eq {n : ℕ} (lam : Lambda_0 n) (e : Edge n) :
    lam.parityZ e = (if lam.parity e then 1 else 0) := by
  by_cases h : lam.parity e = true
  · rw [(Lambda_0.parityZ_eq_one_iff lam e).mpr h]
    simp [h]
  · have hf : lam.parity e = false := by
      cases hp : lam.parity e
      · rfl
      · exact absurd hp h
    rw [(Lambda_0.parityZ_eq_zero_iff lam e).mpr hf]
    simp [hf]

/-! ## The induced subgraph `G_{λ^{(2)}}` and vertex degrees -/

/-- The degree of `v` in `G_{λ^{(2)}}`: the number of edges incident to `v`
whose mod-2 reduction is `true`. -/
def Lambda_0.degree {n : ℕ} (lam : Lambda_0 n) (v : Fin n) : ℕ :=
  ((incidentSet n v).filter (fun e => lam.parity e)).card

/-! ## The sublattice Λ

`Λ n` is defined as the kernel (in `ZMod 2`) of the vertex-incidence map:
for every vertex `v`, the sum of `parityZ` over edges incident to `v`
vanishes. -/

/-- Membership predicate for the sublattice `Λ`. -/
def InLambda {n : ℕ} (lam : Lambda_0 n) : Prop :=
  ∀ v : Fin n, (∑ e ∈ incidentSet n v, lam.parityZ e) = 0

instance {n : ℕ} (lam : Lambda_0 n) : Decidable (InLambda lam) := by
  unfold InLambda; exact inferInstance

/-- The sublattice `Λ` as a `Finset` of `Λ₀`. -/
def Lambda (n : ℕ) : Finset (Lambda_0 n) :=
  (Finset.univ : Finset (Lambda_0 n)).filter InLambda

@[simp] lemma mem_Lambda {n : ℕ} (lam : Lambda_0 n) :
    lam ∈ Lambda n ↔ InLambda lam := by
  simp [Lambda]

/-! ## Basic structural lemmas -/

/-- `Λ` is finite (as a subset of the finite type `Λ₀`). -/
instance Lambda.fintype {n : ℕ} : Fintype {lam : Lambda_0 n // InLambda lam} :=
  Subtype.fintype _

end LeaHadamard.Hadamard
