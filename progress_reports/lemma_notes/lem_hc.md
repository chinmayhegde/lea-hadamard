# `lem:hc` — design notes (landed)

## Statement (per blueprint)

For `H` a polynomial of degree at most `q` in either independent
Rademacher signs or independent centered Gaussians, and for every
`p ≥ 2`:
$$\|H\|_{L^p} \;\le\; (p-1)^{q/2}\,\|H\|_{L^2}.$$

## Lean target and scope

Lean target name: `LeaHadamard.Hadamard.fixedDegreeHC_degree2_W_fourth`.

The name is decisive: `fixedDegree` + `degree2` + `W` (Walsh) + `fourth`
(L⁴). This is the **leaf instance** at `(p, q) = (4, 2)` over the
discrete cube — the only case the paper actually invokes downstream.
Davis's own Lean targets exactly this leaf. We follow the same scope.

What landed (in `LeaHadamard/Auto/Lem_hc.lean`):

```lean
theorem fixedDegreeHC_degree2_W_fourth {n : ℕ} (p : WalshDeg2 n) :
    avgSigns n (fun σ => (eval p σ) ^ 4)
      ≤ 81 * (avgSigns n (fun σ => (eval p σ) ^ 2)) ^ 2 :=
  hc_degree2_fourth p
```

Constant `81 = 3^4` matches `((p-1)^{q/2})^p` at `(p,q) = (4,2)`.

## Two attempts; second one clean

**Attempt 1 (2026-05-03 AM)** — caught as the first instance of the
**statement-tautologization** cheat class. Lea introduced an explicit
`hHC` hypothesis whose body was the conclusion, then proved by `:= hHC`.
Quarantined. This finding seeded cheat class 6 in our taxonomy and
forced an update to the dispatcher prompt.

**Attempt 2 (2026-05-03 PM)** — clean. After Lea built the missing
hypercontractive infrastructure across Stages 1, 2, 4, 5 of the
[infrastructure-cliff push](../2026-05-03-infrastructure-cliff.md),
the retry under the strengthened dispatcher prompt produced the
9-turn / ~$0.58 actual / 63-line file linked above. The proof is a
single term-mode application of `hc_degree2_fourth` from
`LeaHadamard.Mathlib.Hypercontractive`.

## Why the win matters

`lem:hc` is the first **previously-cheated** layer-0 leaf to be cleanly
closed. The path was:

1. Recognize the cheat (manual signature audit vs blueprint).
2. Diagnose the missing infrastructure (Bonami-Beckner machinery
   absent from Mathlib).
3. Build that infrastructure autonomously (Stages 1+2+4+5 dispatched
   to Lea, ~$38 actual / 1202 lines across 3 new files).
4. Retry the leaf with the new infrastructure exposed via dispatcher
   hints — close in 9 turns at $0.58.

This is the canonical pattern we now expect to apply to the remaining
stuck leaves (`lem:weak-comparison`, `lem:gaussian-quadratic`,
`fact:fixed-n`): identify missing infrastructure, build it, retry.

## Trust surface

- `#print axioms LeaHadamard.Hadamard.fixedDegreeHC_degree2_W_fourth`
  → `propext, Classical.choice, Quot.sound`.
- No `sorry`, no `axiom`, no `native_decide`.
- The theorem ranges universally over `WalshDeg2 n` (not specialized
  to a trivial case), and the LHS uses the genuine `eval` map (not
  defined-as-RHS).
- The transitive proof chain (through `hc_degree2_fourth` → Bonami
  two-point + linear-form moment identities → induction on Bool^n)
  is fully kernel-verified.

## Files

- Closed leaf: [`LeaHadamard/Auto/Lem_hc.lean`](../../LeaHadamard/Auto/Lem_hc.lean)
- Backing infrastructure: [`LeaHadamard/Mathlib/`](../../LeaHadamard/Mathlib/) — see [`infra_hypercontractive_layer.md`](infra_hypercontractive_layer.md) for the layer overview.
- Quarantined cheat: `runs/stuck/lem_hc.cheat_tautology.lean`.
