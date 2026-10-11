/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Tengoku

/-!
# Indexing equivalences for the QuantumInfo bridge

Translations between Algolean's flat n-qubit register indexing
`Fin n → α` and QuantumInfo's product-based tensor indexing `d₁ × d₂`.
Core of the `par` case in `QuantumCircuit.toCPTP` and of gate embedding.

## Main definitions

- `finFunSplitEquiv m k α` : `(Fin (m + k) → α) ≃ (Fin m → α) × (Fin k → α)`.
  Used to bridge `Fin (m + k) → Fin 2`-indexed states to the product-indexed
  tensor `MState (Fin m → Fin 2) ⊗ᴹ MState (Fin k → Fin 2)`.

## Design

These are needed as `Equiv`s rather than propositional equalities because
QuantumInfo's `CPTPMap.ofEquiv` and `MState.relabel` consume `Equiv`s.
Propositional equalities of indexing types would require casting through
`Eq.mpr`, which the QuantumInfo API does not provide for.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

/-- Split a function on `Fin (m + k)` into the pair of its restrictions to
the first `m` and last `k` indices. Built from `finSumFinEquiv` and
`Equiv.sumArrowEquivProdArrow`.

The computational content is: `f ↦ (f ∘ Fin.castAdd k, f ∘ Fin.natAdd m)`. -/
def finFunSplitEquiv (m k : ℕ) (α : Type*) :
    (Fin (m + k) → α) ≃ (Fin m → α) × (Fin k → α) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl α)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) α)

/--
@isnad1 id=eq.0h5v.s7.e21636704b14 from=translated src=- shape=a8c7ec33 vocab=7fff92ae
-/
@[simp]
theorem finFunSplitEquiv_apply_fst (m k : ℕ) (α : Type*)
    (f : Fin (m + k) → α) (i : Fin m) :
    (finFunSplitEquiv m k α f).1 i = f (Fin.castAdd k i) := by
  simp [finFunSplitEquiv, Equiv.sumArrowEquivProdArrow,
    Equiv.arrowCongr, finSumFinEquiv_apply_left]

/--
@isnad1 id=eq.0h5v.s7.7be9a1e198bc from=translated src=- shape=f01add88 vocab=ecd04d8e
-/
@[simp]
theorem finFunSplitEquiv_apply_snd (m k : ℕ) (α : Type*)
    (f : Fin (m + k) → α) (j : Fin k) :
    (finFunSplitEquiv m k α f).2 j = f (Fin.natAdd m j) := by
  simp [finFunSplitEquiv, Equiv.sumArrowEquivProdArrow,
    Equiv.arrowCongr, finSumFinEquiv_apply_right]

/--
@isnad1 id=eq.0h5v.s7.80ec964b94f7 from=translated src=- shape=1a6ccb71 vocab=32d59f0d
-/
@[simp]
theorem finFunSplitEquiv_symm_apply_castAdd (m k : ℕ) (α : Type*)
    (p : (Fin m → α) × (Fin k → α)) (i : Fin m) :
    (finFunSplitEquiv m k α).symm p (Fin.castAdd k i) = p.1 i := by
  simp [finFunSplitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/--
@isnad1 id=eq.0h5v.s7.10bf2d97a298 from=translated src=- shape=30acd4ec vocab=074d05a7
-/
@[simp]
theorem finFunSplitEquiv_symm_apply_natAdd (m k : ℕ) (α : Type*)
    (p : (Fin m → α) × (Fin k → α)) (j : Fin k) :
    (finFunSplitEquiv m k α).symm p (Fin.natAdd m j) = p.2 j := by
  simp [finFunSplitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

end Algorithms

end Algolean
