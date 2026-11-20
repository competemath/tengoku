/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADECartanGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open scoped Matrix BigOperators Classical

def doubleForkRel (n : ℕ) :
    (Fin n ⊕ (Fin 2 ⊕ Fin 2)) → (Fin n ⊕ (Fin 2 ⊕ Fin 2)) → Prop :=
  fun x y ↦
    match x, y with
    | Sum.inl i, Sum.inl j => (SimpleGraph.pathGraph n).Adj i j
    | Sum.inl i, Sum.inr (Sum.inl _) => i.1 = 0
    | Sum.inl i, Sum.inr (Sum.inr _) => i.1 + 1 = n
    | _, _ => False

def doubleForkGraph (n : ℕ) : SimpleGraph (Fin n ⊕ (Fin 2 ⊕ Fin 2)) :=
  SimpleGraph.fromRel (doubleForkRel n)

def doubleForkWeight {n : ℕ} : Fin n ⊕ (Fin 2 ⊕ Fin 2) → ℤ
  | Sum.inl _ => 2
  | Sum.inr _ => 1

/--
@isnad1 id=eq.0h2v.s7.b8b24548ec72 from=translated src=- shape=538590a5 vocab=62d3c177
-/
theorem pathGraph_sum_adj_indicator (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, if (SimpleGraph.pathGraph n).Adj i j then (1 : ℤ) else 0) =
      (if 0 < i.1 then 1 else 0) + (if i.1 + 1 < n then 1 else 0) := by
  classical
  have hleft :
      (∑ j : Fin n, if j.1 + 1 = i.1 then (1 : ℤ) else 0) =
      if 0 < i.1 then 1 else 0 := by
    by_cases hi : 0 < i.1
    · let p : Fin n := ⟨i.1 - 1, by omega⟩
      have hiff (j : Fin n) : j.1 + 1 = i.1 ↔ j = p := by
        dsimp [p]
        simp only [Fin.ext_iff]
        omega
      simp [hiff, hi]
    · have hnot (j : Fin n) : ¬ j.1 + 1 = i.1 := by omega
      simp [hnot, hi]
  have hright :
      (∑ j : Fin n, if i.1 + 1 = j.1 then (1 : ℤ) else 0) =
      if i.1 + 1 < n then 1 else 0 := by
    by_cases hi : i.1 + 1 < n
    · let p : Fin n := ⟨i.1 + 1, hi⟩
      have hiff (j : Fin n) : i.1 + 1 = j.1 ↔ j = p := by
        dsimp [p]
        simp only [Fin.ext_iff]
        omega
      simp [hiff, hi]
    · have hnot (j : Fin n) : ¬ i.1 + 1 = j.1 := by omega
      simp [hnot, hi]
  calc
    _ = ∑ j : Fin n,
        ((if j.1 + 1 = i.1 then (1 : ℤ) else 0) +
          (if i.1 + 1 = j.1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [SimpleGraph.pathGraph_adj]
      split_ifs <;> omega
    _ = _ := by rw [Finset.sum_add_distrib, hleft, hright]

end Lattice
end SRG266
