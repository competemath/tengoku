/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.BicliqueGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

def neighborCount (T : Finset V) (x : V) : ℕ :=
  (T.filter fun y => D.kreinGraph.Adj x y).card

theorem biclique_neighbors_of_mem_side {S : Finset V} (hI : D.IndependentSet S)
    {x : V} (hx : x ∈ S) :
    (S ∪ D.commonTo S).filter (fun y => D.kreinGraph.Adj x y) = D.commonTo S := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyU,hxy⟩ := Finset.mem_filter.mp hy
    rcases Finset.mem_union.mp hyU with hyS | hyC
    · exact (hI x hx y hyS (D.kreinGraph.ne_of_adj hxy) hxy).elim
    · exact hyC
  · intro hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hy, (D.mem_commonTo _ _).mp hy x hx⟩

def bicliqueOutside (S : Finset V) : Finset V := Finset.univ \ (S ∪ D.commonTo S)

def bicliqueClass (S : Finset V) (i : ℕ) : Finset V :=
  (D.bicliqueOutside S).filter fun x => D.neighborCount (S ∪ D.commonTo S) x = i

@[simp] theorem mem_bicliqueOutside (S : Finset V) (x : V) :
    x ∈ D.bicliqueOutside S ↔ x ∉ S ∪ D.commonTo S := by simp [bicliqueOutside]

theorem boundedTwo_fiber_moments {α : Type*} [DecidableEq α] (U : Finset α)
    (f : α → ℕ) (hle : ∀ x ∈ U, f x ≤ 2) :
    (U.card : ℤ) = (U.filter fun x => f x = 0).card +
      (U.filter fun x => f x = 1).card + (U.filter fun x => f x = 2).card ∧
    (∑ x ∈ U, (f x : ℤ)) = (U.filter fun x => f x = 1).card +
      2 * (U.filter fun x => f x = 2).card ∧
    (∑ x ∈ U, (f x : ℤ)^2) = (U.filter fun x => f x = 1).card +
      4 * (U.filter fun x => f x = 2).card := by
  have hp (x) (hx : x ∈ U) :
      (1 : ℤ) = (if f x = 0 then 1 else 0) + (if f x = 1 then 1 else 0) +
        (if f x = 2 then 1 else 0) ∧
      (f x : ℤ) = (if f x = 1 then 1 else 0) + 2 * (if f x = 2 then 1 else 0) ∧
      (f x : ℤ)^2 = (if f x = 1 then 1 else 0) + 4 * (if f x = 2 then 1 else 0) := by
    have h := hle x hx
    have hcases : f x = 0 ∨ f x = 1 ∨ f x = 2 := by omega
    rcases hcases with h0 | h1 | h2 <;> simp_all
  have h0 := Finset.sum_congr rfl (fun x hx => (hp x hx).1)
  have h1 := Finset.sum_congr rfl (fun x hx => (hp x hx).2.1)
  have h2 := Finset.sum_congr rfl (fun x hx => (hp x hx).2.2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, nsmul_eq_mul, mul_one] at h0 h1 h2
  exact ⟨h0,h1,h2⟩

end SRG266.QuasiSymmetric.TripleDesign57
