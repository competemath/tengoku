/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.CrownRecovery
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.QuadrupleObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A Steiner 3-(12,4,1) design forced by the Krein construction

Unique crown recovery supplies the Steiner blocks. Their replication
equation 3r = 55 excludes the constructed triple design on 57 points.
-/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

def pairNeighborhood (a u : V) : Finset V :=
  Finset.univ.filter fun x => D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x

@[simp] theorem mem_pairNeighborhood (a u x : V) :
    x ∈ D.pairNeighborhood a u ↔ D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x := by simp [pairNeighborhood]

def crownSlice (W : Finset V) (a u : V) : Finset V :=
  W.filter fun x => D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x

@[simp] theorem mem_crownSlice (W : Finset V) (a u x : V) :
    x ∈ D.crownSlice W a u ↔ x ∈ W ∧ D.kreinGraph.Adj a x ∧ D.kreinGraph.Adj u x := by
  simp [crownSlice]

noncomputable def steinerBlocks (a u : V) : Finset (Finset V) := by
  classical
  exact ((D.pairNeighborhood a u).powersetCard 4).filter fun Q =>
    ∃ W : Finset V, D.IsCrown W ∧ Q = D.crownSlice W a u

theorem mem_steinerBlocks (a u : V) (Q : Finset V) :
    Q ∈ D.steinerBlocks a u ↔ (Q ⊆ D.pairNeighborhood a u ∧ Q.card = 4) ∧
      ∃ W : Finset V, D.IsCrown W ∧ Q = D.crownSlice W a u := by
  classical
  simp [steinerBlocks]

end SRG266.QuasiSymmetric.TripleDesign57

namespace SRG266.QuasiSymmetric.ConcreteQSD56

end SRG266.QuasiSymmetric.ConcreteQSD56

namespace SRG266.QuasiSymmetric

universe u

end SRG266.QuasiSymmetric
