/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PDUnimodular
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEGram
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open scoped Matrix

def IsRootADEEmbedding {n : ℕ} (L : PDUnimodularLattice n)
    (ts : List ADEType) : Prop :=
  ∃ f : (Fin (ADEType.rankSum ts) → ℤ) →ₗ[ℤ] L.carrier,
    Function.Injective f ∧
      (∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (adeGram ts).2 v w) ∧
      ∀ r : L.carrier, L.pairing r r = 2 → ∃ v, f v = r

def HasFullRankRootType {n : ℕ} (L : PDUnimodularLattice n)
    (ts : List ADEType) : Prop :=
  ∃ us : List ADEType, us.Perm ts ∧ ADEType.rankSum us = n ∧
    IsRootADEEmbedding L us

theorem HasFullRankRootType.of_perm {n : ℕ} {L : PDUnimodularLattice n}
    {ts us : List ADEType} (h : HasFullRankRootType L ts) (p : ts.Perm us) :
    HasFullRankRootType L us := by
  obtain ⟨vs, hv, hrank, hmodel⟩ := h
  exact ⟨vs, hv.trans p, hrank, hmodel⟩

end Lattice
end SRG266
