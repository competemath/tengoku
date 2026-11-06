/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.LocalRingValuationSubringDVRDominates
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedModel
import Tengoku.Seed.RingTheory.Valuation.LocalSubring
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Tengoku.Seed.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Tengoku.Seed.RingTheory.Localization.AsSubring
import Tengoku.Seed.FieldTheory.AlgebraicClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Detecting nonconstant elements by discrete valuations

A valuation that excludes a nonintegral element admits a finitely generated
integral model containing the inverse. A dominating discrete valuation ring
preserves the inverse as a nonunit. This avoids separability restrictions.
-/

namespace FieldTheory
universe u

/-- A finitely generated field has an affine integral model inside any
valuation subring, containing any prescribed integral element.-/
theorem exists_finiteType_int_model_le_valuationSubring
    (K : Type u) [Field K] (hfg : Field.FG K)
    (V : ValuationSubring K) (y : K) (hy : y ∈ V) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A ∧ IsFractionRing A K ∧
      A.toSubring ≤ V.toSubring ∧ y ∈ A := by
  classical
  obtain ⟨s, hs⟩ := hfg.finitely_generated
  let f : K → K := fun x => if x ∈ V then x else x⁻¹
  let t : Finset K := insert y (s.image f)
  have hft (x : K) (hx : x ∈ s) : f x ∈ t :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have htV : ∀ x ∈ t, x ∈ V := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hy
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      dsimp only [f]
      split_ifs with hzV
      · exact hzV
      · exact (V.mem_or_inv_mem z).resolve_left hzV
  have hst : Subfield.closure (s : Set K) ≤ Subfield.closure (t : Set K) := by
    apply Subfield.closure_le.mpr
    intro x hx
    change x ∈ Subfield.closure (t : Set K)
    have hfx : f x ∈ Subfield.closure (t : Set K) := Subfield.subset_closure (hft x hx)
    by_cases hxV : x ∈ V
    · simpa only [f, ite_eq_left hxV] using hfx
    · have hi := (Subfield.closure (t : Set K)).inv_mem hfx
      simpa only [f, ite_eq_right hxV, inv_inv] using hi
  have ht : Subfield.closure (t : Set K) = ⊤ := top_unique (hs ▸ hst)
  let A := Algebra.adjoin ℤ (t : Set K)
  have hA : A.toSubring = Subring.closure (t : Set K) :=
    congrArg Subalgebra.toSubring (Algebra.adjoin_int (t : Set K))
  refine ⟨A, (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset t), ?_, ?_, ?_⟩
  · apply IsFractionRing.of_field A K
    intro z
    have hz : z ∈ Subfield.closure (t : Set K) := by rw [ht]; exact Subfield.mem_top z
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hz
    exact ⟨⟨a, by change a ∈ A.toSubring; rw [hA]; exact ha⟩,
      ⟨b, by change b ∈ A.toSubring; rw [hA]; exact hb⟩, hab.symm⟩
  · rw [hA]
    exact Subring.closure_le.mpr htV
  · exact Algebra.subset_adjoin (Finset.mem_insert_self y (s.image f))

end FieldTheory
