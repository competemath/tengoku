/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactor
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.Local.CompleteQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite étale local algebras over complete local quotients

A finite étale local algebra over a quotient of a complete Noetherian local
ring is the base change of a finite étale algebra over the original ring.
The lift is the explicit monogenic lift of the residue-field extension.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u

/-- A surjective local homomorphism induces an isomorphism on residue fields.-/
theorem residueField_map_bijective_of_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (ResidueField.map f) := by
  refine ⟨(ResidueField.map f).injective, ?_⟩
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨residue R r, ResidueField.map_residue f r⟩

end EtaleFundamentalGroups

end
