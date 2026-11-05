/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.QuotientGroup.Finite
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.FiniteGroups.Classes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The class of all finite groups

This module defines `FiniteGroupClass.allFinite` and proves its standard closure properties:
formation, subgroup, normal-subgroup, quotient, finite-subdirect-product, extension, and
hereditary closure.  It also supplies the trivial-quotient instance used by pro-\(C\)
constructions when no restriction beyond finiteness is intended.
-/

namespace ProCGroups

universe u

namespace FiniteGroupClass

/-- The class of all finite groups.-/
def allFinite : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G
  finite_of_mem := fun hG => hG
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG
    exact Finite.of_equiv G e.toEquiv

/-- The class of all finite groups is an extension-closed formation.
@isnad1 id=formatio.0h0v.s1.da0d61696d99 from=translated src=- shape=49959d42 vocab=1f24bed1
-/
theorem allFinite_formation : Formation allFinite := by
  refine ⟨?_, ?_⟩
  · intro G _ N _ hG
    let : Finite G := hG
    exact Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · intro ι _ G _ H _ f hf _ hH
    let : ∀ i, Finite (H i) := hH
    exact Finite.of_injective f hf

/-- The class of all finite groups is closed under isomorphism.
@isnad1 id=isomclos.0h0v.s1.8d50b4028349 from=translated src=- shape=49959d42 vocab=834e4579
-/
theorem allFinite_isomClosed : IsomClosed allFinite := by
  exact allFinite.isomClosed

/-- The class of all finite groups is closed under subgroups.
@isnad1 id=subgroup.0h0v.s1.90b1b07fdcf0 from=translated src=- shape=49959d42 vocab=57fe26dc
-/
theorem allFinite_subgroupClosed : SubgroupClosed allFinite := by
  intro G _ H hG
  let : Finite G := hG
  exact Finite.of_injective H.subtype Subtype.val_injective

/-- The class of all finite groups is closed under normal subgroups.
@isnad1 id=normalsu.0h0v.s1.fc5b5dbc9c75 from=translated src=- shape=49959d42 vocab=5e660891
-/
theorem allFinite_normalSubgroupClosed : NormalSubgroupClosed allFinite := by
  intro G _ N _ hG
  exact allFinite_subgroupClosed N hG

/-- The class of all finite groups is closed under quotients.
@isnad1 id=quotient.0h0v.s1.3adc112f0611 from=translated src=- shape=49959d42 vocab=f4ff01a2
-/
theorem allFinite_quotientClosed : QuotientClosed allFinite :=
  allFinite_formation.quotientClosed

/-- The class of all finite groups is closed under finite subdirect products.
@isnad1 id=finitesu.0h0v.s1.14d67cee34d6 from=translated src=- shape=49959d42 vocab=844594a8
-/
theorem allFinite_finiteSubdirectProductClosed : FiniteSubdirectProductClosed allFinite :=
  allFinite_formation.finiteSubdirectProductClosed

/-- The class of all finite groups is extension closed.
@isnad1 id=extensio.0h0v.s1.6464deb282bd from=translated src=- shape=49959d42 vocab=9ba6f44f
-/
theorem allFinite_extensionClosed : ExtensionClosed allFinite := by
  intro E _ N _ hN hQ
  let : Finite N := hN
  let : Finite (E ⧸ N) := hQ
  exact Finite.of_subgroup_quotient N

/-- The class of all finite groups is hereditary.
@isnad1 id=heredita.0h0v.s1.7fb72cdc6ace from=translated src=- shape=49959d42 vocab=fe307c16
-/
theorem allFinite_hereditary : Hereditary allFinite := by
  refine ⟨?_⟩
  intro G H _ _ hH f hf
  let : Finite H := hH
  exact Finite.of_injective f hf

end FiniteGroupClass

end ProCGroups
