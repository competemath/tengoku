/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

module

public import Tengoku.Cslib.Cslib.MachineLearning.PACLearning.VersionSpace
public import Tengoku.Seed.Data.Fin.Tuple.Basic
public import Tengoku.Seed.Data.Set.Card
public import Tengoku.Seed.Data.Set.Finite.Powerset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Version Space Lattice

The collection of all version spaces of a concept
class is a ∩-closed family with top `C`, the *version space lattice* of Mitchell (1982).

## Main definitions

- `VersionSpaces C`: the family of all version spaces of `C`, over samples of every size.

## Main results

- `versionSpace_append`: the version space of an appended sample is the intersection of
  the version spaces.
- `self_mem_versionSpaces`, `inter_mem_versionSpaces`: the family contains `C` (top) and
  is closed under intersection.
- `versionSpaces_subset_powerset`, `versionSpaces_finite`, `versionSpaces_ncard_le`: every
  member is a subset of `C` and for a finite class the family is finite of size at most
  `2 ^ C.ncard`.

## References

* [Mitchell1977]
* [Mitchell1982]
* [Mitchell1997]
-/

@[expose] public section

open Set

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} {β : Type*}

/-- *The version-space meet law.* The version space of an appended sample is the
intersection of the version spaces of the two parts: constraints accumulate by
intersection.
@isnad1 id=eq.0h7v.s6.d173d359a953 from=translated src=- shape=cc2a744e vocab=fd950adc
-/
theorem versionSpace_append {m n : ℕ} (C : ConceptClass α β)
    (S : LabeledSample α β m) (T : LabeledSample α β n) :
    VersionSpace C (Fin.append S T) = VersionSpace C S ∩ VersionSpace C T := by
  ext h
  constructor
  · intro hh
    refine ⟨⟨hh.1, fun i => ?_⟩, hh.1, fun i => ?_⟩
    · have hi := hh.2 (Fin.castAdd n i)
      rwa [Fin.append_left] at hi
    · have hi := hh.2 (Fin.natAdd m i)
      rwa [Fin.append_right] at hi
  · rintro ⟨⟨hC, hS⟩, ⟨-, hT⟩⟩
    refine ⟨hC, fun i => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact hS j
    · rw [Fin.append_right]
      exact hT j

/-- The family of all version spaces of a concept class, over labeled samples of every
size.-/
def VersionSpaces (C : ConceptClass α β) : Set (ConceptClass α β) :=
  {V | ∃ (m : ℕ) (S : LabeledSample α β m), V = VersionSpace C S}

/-- Membership in the version-space family unfolds to a witnessing sample.
@isnad1 id=iff.0h4v.s5.457438c3952e from=translated src=- shape=ed2fb3a7 vocab=147bc995
-/
theorem mem_versionSpaces_iff {C V : ConceptClass α β} :
    V ∈ VersionSpaces C ↔ ∃ (m : ℕ) (S : LabeledSample α β m), V = VersionSpace C S :=
  Iff.rfl

/-- The whole class is a version space (of the empty sample) which means the family has top `C`.
@isnad1 id=mem.0h3v.s4.85b3215958fb from=translated src=- shape=d706ffae vocab=394d7269
-/
theorem self_mem_versionSpaces (C : ConceptClass α β) : C ∈ VersionSpaces C :=
  ⟨0, Fin.elim0, (versionSpace_empty_sample C Fin.elim0).symm⟩

/-- The version-space family is closed under intersection (append the witnessing
samples).
@isnad1 id=mem.2h5v.s6.91d612a6a6d9 from=translated src=- shape=048c354f vocab=fbfab384
-/
theorem inter_mem_versionSpaces {C U V : ConceptClass α β}
    (hU : U ∈ VersionSpaces C) (hV : V ∈ VersionSpaces C) :
    U ∩ V ∈ VersionSpaces C := by
  obtain ⟨m, S, rfl⟩ := hU
  obtain ⟨n, T, rfl⟩ := hV
  exact ⟨m + n, Fin.append S T, (versionSpace_append C S T).symm⟩

/-- Every version space is a subset of the class: the family lives in the powerset
of `C`.
@isnad1 id=le.0h3v.s4.5142be716ed5 from=translated src=- shape=fff64808 vocab=e16b99ca
-/
theorem versionSpaces_subset_powerset (C : ConceptClass α β) :
    VersionSpaces C ⊆ 𝒫 C := by
  rintro V ⟨m, S, rfl⟩
  exact versionSpace_subset C S

/-- A finite concept class has finitely many version spaces.
@isnad1 id=finite.1h3v.s4.455320e7035a from=translated src=- shape=7d821472 vocab=afd0f2b4
-/
theorem versionSpaces_finite {C : ConceptClass α β} (hC : C.Finite) :
    (VersionSpaces C).Finite :=
  hC.finite_subsets.subset (versionSpaces_subset_powerset C)

/-- A finite concept class has at most `2 ^ C.ncard` version spaces: the lattice embeds
in the powerset.
@isnad1 id=le.1h3v.s5.7263d19e234f from=translated src=- shape=b2348bb7 vocab=554cf3c2
-/
theorem versionSpaces_ncard_le {C : ConceptClass α β} (hC : C.Finite) :
    (VersionSpaces C).ncard ≤ 2 ^ C.ncard :=
  (ncard_le_ncard (versionSpaces_subset_powerset C) hC.finite_subsets).trans_eq
    (ncard_powerset C hC)

end Cslib.MachineLearning.PACLearning
