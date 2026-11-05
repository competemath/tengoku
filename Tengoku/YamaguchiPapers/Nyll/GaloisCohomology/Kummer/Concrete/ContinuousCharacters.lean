/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.Infinite
import Tengoku.Seed.FieldTheory.Galois.Profinite
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-stage factorization of continuous Galois characters

A continuous character from an infinite Galois group to a discrete group
factors through the Galois group of a finite Galois intermediate field.
-/

noncomputable section

namespace KummerTheory

open scoped Topology

variable {K Ω A : Type*}
  [Field K] [Field Ω] [Algebra K Ω]
  [Group A] [TopologicalSpace A] [DiscreteTopology A]

private theorem continuousCharacterIsOpenKer (χ : Gal(Ω/K) →ₜ* A) :
    IsOpen (χ.toMonoidHom.ker : Set Gal(Ω/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete ({1} : Set A)).preimage χ.continuous

variable [IsGalois K Ω]

private theorem continuousCharacterExistsFiniteGaloisFixingSubgroupLeKer
    (χ : Gal(Ω/K) →ₜ* A) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      E.fixingSubgroup ≤ χ.toMonoidHom.ker := by
  have hnhds : (χ.toMonoidHom.ker : Set Gal(Ω/K)) ∈ 𝓝 1 :=
    (continuousCharacterIsOpenKer χ).mem_nhds χ.toMonoidHom.ker.one_mem
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := K) (K := Ω) (χ.toMonoidHom.ker : Set Gal(Ω/K))).1 hnhds
  exact ⟨E, hE⟩

/-- Every continuous character of an infinite Galois group into a discrete
group factors through the Galois group of a finite Galois intermediate
field.
@isnad1 id=ex.0h4v.s12.2064345cb7e1 from=translated src=- shape=f03e05c8 vocab=9b551848
-/
theorem continuousCharacter_factors_through_finiteGalois
    (χ : Gal(Ω/K) →ₜ* A) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (χE : Gal(E/K) →* A),
      χE.comp (AlgEquiv.restrictNormalHom E) = χ.toMonoidHom := by
  obtain ⟨E, hE⟩ :=
    continuousCharacterExistsFiniteGaloisFixingSubgroupLeKer χ
  have hker : (AlgEquiv.restrictNormalHom E).ker ≤ χ.toMonoidHom.ker := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact hE
  let χE : Gal(E/K) →* A :=
    (AlgEquiv.restrictNormalHom E).liftOfSurjective
      (AlgEquiv.restrictNormalHom_surjective Ω) ⟨χ.toMonoidHom, hker⟩
  refine ⟨E, χE, ?_⟩
  simp [χE]

end KummerTheory
