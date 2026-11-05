/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.KrullTopology
import Tengoku.Seed.Topology.LocallyConstant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Locally constant orbit maps in algebraic Galois groups

A single algebraic element is fixed by an open subgroup. Its orbit map, and
the induced orbit map on units, are locally constant in the Krull topology.
-/

open scoped Pointwise

namespace GaloisCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [Algebra.IsIntegral K Ω]

/-- Evaluation at an algebraic element is locally constant.
@isnad1 id=islocall.0h3v.s7.4f598de8996b from=translated src=- shape=01d5b343 vocab=2b5eef5c
-/
theorem isLocallyConstant_galois_apply (x : Ω) :
    IsLocallyConstant (fun σ : Gal(Ω/K) => σ x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro σ
  let E : IntermediateField K Ω := IntermediateField.adjoin K {x}
  have : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  refine ⟨σ • (E.fixingSubgroup : Set Gal(Ω/K)),
    E.fixingSubgroup_isOpen.leftCoset σ, ?_, ?_⟩
  · exact ⟨1, E.fixingSubgroup.one_mem, mul_one σ⟩
  · rintro τ ⟨ρ, hρ, rfl⟩
    have hfix : ρ x = x :=
      (IntermediateField.mem_fixingSubgroup_iff E ρ).mp hρ x
        (IntermediateField.mem_adjoin_simple_self K x)
    change σ (ρ x) = σ x
    exact congrArg σ hfix

/-- The Galois orbit of an algebraic unit is locally constant.
@isnad1 id=islocall.0h3v.s9.fc48f03ff8cc from=translated src=- shape=4cb7b527 vocab=fcf4c5f6
-/
theorem isLocallyConstant_galois_units (x : Ωˣ) :
    IsLocallyConstant (fun σ : Gal(Ω/K) => σ • x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro σ
  obtain ⟨U, hU, hσ, hconst⟩ := (isLocallyConstant_galois_apply (K := K) (x : Ω)).exists_open σ
  refine ⟨U, hU, hσ, ?_⟩
  intro τ hτ
  apply Units.ext
  exact hconst τ hτ

end GaloisCohomology
