/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaTemperedFundamentalGroups.TemperedFundamentalGroups.SemistableReduction.NodeNormal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local tame lemma

Blueprint §9.2, first step of the tame route. Let `O` be an integrally closed domain (e.g. a
discrete valuation ring), `c ∈ O` nonzero (e.g. `c = ϖ ^ n` for a uniformizer `ϖ`) and `0 < m`.

* **At a node** (`Node.kummer_isIntegralClosure`): let `A = O[u, v] ⧸ (u v - c ^ m)` and
  `B = O[w, z] ⧸ (w z - c)`, with `A → B`, `u ↦ w ^ m`, `v ↦ z ^ m` (`Node.kummerAlgebra`). Then `B`
  is the integral closure of `A` in `Frac B`, i.e. the normalization of the node `A` in the Kummer
  extension `Frac A (u ^ (1 / m))` is again a node, of thickness `c` instead of `c ^ m`. For a DVR
  and `c = ϖ ^ n` this is `Node.kummer_isIntegralClosure_of_irreducible`: the normalization of the
  node `u v = ϖ ^ (m n)` (written `(ϖ ^ n) ^ m`) is the node `w z = ϖ ^ n`.
* **At a smooth point** (`smoothKummer_isIntegralClosure`): `O[w]` is the integral closure of
  `O[u] = O[w ^ m]` in `Frac O[w]`.
-/

open Polynomial

namespace SemistableReduction

namespace Node

variable {O : Type*} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] {c : O} {m : ℕ}

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

end DVR

end Node

section Smooth

variable (O : Type*) [CommRing O] (m : ℕ)

/-- The smooth local model `O[u] = O[w ^ m] ⊆ O[w]` of the Kummer cover `u = w ^ m`. -/
noncomputable abbrev smoothKummer : Subalgebra O O[X] := Algebra.adjoin O {X ^ m}

lemma range_expand : (expand O m).range = smoothKummer O m := by
  rw [smoothKummer, Algebra.adjoin_singleton_eq_range_aeval]
  congr 1

variable {m}

/-- For `0 < m`, `O[u] ≅ O[w ^ m]`, `u ↦ w ^ m`. -/
noncomputable def smoothKummerEquiv [IsDomain O] (hm : 0 < m) : O[X] ≃ₐ[O] smoothKummer O m :=
  (AlgEquiv.ofInjective _ (expand_injective hm)).trans (Subalgebra.equivOfEq _ _ (range_expand O m))

@[simp] lemma smoothKummerEquiv_X [IsDomain O] (hm : 0 < m) :
    (smoothKummerEquiv O hm X : O[X]) = X ^ m := by
  simp [smoothKummerEquiv]

lemma smoothKummer_adjoin_X : Algebra.adjoin (smoothKummer O m) {(X : O[X])} = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using Polynomial.induction_on with
  | C a =>
    have ha : C a ∈ smoothKummer O m := (smoothKummer O m).algebraMap_mem a
    exact Subalgebra.algebraMap_mem _ (⟨C a, ha⟩ : smoothKummer O m)
  | add p q hp hq => exact add_mem hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc]
    exact mul_mem h (Algebra.subset_adjoin rfl)

/-- `O[w]` is finite over `O[w ^ m]` for `0 < m`. -/
theorem smoothKummer_finite (hm : 0 < m) : Module.Finite (smoothKummer O m) O[X] := by
  have h := fg_adjoin_of_finite (R := smoothKummer O m) (Set.toFinite {(X : O[X])}) (by
    rintro x rfl
    refine ⟨Polynomial.X ^ m - Polynomial.C ⟨X ^ m, Algebra.subset_adjoin rfl⟩,
      Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
    simp [Polynomial.eval₂_sub])
  rw [smoothKummer_adjoin_X, Algebra.top_toSubmodule] at h
  exact ⟨h⟩

/-- **Local tame lemma at a smooth point.** For an integrally closed domain `O` and `0 < m`,
`O[w]` is the integral closure of `O[u] = O[w ^ m]` in its fraction field. -/
theorem smoothKummer_isIntegralClosure [IsDomain O] [IsIntegrallyClosed O] (hm : 0 < m) :
    IsIntegralClosure O[X] (smoothKummer O m) (FractionRing O[X]) := by
  have := smoothKummer_finite O hm
  have : Algebra.IsIntegral (smoothKummer O m) O[X] := Algebra.IsIntegral.of_finite _ _
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

end Smooth

end SemistableReduction
