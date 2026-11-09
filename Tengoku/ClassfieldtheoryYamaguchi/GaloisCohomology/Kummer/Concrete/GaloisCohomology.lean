/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Galois cohomology for Kummer theory

Hilbert 90 and multiplicative cocycle statements used by the concrete Kummer correspondence.
-/

namespace KummerTheory

open groupCohomology

section NoetherHilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {f : Gal(L/K) → Lˣ}

/-- Rearranged unit-valued form of Noether's Hilbert theorem 90.
@isnad1 id=ex.1h3v.s10.61a1c54c93bc from=translated src=- shape=2a61bed1 vocab=620ab088
-/
theorem noetherHilbert90_exists_mul (hf : IsMulCocycle₁ f) :
    ∃ β : Lˣ, ∀ σ : Gal(L/K), σ • β = f σ * β := by
  rcases
      groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf with
    ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  intro σ
  rw [← hβ σ]
  exact (div_mul_cancel (σ • β) β).symm

/-- Field-valued version of Noether's Hilbert theorem 90.
@isnad1 id=ex.1h3v.s9.bdb93e496763 from=translated src=- shape=66015d55 vocab=347a35c2
-/
theorem noetherHilbert90_exists_nonzero_div (hf : IsMulCocycle₁ f) :
    ∃ β : L, β ≠ 0 ∧ ∀ σ : Gal(L/K), σ β / β = f σ := by
  rcases
      groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf with
    ⟨β, hβ⟩
  refine ⟨β, Units.ne_zero β, ?_⟩
  intro σ
  simpa using congrArg Units.val (hβ σ)

/-- Rearranged field-valued form of Noether's Hilbert theorem 90.
@isnad1 id=ex.1h3v.s9.b7da8eb2d4fe from=translated src=- shape=d7fa40d2 vocab=345fece3
-/
theorem noetherHilbert90_exists_nonzero_mul (hf : IsMulCocycle₁ f) :
    ∃ β : L, β ≠ 0 ∧ ∀ σ : Gal(L/K), σ β = f σ * β := by
  rcases noetherHilbert90_exists_nonzero_div (K := K) (L := L) hf with ⟨β, hβ0, hβ⟩
  refine ⟨β, hβ0, ?_⟩
  intro σ
  have h := hβ σ
  rw [div_eq_iff hβ0] at h
  exact h

end NoetherHilbert90

section CyclicHilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable [IsGalois K L]

/-- Cyclic Hilbert theorem 90: a norm-one element in a cyclic extension is `y / σ(y)`.
@isnad1 id=ex.2h4v.s9.ed921583fc27 from=translated src=- shape=0a189045 vocab=54846d3d
-/
theorem cyclicHilbert90_exists_div_of_norm_eq_one
    {g : Gal(L/K)} (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, ↑y / g ↑y = x := by
  let : IsCyclic (Gal(L/K)) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg⟩
  exact groupCohomology.exists_div_of_norm_eq_one hg hx

/-- Field-valued version of Cyclic Hilbert theorem 90.
@isnad1 id=ex.2h4v.s9.36397c68268c from=translated src=- shape=079540ea vocab=3c0bd5ff
-/
theorem cyclicHilbert90_exists_nonzero_div_of_norm_eq_one
    {g : Gal(L/K)} (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) :
    ∃ y : L, y ≠ 0 ∧ y / g y = x := by
  let : IsCyclic (Gal(L/K)) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg⟩
  rcases groupCohomology.exists_div_of_norm_eq_one (K := K) (L := L) hg hx with ⟨y, hy⟩
  exact ⟨y, Units.ne_zero y, hy⟩

/-- The `β^{σ-1}` orientation of Hilbert 90.  Mathlib's
standard endpoint uses `β / σ(β)`; applying it to the inverse generator
gives the ambient-power quotient `σ(β) / β` for the specified generator.
@isnad1 id=ex.2h4v.s9.f89bfbb31e21 from=translated src=- shape=97264bde vocab=54846d3d
-/
theorem cyclicHilbert90_exists_gal_div_of_norm_eq_one
    {g : Gal(L/K)} (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, g (y : L) / y = x := by
  let : IsCyclic (Gal(L/K)) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg⟩
  have hg_inv : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g⁻¹ := by
    intro σ
    rw [Subgroup.zpowers_inv]
    exact hg σ
  rcases groupCohomology.exists_div_of_norm_eq_one
      (K := K) (L := L) (g := g⁻¹) hg_inv hx with ⟨z, hz⟩
  refine ⟨g⁻¹ • z, ?_⟩
  simpa using hz

/-- Unit-valued version of Cyclic Hilbert theorem 90.
@isnad1 id=ex.2h4v.s9.2d84f21ed12f from=translated src=- shape=bacc03a8 vocab=834b4c31
-/
theorem cyclicHilbert90_exists_unit_div_of_norm_eq_one
    {g : Gal(L/K)} (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) {x : Lˣ}
    (hx : Algebra.norm K (x : L) = 1) :
    ∃ y : Lˣ, x = y / (g • y) := by
  let : IsCyclic (Gal(L/K)) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg⟩
  rcases groupCohomology.exists_div_of_norm_eq_one (K := K) (L := L) hg hx with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  ext
  simpa using hy.symm

/-- Rearranged unit-valued version of Cyclic Hilbert theorem 90.
@isnad1 id=ex.2h4v.s9.ef4394b43c5f from=translated src=- shape=ec3767ef vocab=0f063796
-/
theorem cyclicHilbert90_exists_unit_mul_gal_of_norm_eq_one
    {g : Gal(L/K)} (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) {x : Lˣ}
    (hx : Algebra.norm K (x : L) = 1) :
    ∃ y : Lˣ, x * (g • y) = y := by
  rcases cyclicHilbert90_exists_unit_div_of_norm_eq_one (K := K) (L := L) hg hx with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [hy]
  exact div_mul_cancel y (g • y)

end CyclicHilbert90

section IntegralHilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable [IsGalois K L]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra A B] [Algebra A L] [Algebra A K] [Algebra B L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
variable [IsDomain A] [IsIntegralClosure B A L]

/-- Integral Hilbert 90 for a cyclic Galois extension.
@isnad1 id=ex.2h6v.s10.19a4ca1b32b8 from=translated src=- shape=a6045e0a vocab=33f9c730
-/
theorem cyclicHilbert90_exists_mul_galRestrict_of_norm_eq_one
    {g : Gal(L/K)} (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) {η : B}
    (hη : Algebra.norm K ((algebraMap B L) η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * ((galRestrict A K L B) g) ε = ε := by
  let : IsCyclic (Gal(L/K)) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg⟩
  exact groupCohomology.exists_mul_galRestrict_of_norm_eq_one hg hη

end IntegralHilbert90

end KummerTheory
