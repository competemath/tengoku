/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Stalk
import Tengoku.Hironaka.Hironaka.Algebra.Local.RegularSystem
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Cotangent
import Tengoku.Hironaka.Hironaka.Scheme.Smooth.AdaptedCoordinates
import Tengoku.Hironaka.Hironaka.Scheme.Snc.RelativeDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derivations dual to a regular system of parameters at any point

The input for [Hau14, Proposition 5.4 (6)] at a non-closed point
(`Hironaka.Scheme.Snc.InducedCoordinates`): at a point `x` of a scheme `X` smooth over a perfect
field `k`, a regular system of parameters `z_1, …, z_n` of `𝒪_{X,x}` admits dual derivations
`D_1, …, D_n : 𝒪_{X,x} → 𝒪_{X,x}` over `k` with `D_i z_j = δ_{ij}` (`exists_derivation_dual`). At a
closed point this is the route of `Hironaka.Scheme.Snc.EtaleParameters` through étale coordinates;
at a general point it needs the injectivity of the conormal map
(`Hironaka.Algebra.RegularSmooth.Cotangent`):

* `Ω[𝒪_{X,x}⁄k]` is free of finite rank — the base change of `Ω[Γ(V)⁄k]` for a standard smooth
  affine neighbourhood `V` of `x` (`exists_affineOpen_isStandardSmooth` of
  `Hironaka.Scheme.Snc.RelativeDimension`; `free_finite_kaehlerDifferential_stalk`);
* the conormal map `𝔪_x/𝔪_x² → κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` is injective because `κ(x)` is formally smooth
  over the perfect field `k` ([Sta, Tag 00TU]; `injective_cotangentSpaceToTensor`, with Mathlib's
  `Algebra.FormallySmooth.of_perfectField`), so the classes of `dz_1, …, dz_n` are linearly
  independent in `κ(x) ⊗ Ω` (the `z_i` are a basis of `𝔪_x/𝔪_x²`);
* a linear map `𝒪^n → Ω` into a finite free module over a local ring which is injective modulo the
  maximal ideal is a split injection (Mathlib's
  `IsLocalRing.split_injective_iff_lTensor_residueField_injective`); the retraction composed with
  the universal derivation `d` and the coordinate projections gives the `D_i`.

Sources: [Hau14, Proposition 5.4 (6)]; [Hau03, Appendix C (7)]; [Sta, Tag 00TU].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `Ω[𝒪_{X,x}⁄k]` is a finite free module at every point of a scheme smooth over `k`: the base
change of `Ω[Γ(V)⁄k]`, free and finite on a standard smooth affine neighbourhood `V ∋ x`.-/
theorem free_finite_kaehlerDifferential_stalk [Smooth f] (x : X) :
    letI := f.stalkAlgebra x
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧
      Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := by
  obtain ⟨U, hU, hxU, hstd⟩ := exists_affineOpen_isStandardSmooth f x
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sectionsAlgebra hU
  set e := (IsLocalizedModule.isBaseChange (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk x))).equiv
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- The stalk of a scheme smooth over `k` is essentially of finite type over `k` (the form of
`essFiniteType_stalk` without a relative dimension).-/
theorem essFiniteType_stalk_of_smooth [Smooth f] (x : X) :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sectionsAlgebra hU
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk x)

/-- The residue field of the stalk is essentially of finite type over `k`.-/
theorem essFiniteType_residueField_stalk_of_smooth [Smooth f] (x : X) :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (ResidueField (X.presheaf.stalk x)) := by
  let _ := f.stalkAlgebra x
  have := essFiniteType_stalk_of_smooth f x
  have : Algebra.EssFiniteType (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) :=
    inferInstanceAs (Algebra.EssFiniteType (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x)))
  exact Algebra.EssFiniteType.comp k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))

end AlgebraicGeometry
