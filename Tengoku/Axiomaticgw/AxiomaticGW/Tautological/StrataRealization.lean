/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Tautological.StrataModule
public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.StableCurve
public import Tengoku.Seed.LinearAlgebra.Quotient.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realizing strata in a cohomology target

The free strata module is combinatorial. A geometric model of
`H^*(Mbar_(g,S))` supplies a linear realization sending each decorated graph
to its gluing pushforward. Relations are imposed only when the realization
proves that they lie in its kernel. This keeps the distinction between a
formal quotient and an actual cohomology class explicit.
-/

@[expose] public section

namespace AxiomaticGW

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  (C : StableCurveCohomology R) (g : ℕ) (S : Type) [Fintype S]

/-- Restrict the target's `R`-module structure along `algebraMap ℚ R` for
the rational strata realization map.-/
@[reducible]
def strataRealizationModule : Module ℚ (C.H g S) :=
  Module.compHom (C.H g S) (algebraMap ℚ R)

attribute [local instance] strataRealizationModule

/-- A realization of the fixed `(g,S)` strata module in an abstract stable-
curve cohomology target. The target is not assumed to be the cohomology of a
constructed moduli space.-/
structure StrataRealization where
  /-- Linear map sending a formal stratum combination to cohomology.-/
  map : StrataModule g S →ₗ[ℚ] C.H g S
  /-- A decorated stratum of codimension `d` realizes in codimension `d`.-/
  map_basis_degree : ∀ x,
    map (StrataModule.basis x) ∈ (C.H g S).degree x.codimension

namespace StrataRealization

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

/-- Relations invisible in the chosen cohomology realization.-/
noncomputable def kernel (A : StrataRealization C g S) :
    Submodule ℚ (StrataModule g S) := LinearMap.ker A.map

theorem mem_kernel_iff (A : StrataRealization C g S)
    (x : StrataModule g S) : x ∈ A.kernel ↔ A.map x = 0 := Iff.rfl

/-- Dimension relations vanish under every degree-preserving realization of
a stable arity.-/
theorem dimensionRelations_le_kernel (A : StrataRealization C g S)
    (h : StableArity g S) : StrataModule.dimensionRelations ≤ A.kernel := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨s, hs, rfl⟩
  change StrataModule.basis s ∈ A.kernel
  rw [A.mem_kernel_iff]
  exact C.eq_zero_of_dimension_lt g S h s.codimension
    (A.map (StrataModule.basis s)) (A.map_basis_degree s) hs

/-- Factor a realization through any relation submodule contained in its
kernel.-/
noncomputable def factor (A : StrataRealization C g S)
    (relations : Submodule ℚ (StrataModule g S))
    (hrelations : relations ≤ A.kernel) :
    StrataModule.KnownRelationsQuotient relations →ₗ[ℚ] C.H g S :=
  relations.liftQ A.map hrelations

@[simp]
theorem factor_comp_quotientMk (A : StrataRealization C g S)
    (relations : Submodule ℚ (StrataModule g S))
    (hrelations : relations ≤ A.kernel) :
    (A.factor relations hrelations).comp
        (StrataModule.quotientMk relations) = A.map := by
  exact Submodule.liftQ_mkQ relations A.map hrelations

theorem factor_mk (A : StrataRealization C g S)
    (relations : Submodule ℚ (StrataModule g S))
    (hrelations : relations ≤ A.kernel)
    (x : StrataModule g S) :
    A.factor relations hrelations (StrataModule.quotientMk relations x) =
      A.map x := by
  exact congrArg (fun f ↦ f x)
    (A.factor_comp_quotientMk relations hrelations)

end StrataRealization

end AxiomaticGW
