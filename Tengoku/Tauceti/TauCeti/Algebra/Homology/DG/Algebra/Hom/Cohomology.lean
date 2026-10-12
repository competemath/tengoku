/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.Homology.DG.Algebra.Cohomology
public import Tengoku.Tauceti.TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic

/-!
# Functoriality of the cohomology algebra

A morphism of differential graded algebras induces a graded algebra homomorphism on cohomology,
compatibly with identities and composition.

The induced map is obtained in two stages.  Commutation with the differentials first restricts the
underlying algebra homomorphism to cycles and sends boundaries to boundaries.  The quotient
universal property then descends this map to cohomology.  Its preservation of the cohomological
grading follows from the description of a homogeneous cohomology class by a homogeneous cycle
representative.

Functoriality is what makes cohomology a usable invariant: it is the source of the notion of a
quasi-isomorphism, a morphism inducing an isomorphism on cohomology, and it is the shadow on
cohomology of the comparison between differential graded algebras and `A∞` algebras.

## Main definitions

* `TauCeti.DGAlgHom.cyclesMap`: the induced graded algebra homomorphism on cycles.
* `TauCeti.DGAlgHom.cohomologyMap`: the induced graded algebra homomorphism on cohomology.

## Main results

* `TauCeti.DGAlgHom.cohomologyMap_mk`: the cohomology map sends the class of a cycle to the class
  of its image.
* `TauCeti.DGAlgHom.cohomologyMap_id` and `TauCeti.DGAlgHom.cohomologyMap_comp`: passage to
  cohomology preserves identities and composition.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {hC : IsDGAlgebra 𝒞 dC}

/-- A DG algebra morphism restricts to a graded algebra homomorphism on cycles. -/
def cyclesMap (f : DGAlgHom hA hB) : hA.cyclesDeg →ₐᵍ[R] hB.cyclesDeg where
  __ := (f.toGradedAlgHom.toAlgHom.comp hA.cycles.val).codRestrict hB.cycles fun z => by
    rw [hB.mem_cycles]
    calc
      dB ((f.toGradedAlgHom.toAlgHom.comp hA.cycles.val) z) =
          f (dA (z : A)) := f.map_d (z : A)
      _ = 0 := by rw [hA.mem_cycles.mp z.2, map_zero]
  map_mem hz :=
    hB.mem_cyclesDeg.mpr (f.toGradedAlgHom.map_mem (hA.mem_cyclesDeg.mp hz))

@[simp]
theorem cyclesMap_apply_coe (f : DGAlgHom hA hB) (z : hA.cycles) :
    ((f.cyclesMap z : hB.cycles) : B) = f (z : A) := (rfl)

/-- The restriction of a DG algebra morphism to cycles sends boundaries to boundaries. -/
theorem cyclesMap_mem_boundaries (f : DGAlgHom hA hB) {z : hA.cycles}
    (hz : z ∈ hA.boundaries) : f.cyclesMap z ∈ hB.boundaries := by
  rw [hA.mem_boundaries] at hz
  obtain ⟨a, ha⟩ := hz
  have himage : f.cyclesMap z =
      (⟨dB (f a), hB.map_mem_cycles (f a)⟩ : hB.cycles) := by
    apply Subtype.ext
    calc
      (f.cyclesMap z : B) = f (z : A) := cyclesMap_apply_coe f z
      _ = f (dA a) := congrArg f ha.symm
      _ = dB (f a) := (f.map_d a).symm
  rw [himage]
  exact hB.map_mem_boundaries (f a)

/-- The boundary ideal of the source lands in the boundary ideal of the target: the hypothesis
under which the map on cycles descends to the quotients. -/
theorem boundaries_le_comap_boundaries (f : DGAlgHom hA hB) :
    hA.boundaries.asIdeal ≤ hB.boundaries.asIdeal.comap f.cyclesMap.toAlgHom := fun _z hz =>
  TwoSidedIdeal.mem_asIdeal.mpr (f.cyclesMap_mem_boundaries (TwoSidedIdeal.mem_asIdeal.mp hz))

/-- A DG algebra morphism induces a graded algebra homomorphism on cohomology. -/
noncomputable def cohomologyMap (f : DGAlgHom hA hB) :
    hA.cohomologyGrading →ₐᵍ[R] hB.cohomologyGrading where
  __ := Ideal.quotientMapₐ hB.boundaries.asIdeal f.cyclesMap.toAlgHom
    f.boundaries_le_comap_boundaries
  map_mem := fun {p} {x} hx => by
    obtain ⟨z, hz, rfl⟩ := hA.mem_cohomologyGrading.mp hx
    exact hB.mem_cohomologyGrading.mpr
      ⟨f.cyclesMap z, f.toGradedAlgHom.map_mem hz, (Ideal.quotient_map_mkₐ ..).symm⟩

end DGAlgHom

end TauCeti
