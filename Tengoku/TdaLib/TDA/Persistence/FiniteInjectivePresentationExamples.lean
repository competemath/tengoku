import Tengoku.TdaLib.TDA.Persistence.FiniteInjectivePresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal-downset and finite-presentation examples

These examples use rational coefficients to exercise a nonzero downset over an
infinite poset, coextension away from its endpoint, multiplicity-two coordinates,
and the zero-module and empty-poset boundaries.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteInjectivePresentation.Examples

open CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

namespace Downset

open PrincipalDownsetInjective

/-- A principal downset can have a nonzero fiber strictly before its endpoint.
@isnad1 id=ex.0h0v.s8.4f0f0f181302 from=translated src=- shape=d774adcb vocab=c27e0e94
-/
theorem earlier_fiber_nonzero :
    ∃ x : (PrincipalDownsetInjective.module (k := ℚ) (2 : ℕ)).obj 0, x ≠ 0 := by
  refine ⟨SupportInterval.one (Set.Iic (2 : ℕ)) (by decide), ?_⟩
  intro h
  exact (one_ne_zero : (1 : ℚ) ≠ 0) (congrArg Subtype.val h)

/-- The constant scalar module on an infinite poset.-/
abbrev scalarLine : PModule ℚ ℕ := (Functor.const ℕ).obj (ModuleCat.of ℚ ℚ)

/-- The extended functional has a nonzero coefficient away from the endpoint.
@isnad1 id=eq.0h0v.s9.7c9c32fe0ab3 from=translated src=- shape=4237621f vocab=cdac2441
-/
theorem off_endpoint_coefficient :
    (((extension 2 scalarLine (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).app 0).hom (7 : ℚ) : ℚ) = 7 := by
  rw [extension_app_val]
  simp [scalarLine, structureMapLinear, structureMap]

/-- Coextension is zero immediately beyond the terminal support grade.
@isnad1 id=eq.0h0v.s9.141d0ce4ff35 from=translated src=- shape=4237621f vocab=cdac2441
-/
theorem outside_coefficient :
    (((extension 2 scalarLine (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).app 3).hom (7 : ℚ) : ℚ) = 0 := by
  rw [extension_app_val]
  simp

/-- Injectivity holds on the infinite indexing poset as well.
@isnad1 id=injectiv.0h0v.s5.224c6592bd94 from=translated src=- shape=1f9bed29 vocab=7972c9a6
-/
theorem infinite_poset_injective :
    Injective (PrincipalDownsetInjective.module (k := ℚ) (2 : ℕ)) := inferInstance

end Downset

/-- A two-dimensional fiber at a single grade.-/
abbrev doubleModule : PModule ℚ (Fin 1) :=
  (Functor.const (Fin 1)).obj (ModuleCat.of ℚ (ℚ × ℚ))

/--
@isnad1 id=finitedi.0h1v.s7.0d99c1137e91 from=translated src=- shape=a270787e vocab=8873554a
-/
instance doubleModule_finiteDimensional (p : Fin 1) :
    FiniteDimensional ℚ (doubleModule.obj p) :=
  inferInstanceAs (FiniteDimensional ℚ (ℚ × ℚ))

/-- Both scalar coordinates survive as separate occurrences at the same grade.
@isnad1 id=eq.0h0v.s5.42a45aababb4 from=translated src=- shape=9fc4802a vocab=ce472a34
-/
theorem repeated_occurrence_count : Fintype.card (Index doubleModule) = 2 := by
  simp [Index, doubleModule, Module.finrank_prod]

private abbrev doubleIndex (j : Fin 2) : Index doubleModule :=
  ⟨0, ⟨j.val, by simpa [doubleModule, Module.finrank_prod] using j.isLt⟩⟩

/-- Distinct coordinates retain distinct tags even though their injectives agree.
@isnad1 id=ex.0h0v.s7.c65926f5a970 from=translated src=- shape=8b4b02da vocab=db235af0
-/
theorem repeated_occurrences_distinct :
    ∃ s t : Index doubleModule, s ≠ t ∧ family doubleModule s = family doubleModule t := by
  refine ⟨doubleIndex 0, doubleIndex 1, ?_, rfl⟩
  intro h
  have hv := congrArg (fun t : Index doubleModule => t.2.val) h
  norm_num [doubleIndex] at hv

/-- Projection of an embedded basis vector reads one in its own coordinate and
zero in the other coordinate.
@isnad1 id=ex.0h0v.s13.133340ed8b45 from=translated src=- shape=368dc696 vocab=04ef0e52
-/
theorem repeated_coordinate_values :
    ∃ (s t : Index doubleModule) (x : doubleModule.obj 0), s ≠ t ∧
      (((biproduct.π (family doubleModule) s).app 0).hom
        (((embedding doubleModule).app 0).hom x) : ℚ) = 1 ∧
      (((biproduct.π (family doubleModule) t).app 0).hom
        (((embedding doubleModule).app 0).hom x) : ℚ) = 0 := by
  have hne : doubleIndex 0 ≠ doubleIndex 1 := by
    intro h
    have hv := congrArg (fun t : Index doubleModule => t.2.val) h
    norm_num [doubleIndex] at hv
  refine ⟨doubleIndex 0, doubleIndex 1,
    Module.finBasis ℚ (doubleModule.obj 0) (doubleIndex 0).2, hne, ?_, ?_⟩
  · rw [embedding_coordinate]
    simp [coordinate]
  · rw [embedding_coordinate]
    simp [coordinate]

/-- The categorical zero module has zero-dimensional fibers.-/
private instance zeroFiberSubsingleton {P : Type} [PartialOrder P] (p : P) :
    Subsingleton ((0 : PModule ℚ P).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance zeroFiberFiniteDimensional {P : Type} [PartialOrder P] (p : P) :
    FiniteDimensional ℚ ((0 : PModule ℚ P).obj p) := by infer_instance

/-- The zero module has no coordinate occurrences.
@isnad1 id=eq.0h0v.s8.84aeb6c96d6f from=translated src=- shape=04d255d8 vocab=8dc98e32
-/
theorem zero_occurrences : Fintype.card (Index (0 : PModule ℚ (Fin 2))) = 0 := by
  simp [Index, Module.finrank_zero_of_subsingleton]

/-- The zero module still has its actual mono into an injective target.
@isnad1 id=and.0h0v.s10.5b9cc55a0c66 from=translated src=- shape=d51b3138 vocab=f65f0d5e
-/
theorem zero_presentation :
    Mono (presentation (0 : PModule ℚ (Fin 2))).f ∧
      Injective (presentation (0 : PModule ℚ (Fin 2))).J := ⟨inferInstance, inferInstance⟩

/-- The construction includes the empty indexing poset.
@isnad1 id=and.0h0v.s9.fab79c476f1b from=translated src=- shape=406d63a3 vocab=2b42a12d
-/
theorem empty_poset :
    Fintype.card (Index (0 : PModule ℚ (Fin 0))) = 0 ∧
      Mono (embedding (0 : PModule ℚ (Fin 0))) := ⟨by simp, inferInstance⟩

/-- The injective principal downset has the actual chosen splitting.
@isnad1 id=eq.0h0v.s9.e3700dedc5cc from=translated src=- shape=1471e48e vocab=71701a06
-/
theorem downset_splitting :
    embedding (PrincipalDownsetInjective.module (k := ℚ) (1 : Fin 2)) ≫
        retraction (PrincipalDownsetInjective.module (k := ℚ) (1 : Fin 2)) =
      𝟙 (PrincipalDownsetInjective.module (k := ℚ) (1 : Fin 2)) :=
  embedding_retraction _

end TDA.Persistence.FiniteInjectivePresentation.Examples
