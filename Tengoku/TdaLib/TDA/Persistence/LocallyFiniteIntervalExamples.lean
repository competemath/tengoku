import Tengoku.TdaLib.TDA.Persistence.FiniteObservation
import Tengoku.TdaLib.TDA.Persistence.RealIntervalExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/uda-lab/tda-lib@6880b1ef1fcf, `TDA/Persistence/LocallyFiniteIntervalExamples.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

namespace TDA.Persistence.LocalFiniteExamples

open CategoryTheory CategoryTheory.Limits

private noncomputable def oneSample (t : ℝ) : Fin 1 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun _ => t) (Subsingleton.strictMono _)

/-- A locally finite algebraic family of convex real intervals has
finite-dimensional fibers, even when its occurrence type is infinite.
@isnad1 id=finitedi.2h4v.s7.4c7bce7bbc75 from=translated src=- shape=c19135ff vocab=e9b41475
-/
theorem locallyFinite_family_finiteDimensional {k : Type*} [Field k] {J : Type}
    (S : J → Set ℝ) (hS : ∀ j, (S j).OrdConnected)
    (hlocal : ∀ t : ℝ, {j : J | t ∈ S j}.Finite) (t : ℝ) :
    FiniteDimensional k ((AlgebraicFamily.familyModule
      (fun j => SupportInterval.module (k := k) (S j) (hS j))).obj t) := by
  classical
  let V : Set J := {j | t ∈ S j}
  letI : Fintype V := (hlocal t).fintype
  let Fv : V → PModule.{_,0,_} k ℝ :=
    fun j => SupportInterval.module (k := k) (S j.val) (hS j.val)
  have hprod : FiniteDimensional k ((RealBarcode.familyModule Fv).obj t) := by
    change FiniteDimensional k (∀ j : V, SupportInterval.fiber (k := k) (S j.val) t)
    infer_instance
  have hfinite : FiniteDimensional k ((AlgebraicFamily.familyModule Fv).obj t) := by
    exact Module.Finite.equiv ((AlgebraicFamily.finiteProductIso Fv).app t).toLinearEquiv.symm
  let c := oneSample t
  have hcover (j : J) : (∃ i : Fin 1, c i ∈ S j) → j ∈ V := by
    rintro ⟨i, hi⟩
    exact hi
  let e := FiniteObservation.visibleFamilyIso (k := k) c S hS V hcover
  change FiniteDimensional k
    ((reindex c.toOrderHom (AlgebraicFamily.familyModule
      (fun j => SupportInterval.module (k := k) (S j) (hS j)))).obj 0)
  exact Module.Finite.equiv ((e.app 0).toLinearEquiv.symm)

/-- The accumulating family has a countably infinite occurrence type but
finite-dimensional fibers at every real parameter.-/
private theorem accumulatingOrdConnected (n : ℕ) :
    (RealIntervalExamples.accumulatingInterval n).OrdConnected := by
  change (Set.Ioc (RealIntervalExamples.endpoint (n + 1))
    (RealIntervalExamples.endpoint n)).OrdConnected
  exact Set.ordConnected_Ioc

noncomputable def accumulatingFamily : PModule ℚ ℝ :=
  AlgebraicFamily.familyModule (fun n : ℕ => SupportInterval.module (k := ℚ)
    (RealIntervalExamples.accumulatingInterval n) (accumulatingOrdConnected n))

/--
@isnad1 id=finitedi.0h1v.s6.98a18d94ff16 from=translated src=- shape=1fd56d81 vocab=93a082af
-/
theorem accumulatingFamily_finiteDimensional (t : ℝ) :
    FiniteDimensional ℚ (accumulatingFamily.obj t) := by
  exact locallyFinite_family_finiteDimensional
    RealIntervalExamples.accumulatingInterval
    accumulatingOrdConnected
    RealIntervalExamples.activeIndices_finite t

/-- Every occurrence contributes a nonzero fiber at its selected point.
@isnad1 id=ex.0h1v.s8.3482fe4818f7 from=translated src=- shape=91d95bc7 vocab=cd2af190
-/
theorem accumulatingFamily_nonzero_at_endpoint (n : ℕ) :
    ∃ y : accumulatingFamily.obj (RealIntervalExamples.endpoint n), y ≠ 0 := by
  let F : ℕ → PModule ℚ ℝ := fun j => SupportInterval.module (k := ℚ)
    (RealIntervalExamples.accumulatingInterval j) (accumulatingOrdConnected j)
  let x : (F n).obj (RealIntervalExamples.endpoint n) :=
    SupportInterval.one (k := ℚ) (RealIntervalExamples.accumulatingInterval n)
      (RealIntervalExamples.occurrence_point_lies_in_interval n)
  let y : accumulatingFamily.obj (RealIntervalExamples.endpoint n) :=
    ((AlgebraicFamily.inclusion F n).app (RealIntervalExamples.endpoint n)).hom x
  refine ⟨y, ?_⟩
  intro hy
  have hx : x ≠ 0 := by
    intro he
    have hv := congrArg (fun z : SupportInterval.fiber (k := ℚ)
      (RealIntervalExamples.accumulatingInterval n)
      (RealIntervalExamples.endpoint n) => (z : ℚ)) he
    simp [x, SupportInterval.one] at hv
  have hc := congrArg (DirectSum.component ℚ ℕ
    (fun j => (F j).obj (RealIntervalExamples.endpoint n)) n) hy
  change DirectSum.component ℚ ℕ
    (fun j => (F j).obj (RealIntervalExamples.endpoint n)) n
      (((AlgebraicFamily.inclusion F n).app
        (RealIntervalExamples.endpoint n)).hom x) = 0 at hc
  rw [AlgebraicFamily.inclusion_apply_self] at hc
  exact hx hc

/-- The empty occurrence family is the zero persistence module itself.
@isnad1 id=iszero.0h0v.s5.8953760607b5 from=translated src=- shape=7cc977bf vocab=895c2b54
-/
theorem emptyFamily_isZero :
    IsZero (AlgebraicFamily.familyModule RealIntervalExamples.emptyFamily) := by
  apply Functor.isZero
  intro t
  rw [ModuleCat.isZero_iff_subsingleton]
  exact RealIntervalExamples.empty_family_fiber_is_subsingleton t

end TDA.Persistence.LocalFiniteExamples
