import Tengoku.TdaLib.TDA.Persistence.GradedFree
import Tengoku.TdaLib.TDA.Persistence.RankExact
import Tengoku.Seed.LinearAlgebra.Finsupp.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hooks with infinite death

The principal-upset module is the graded free module with one generator at its birth.
Its supported fibers identify with the coefficient ring and its other fibers vanish.
Evaluation at birth identifies its morphisms with the target's birth fiber, so a
surjection at that one fiber suffices to lift a morphism. This includes the infinite-death
hooks of Botnan et al., arXiv:2208.00300v3, Section 2.14, over a field.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.HookInfinity

open CategoryTheory

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- One generator born at the lower endpoint of the principal upset.-/
abbrev generators (i : P) : GradedFree.GradedGenerators.{v,0} P where
  Carrier := Unit
  grade _ := i

/-- The infinite-death hook, represented by the free module on one graded generator.-/
noncomputable abbrev module (i : P) : PModule.{u,v,u} R P := GradedFree.module (R := R) (generators i)

/-- The generating vector at birth.-/
noncomputable def birth (i : P) : (module (R := R) i).obj i :=
  GradedFree.birth (R := R) (generators i) ()

/-- The fiber at any point of the principal upset is one copy of the coefficient ring.-/
noncomputable def fiberEquivOfLe {i a : P} (hia : i ≤ a) :
    (module (R := R) i).obj a ≃ₗ[R] R :=
  (GradedFree.fiberEquiv (R := R) (generators i) a).trans
    (Finsupp.uniqueLinearEquiv R R ⟨(), hia⟩)

/-- The supported-fiber equivalence reads the unique generator coefficient.
@isnad1 id=eq.1h5v.s9.1eb353d1d6e5 from=translated src=- shape=2412273e vocab=29017513
-/
@[simp] theorem fiberEquivOfLe_apply {i a : P} (hia : i ≤ a)
    (x : (module (R := R) i).obj a) : fiberEquivOfLe hia x = x.val () := rfl

/-- Structure maps within the principal upset preserve the coefficient.
@isnad1 id=eq.2h6v.s10.d820bddc6733 from=translated src=- shape=3c162dd7 vocab=13106fe4
-/
theorem fiberEquivOfLe_structureMap {i a b : P} (hia : i ≤ a) (hab : a ≤ b)
    (x : (module (R := R) i).obj a) :
    fiberEquivOfLe (hia.trans hab) (structureMapLinear (module i) hab x) =
      fiberEquivOfLe hia x := rfl

/-- Outside the principal upset, the fiber consists only of zero.
@isnad1 id=eq.1h5v.s7.6cdeda697b9c from=translated src=- shape=8be2a724 vocab=8fc09975
-/
theorem fiber_eq_zero_of_not_le {i a : P} (hia : ¬ i ≤ a)
    (x : (module (R := R) i).obj a) : x = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro g
  cases g
  exact (Finsupp.mem_supported' R x.val).mp x.property () hia

/-- A choice of birth value extends to a morphism from the infinite-death hook.-/
noncomputable def fromBirth (i : P) (M : PModule.{u,v,u} R P) (m : M.obj i) :
    module (R := R) i ⟶ M :=
  GradedFree.lift (R := R) (generators i) M (fun _ => m)

/-- The extended morphism takes the generating vector to the chosen birth value.
@isnad1 id=eq.0h5v.s9.7ba43f1979a7 from=translated src=- shape=74f0af45 vocab=db68017e
-/
@[simp] theorem fromBirth_birth (i : P) (M : PModule.{u,v,u} R P) (m : M.obj i) :
    ((fromBirth i M m).app i).hom (birth i) = m :=
  GradedFree.lift_birth (R := R) (generators i) M (fun _ => m) ()

/-- Evaluation on the birth generator determines a morphism from a principal upset.
@isnad1 id=eq.1h6v.s10.d51a5e43c7a9 from=translated src=- shape=a7d7d6e4 vocab=117c05c6
-/
theorem hom_ext {i : P} {M : PModule.{u,v,u} R P} {α β : module (R := R) i ⟶ M}
    (h : (α.app i).hom (birth i) = (β.app i).hom (birth i)) : α = β := by
  have hα := GradedFree.lift_unique (R := R) (generators i) M
    (fun _ => (α.app i).hom (birth i)) α (by intro g; cases g; rfl)
  have hβ := GradedFree.lift_unique (R := R) (generators i) M
    (fun _ => (α.app i).hom (birth i)) β (by intro g; cases g; exact h.symm)
  exact hα.trans hβ.symm

/-- Morphisms from an infinite-death hook correspond to arbitrary birth-fiber vectors.-/
noncomputable def homEquivFiber (i : P) (M : PModule.{u,v,u} R P) :
    (module (R := R) i ⟶ M) ≃ M.obj i where
  toFun α := (α.app i).hom (birth i)
  invFun m := fromBirth i M m
  left_inv _α := hom_ext (fromBirth_birth i M _)
  right_inv m := fromBirth_birth i M m

/-- Only surjectivity at birth is needed to lift a morphism from a principal upset.
@isnad1 id=ex.1h7v.s9.fe199e04acf2 from=translated src=- shape=a1f19e9f vocab=531116aa
-/
theorem exists_lift_of_birth_surjective {i : P} {M N : PModule.{u,v,u} R P}
    (π : M ⟶ N) (hπ : Function.Surjective (π.app i).hom)
    (α : module (R := R) i ⟶ N) : ∃ β : module (R := R) i ⟶ M, β ≫ π = α := by
  obtain ⟨m, hm⟩ := hπ ((α.app i).hom (birth i))
  refine ⟨fromBirth i M m, ?_⟩
  apply hom_ext
  change (π.app i).hom (((fromBirth i M m).app i).hom (birth i)) = _
  rw [fromBirth_birth]
  exact hm

/-- Infinite-death hooks lift along every componentwise surjective natural transformation.
@isnad1 id=ex.1h7v.s9.72f3945973a3 from=translated src=- shape=cd4459e4 vocab=531116aa
-/
theorem exists_lift_of_surjective {i : P} {M N : PModule.{u,v,u} R P}
    (π : M ⟶ N) (hπ : ∀ a, Function.Surjective (π.app a).hom)
    (α : module (R := R) i ⟶ N) : ∃ β : module (R := R) i ⟶ M, β ≫ π = α :=
  exists_lift_of_birth_surjective π (hπ i) α

/-- Infinite-death hooks in particular lift against rank exact quotient maps.
@isnad1 id=ex.1h9v.s8.d2b3b4c84b2d from=translated src=- shape=067a53f9 vocab=11d347f3
-/
theorem exists_lift_rankExact {k : Type u} [Field k]
    {i : P} {L M N : PModule.{u,v,u} k P} {ι : L ⟶ M} {π : M ⟶ N}
    (hs : IsRankExact ι π) (α : module (R := k) i ⟶ N) :
    ∃ β : module (R := k) i ⟶ M, β ≫ π = α :=
  exists_lift_of_surjective π hs.surjective α

end TDA.Persistence.HookInfinity
