import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Algebra.RightModuleFiniteType
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import Tengoku
import Tengoku.Seed.Algebra.Category.ModuleCat.Biproducts
import Tengoku.Seed.LinearAlgebra.Projection
import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.RingTheory.LocalRing.Basic
import Tengoku.Seed.RingTheory.Nilpotent.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local endomorphism rings of finite-dimensional indecomposable modules

Fitting decomposition shows that every endomorphism of a finite-dimensional
indecomposable module is either invertible or nilpotent.  Consequently its
endomorphism ring is local.  The result is then transported through the fully
faithful inclusion of finitely generated modules into all modules.

The Fitting argument and the two small transport lemmas are adapted from
`CartanDeterminant.RepresentationTheory.IndecomposableLocalEnd` and
`CartanDeterminant.CategoryTheory.LinearEndTransport` at
homological-conjectures commit `eade4e75`.

The file also records a ring-level form: a finite-dimensional algebra with
no nontrivial idempotents is local.  This follows by applying Fitting's lemma
to its right regular module.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture

universe u₁ u₂ v

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C] [Preadditive C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D]

/-- A fully faithful additive functor identifies the endomorphism rings of an
object and its image.-/
def endRingEquivOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X : C) :
    End X ≃+* End (F.obj X) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f

/--
@isnad1 id=eq.0h5v.s8.97b48138749b from=translated src=- shape=4faae606 vocab=cb7994da
-/
@[simp]
theorem endRingEquivOfFullyFaithful_apply
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (X : C) (f : End X) :
    endRingEquivOfFullyFaithful F X f = F.map f :=
  rfl

end CategoryTheory.Functor

universe u

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- Left multiplication identifies a ring with the endomorphism ring of its
right regular module.-/
noncomputable def rightRegularEndEquiv (R : Type v) [Ring R] :
    R ≃+* Module.End Rᵐᵒᵖ R where
  toFun a := LinearMap.mulLeft Rᵐᵒᵖ a
  invFun f := f 1
  left_inv a := by simp
  right_inv f := by
    apply LinearMap.ext
    intro x
    have hx := f.map_smul (MulOpposite.op x) (1 : R)
    simpa using hx.symm
  map_add' a b := by
    apply LinearMap.ext
    intro x
    exact add_mul a b x
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply]

/-- A finite-dimensional indecomposable module has the Fitting alternative:
each endomorphism is invertible or nilpotent.
@isnad1 id=or.1h4v.s7.45c0f488fba7 from=translated src=- shape=cdd49773 vocab=c497b82f
-/
theorem isUnit_or_isNilpotent_of_finite_indecomposable
    [Module.Finite k A] (M : ModuleCat.{v} A) [Module.Finite k M]
    (hM : Indecomposable M) (f : End M) :
    IsUnit f ∨ IsNilpotent f := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  letI : Module.Finite A M :=
    Module.Finite.of_restrictScalars_finite k A M
  letI : IsArtinian A M := inferInstance
  letI : IsNoetherian A M := inferInstance
  let φ : Module.End A M := f.hom
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    φ.eventually_isCompl_ker_pow_range_pow
  let n := N + 1
  have hn : N ≤ n := Nat.le_succ N
  have hcompl : IsCompl (LinearMap.ker (φ ^ n))
      (LinearMap.range (φ ^ n)) := hN n hn
  let K : ModuleCat.{v} A := ModuleCat.of A (LinearMap.ker (φ ^ n))
  let R : ModuleCat.{v} A := ModuleCat.of A (LinearMap.range (φ ^ n))
  let eProd : ModuleCat.of A
      (LinearMap.ker (φ ^ n) × LinearMap.range (φ ^ n)) ≅ M :=
    (Submodule.prodEquivOfIsCompl _ _ hcompl).toModuleIso
  let e : M ≅ K ⊞ R :=
    eProd.symm.trans (ModuleCat.biprodIsoProd K R).symm
  rcases hM.2 K R e with hK | hR
  · left
    have hker : LinearMap.ker (φ ^ n) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      let y : K := ⟨x, hx⟩
      haveI : Subsingleton K := ModuleCat.subsingleton_of_isZero hK
      exact congrArg Subtype.val (Subsingleton.elim y 0)
    have hnpos : 0 < n := by simp [n]
    have hkerle : LinearMap.ker φ ≤ LinearMap.ker (φ ^ n) := by
      simpa using φ.iterateKer.monotone hnpos
    have hfker : LinearMap.ker φ = ⊥ :=
      le_antisymm (hkerle.trans_eq hker) bot_le
    have hfinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hfker
    have hfsurj : Function.Surjective φ :=
      (φ.restrictScalars k).surjective_of_injective hfinj
    apply (isUnit_map_iff (ModuleCat.endRingEquiv M) f).mp
    exact (Module.End.isUnit_iff φ).2 ⟨hfinj, hfsurj⟩
  · right
    have hrange : LinearMap.range (φ ^ n) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      let y : R := ⟨x, hx⟩
      haveI : Subsingleton R := ModuleCat.subsingleton_of_isZero hR
      exact congrArg Subtype.val (Subsingleton.elim y 0)
    refine ⟨n, ?_⟩
    apply (ModuleCat.endRingEquiv M).injective
    rw [map_pow, map_zero]
    exact LinearMap.range_eq_bot.mp hrange

/-- The categorical endomorphism ring of a finite-dimensional indecomposable
module is local.
@isnad1 id=islocalr.1h3v.s7.0c555994f3e1 from=translated src=- shape=b4c4bde6 vocab=fd295328
-/
theorem moduleCat_end_isLocalRing [Module.Finite k A]
    (M : ModuleCat.{v} A) [Module.Finite k M] (hM : Indecomposable M) :
    IsLocalRing (End M) := by
  have hnsub : ¬ Subsingleton M :=
    (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hM.1
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hnsub
  letI : Nontrivial (End M) :=
    (ModuleCat.endRingEquiv M).symm.injective.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  rcases isUnit_or_isNilpotent_of_finite_indecomposable
    (k := k) (A := A) M hM f with hf | hf
  · exact Or.inl hf
  · exact Or.inr hf.isUnit_one_sub

namespace RightModule.FiniteIndecomposableSkeleton

variable [FiniteDimensional k A]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The chosen skeleton object's endomorphism ring remains local after it is
bundled in the literal category of finitely generated right modules.
@isnad1 id=islocalr.0h4v.s7.96e18a45d1dd from=translated src=- shape=43f8ffde vocab=b026926d
-/
theorem fgObj_end_isLocalRing (i : Fin S.n) :
    IsLocalRing (End (S.fgObj i)) := by
  let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
    (RightModule.Category A)
  letI : U.Additive := ⟨by intros; rfl⟩
  letI : Module.Finite k Aᵐᵒᵖ := inferInstance
  letI : Module.Finite k (S.obj i) := S.obj_finite i
  letI : IsLocalRing (End (U.obj (S.fgObj i))) := by
    change IsLocalRing (End (S.obj i))
    exact moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖ)
      (S.obj i) (S.obj_indecomposable i)
  exact RingEquiv.isLocalRing_noncomm
    (CategoryTheory.Functor.endRingEquivOfFullyFaithful U (S.fgObj i)).symm

end RightModule.FiniteIndecomposableSkeleton

end MagnitudeConjecture
