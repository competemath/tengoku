import Tengoku.DgLean.DG.Algebra.Hom
import Tengoku.DgLean.DG.Module.Cohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functoriality of the cohomology ring

For a morphism of dg rings `f : A →ᵈᵍ+* B`, the maps `Hⁿ(f) : Hⁿ(A) → Hⁿ(B)` are compatible with
the graded products, so that they assemble to a morphism of dg rings `H(f) : H(A) → H(B)` of the
cohomology rings (`DG.Cohomology A`, with zero differential).

* `DG.DGRingHom.cohomologyMap f n`: the map `Hⁿ(A) →+ Hⁿ(B)` (the map of `DG.cohomology`
  induced by the underlying chain map), with `cohomologyMap_one`, `cohomologyMap_mul`.
* `DG.DGRingHom.cohomologyRingMap f`: the morphism of dg rings `H(A) →ᵈᵍ+* H(B)`; identity and
  composition.
* `DG.DGRingHom.IsQuasiIso f`: `f` induces isomorphisms on all cohomology groups.
-/

open scoped DG

open DirectSum GradedMonoid

namespace DG

namespace DGRingHom

variable {A B C : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [Ring C] [DGAddCommGroup C] (f : A →ᵈᵍ+* B)

/-- The map on cocycles induced by a morphism of dg rings.-/
def cocyclesMap (n : ℤ) : cocycles A n →+ cocycles B n :=
  cocycles.mapAddMonoidHom f.toRingHom.toAddMonoidHom (fun ha => f.map_mem ha) f.map_d n

/--
@isnad1 id=eq.0h5v.s10.c341d2e02466 from=translated src=- shape=a23f1407 vocab=7031c84f
-/
@[simp]
theorem coe_cocyclesMap (n : ℤ) (a : cocycles A n) : (f.cocyclesMap n a : B) = f a := rfl

/-- The map `Hⁿ(A) → Hⁿ(B)` induced by a morphism of dg rings.-/
def cohomologyMap (n : ℤ) : cohomology A n →+ cohomology B n :=
  cohomology.mapAddMonoidHom f.toRingHom.toAddMonoidHom (fun ha => f.map_mem ha) f.map_d n

/--
@isnad1 id=eq.0h5v.s11.5527c4ee132f from=translated src=- shape=d5360073 vocab=2841e187
-/
@[simp]
theorem cohomologyMap_mk (n : ℤ) (a : cocycles A n) :
    f.cohomologyMap n (cohomology.mk A n a) = cohomology.mk B n (f.cocyclesMap n a) :=
  cohomology.mapAddMonoidHom_mk _ _ _ n a

/--
@isnad1 id=eq.2h5v.s8.162f84f0b05c from=translated src=- shape=a8d5c2b2 vocab=5456981c
-/
theorem cohomologyMap_mkOf {n : ℤ} {a : A} (ha : a ∈ grading n) (hd : d a = 0) :
    f.cohomologyMap n (cohomology.mkOf ha hd) =
      cohomology.mkOf (f.map_mem ha) (by rw [← f.map_d, hd, map_zero]) :=
  cohomology.mapAddMonoidHom_mkOf _ _ _ ha hd

variable (A) in
/--
@isnad1 id=eq.0h2v.s7.f9caee3c9c3b from=translated src=- shape=83bb3c2a vocab=d1ae2f48
-/
theorem cohomologyMap_id (n : ℤ) :
    (DGRingHom.id : A →ᵈᵍ+* A).cohomologyMap n = AddMonoidHom.id _ := by
  ext a
  rfl

/--
@isnad1 id=eq.0h6v.s8.7ee74bd73378 from=translated src=- shape=126104f1 vocab=3d2a110d
-/
theorem cohomologyMap_comp (g : B →ᵈᵍ+* C) (n : ℤ) :
    (g.comp f).cohomologyMap n = (g.cohomologyMap n).comp (f.cohomologyMap n) := by
  ext a
  rfl

/-- A morphism of dg rings is a quasi-isomorphism if it induces isomorphisms on all cohomology
groups.-/
def IsQuasiIso : Prop :=
  ∀ n : ℤ, Function.Bijective (f.cohomologyMap n)

variable (A) in
/--
@isnad1 id=isquasii.0h1v.s4.6f9657338a5a from=translated src=- shape=ac0af42f vocab=e72d5927
-/
theorem isQuasiIso_id : IsQuasiIso (DGRingHom.id : A →ᵈᵍ+* A) := fun n => by
  rw [cohomologyMap_id]
  exact Function.bijective_id

/--
@isnad1 id=isquasii.2h5v.s6.688590c58ed3 from=translated src=- shape=30de51f9 vocab=c1e2198a
-/
theorem IsQuasiIso.comp {g : B →ᵈᵍ+* C} {f : A →ᵈᵍ+* B} (hg : IsQuasiIso g) (hf : IsQuasiIso f) :
    IsQuasiIso (g.comp f) := fun n => by
  rw [cohomologyMap_comp]
  exact (hg n).comp (hf n)

variable [DGRing A] [DGRing B] [DGRing C]

/--
@isnad1 id=eq.0h3v.s8.3b72544326ef from=translated src=- shape=9fa84e1a vocab=b324aeb9
-/
theorem cohomologyMap_one : f.cohomologyMap 0 GOne.one = GOne.one := by
  rw [Cohomology.one_def, cohomologyMap_mk]
  exact congrArg (cohomology.mk B 0) (Subtype.ext (map_one f))

/--
@isnad1 id=eq.0h7v.s10.9edfe565c2e4 from=translated src=- shape=b1c99809 vocab=88a77ea5
-/
theorem cohomologyMap_mul {i j : ℤ} (x : cohomology A i) (y : cohomology A j) :
    f.cohomologyMap (i + j) (GMul.mul x y) =
      GMul.mul (f.cohomologyMap i x) (f.cohomologyMap j y) := by
  induction x using cohomology.induction_on with
  | h a =>
  induction y using cohomology.induction_on with
  | h b =>
    rw [Cohomology.mk_mul_mk, cohomologyMap_mk, cohomologyMap_mk, cohomologyMap_mk,
      Cohomology.mk_mul_mk]
    exact congrArg (cohomology.mk B (i + j)) (Subtype.ext (by simp))

/-- The ring homomorphism `H(A) →+* H(B)` induced by a morphism of dg rings `A → B`; see
`DGRingHom.cohomologyRingMap` for the morphism of dg rings.-/
def cohomologyRingHom : Cohomology A →+* Cohomology B :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (fun n => cohomology B n) n).comp (f.cohomologyMap n))
    (by rw [AddMonoidHom.comp_apply, cohomologyMap_one]; rfl)
    (fun {i j} x y => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        cohomologyMap_mul, DirectSum.of_mul_of])

/--
@isnad1 id=eq.0h5v.s10.0147edf0f2b7 from=translated src=- shape=a18b01fe vocab=89f4672b
-/
@[simp]
theorem cohomologyRingHom_of (n : ℤ) (x : cohomology A n) :
    f.cohomologyRingHom (DirectSum.of (fun n => cohomology A n) n x) =
      DirectSum.of (fun n => cohomology B n) n (f.cohomologyMap n x) :=
  DirectSum.toSemiring_of _ _ _ n x

/-- The morphism of dg rings `H(A) → H(B)` induced by a morphism of dg rings `A → B`.-/
def cohomologyRingMap : Cohomology A →ᵈᵍ+* Cohomology B where
  __ := f.cohomologyRingHom
  map_mem' := by
    rintro n _ ⟨x, rfl⟩
    exact ⟨f.cohomologyMap n x, (f.cohomologyRingHom_of n x).symm⟩
  map_d' _ := by simp

/--
@isnad1 id=eq.0h5v.s10.1e38445e8a9b from=translated src=- shape=dbdc707b vocab=f46efab6
-/
@[simp]
theorem cohomologyRingMap_of (n : ℤ) (x : cohomology A n) :
    f.cohomologyRingMap (DirectSum.of (fun n => cohomology A n) n x) =
      DirectSum.of (fun n => cohomology B n) n (f.cohomologyMap n x) :=
  f.cohomologyRingHom_of n x

end DGRingHom

end DG
