import Tengoku.DgLean.DG.Category.Functor
import Tengoku.DgLean.DG.Module.Shift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Formal shifts of objects of a dg category

Let `C` be a dg category and `φ : ι → C × ℤ` a family of pairs `(Xᵢ, mᵢ)` of an object and an
integer. The dg category `DG.ShiftedObjects φ` has objects `ι`, and its Hom complexes are those of
`C`, regraded by the shifts: an element of `C(Xᵢ, Xⱼ)` of degree `n + mⱼ - mᵢ` is a morphism
`i ⟶ j` of degree `n`, and the differential is twisted by the sign of the shift of the target,

  `ShiftedObjects φ (i, j)ⁿ = C(Xᵢ, Xⱼ)^{n + mⱼ - mᵢ}`,  `d' f = (-1)^{mⱼ} d f`,

with the composition of `C`. The object `i` behaves as the formal shift `Xᵢ[mᵢ]`: the
representable module of `i` is the shift by `mᵢ` of the representable module of `Xᵢ` (up to the
usual signs), and for `C` the one-object dg category of a dg ring this is the dg category of the
shifted free modules `A[mᵢ]`. The sign of the differential is forced by the Leibniz rule of
`docs/CONVENTIONS.md`: for `f : i ⟶ j` and `g : j ⟶ l` homogeneous of degree `q` (so of degree
`q + mₗ - mⱼ` in `C`),
`(-1)^{mₗ} d (f ≫ g) = f ≫ (-1)^{mₗ} d g + (-1)^q ((-1)^{mⱼ} d f ≫ g)`.

## Main definitions

* `DG.ShiftedHom a b M`: a dg abelian group `M` regraded by `b - a` with differential
  `(-1)^b d` (the Hom complexes of `ShiftedObjects`).
* `DG.ShiftedObjects φ`, with `Category`, `Preadditive` and `DGCategory` instances.
* `DG.ShiftedObjects.reindexFunctor φ ψ : ShiftedObjects (φ ∘ ψ) ⥤ ShiftedObjects φ` for
  `ψ : κ → ι`, and `DG.ShiftedObjects.ofZeroFunctor φ s hs : C ⥤ ShiftedObjects φ` for a section
  `s` with `φ (s X) = (X, 0)`: dg functors which are the identity on Hom complexes.
* `DG.ShiftedObjects.mapFunctor F φ : ShiftedObjects φ ⥤ ShiftedObjects (F.obj ∘ φ)`: the dg
  functor induced by a dg functor `F : C ⥤ D`.
* `DG.ShiftedObjects.shiftHom`: the identity `𝟙 X` as a closed isomorphism of degree `m' - m`
  between objects with the same underlying object of `C` and shifts `m`, `m'`.
-/

open scoped DG

open CategoryTheory DirectSum

universe v u u'

namespace DG

/-! ### Regraded Hom complexes -/

/-- A dg abelian group `M` regraded for the Hom complexes of `DG.ShiftedObjects`: the component
of degree `n` is `M^{n + (b - a)}` and the differential is `(-1)^b d`.-/
def ShiftedHom (_a _b : ℤ) (M : Type*) : Type _ := M

namespace ShiftedHom

variable (a b : ℤ) (M : Type*) [AddCommGroup M]

instance : AddCommGroup (ShiftedHom a b M) := inferInstanceAs (AddCommGroup M)

/-- The identity `ShiftedHom a b M → M`, as an additive equivalence.-/
def val : ShiftedHom a b M ≃+ M := AddEquiv.refl M

variable [DGAddCommGroup M]

instance : DGAddCommGroup (ShiftedHom a b M) where
  grading n := grading (M := M) (n + (b - a))
  decomposition := Decomposition.reindex (grading (M := M)) (Equiv.addRight (b - a))
  d := (val a b M).symm.toAddMonoidHom.comp
    ((DistribSMul.toAddMonoidHom M (koszulSign b)).comp
      ((d : M →+ M).comp (val a b M).toAddMonoidHom))
  d_mem' {n m} hm := by
    have hm' : val a b M m ∈ grading (M := M) (n + (b - a)) := hm
    change koszulSign b • d (val a b M m) ∈ grading (M := M) (n + 1 + (b - a))
    rw [add_right_comm, Units.smul_def]
    exact zsmul_mem (d_mem hm') _
  d_d' m := by
    change koszulSign b • d (koszulSign b • d (val a b M m)) = 0
    rw [d_units_smul, d_d, smul_zero, smul_zero]

variable {a b M}

end ShiftedHom

/-! ### The dg category -/

/-- The dg category of formal shifts `Xᵢ[mᵢ]` of objects of a dg category, for a family
`φ : ι → C × ℤ`, `φ i = (Xᵢ, mᵢ)`: objects `ι`, Hom complexes
`(i ⟶ j)ⁿ = C(Xᵢ, Xⱼ)^{n + mⱼ - mᵢ}` with differential `(-1)^{mⱼ} d`.-/
@[ext]
structure ShiftedObjects {C : Type u} {ι : Type u'} (_φ : ι → C × ℤ) where
  /-- The index underlying an object.-/
  as : ι

namespace ShiftedObjects

variable {C : Type u} [Category.{v} C] {ι : Type u'} (φ : ι → C × ℤ)

instance category : Category.{v} (ShiftedObjects φ) where
  Hom i j := ShiftedHom (φ i.as).2 (φ j.as).2 ((φ i.as).1 ⟶ (φ j.as).1)
  id i := (𝟙 (φ i.as).1 : (φ i.as).1 ⟶ (φ i.as).1)
  comp {i j l} f g :=
    ((f : (φ i.as).1 ⟶ (φ j.as).1) ≫ (g : (φ j.as).1 ⟶ (φ l.as).1) : (φ i.as).1 ⟶ (φ l.as).1)
  id_comp _ := Category.id_comp (obj := C) _
  comp_id _ := Category.comp_id (obj := C) _
  assoc _ _ _ := Category.assoc (obj := C) _ _ _

variable {φ}

/-- A morphism of `C` as a morphism of `ShiftedObjects φ`.-/
def homMk {i j : ShiftedObjects φ} (f : (φ i.as).1 ⟶ (φ j.as).1) : i ⟶ j := f

/-- The morphism of `C` underlying a morphism of `ShiftedObjects φ`.-/
def homVal {i j : ShiftedObjects φ} (f : i ⟶ j) : (φ i.as).1 ⟶ (φ j.as).1 := f

/--
@isnad1 id=eq.0h6v.s6.d2af66bb10c8 from=translated src=- shape=6ebb13de vocab=3d43d84c
-/
@[simp] theorem homVal_homMk {i j : ShiftedObjects φ} (f : (φ i.as).1 ⟶ (φ j.as).1) :
    homVal (homMk (i := i) (j := j) f) = f := rfl

/--
@isnad1 id=eq.0h6v.s6.8d00d07a8eee from=translated src=- shape=864f8d98 vocab=9a7df32f
-/
@[simp] theorem homMk_homVal {i j : ShiftedObjects φ} (f : i ⟶ j) : homMk (homVal f) = f := rfl

/--
@isnad1 id=eq.1h7v.s7.5a348ef6ef24 from=translated src=- shape=b04a5dde vocab=ad373c03
-/
theorem hom_ext {i j : ShiftedObjects φ} {f g : i ⟶ j} (h : homVal f = homVal g) : f = g := h

/--
@isnad1 id=eq.0h4v.s6.ed113384eba9 from=translated src=- shape=a2112af8 vocab=dbe71782
-/
@[simp] theorem homVal_id (i : ShiftedObjects φ) : homVal (𝟙 i) = 𝟙 (φ i.as).1 := rfl

/--
@isnad1 id=eq.0h8v.s7.ba10bd95b502 from=translated src=- shape=a9b20c68 vocab=e551ca6e
-/
@[simp] theorem homVal_comp {i j l : ShiftedObjects φ} (f : i ⟶ j) (g : j ⟶ l) :
    homVal (f ≫ g) = homVal f ≫ homVal g := rfl

variable [Preadditive C]

instance (i j : ShiftedObjects φ) : AddCommGroup (i ⟶ j) :=
  inferInstanceAs (AddCommGroup (ShiftedHom (φ i.as).2 (φ j.as).2 ((φ i.as).1 ⟶ (φ j.as).1)))

/-- `homVal` as an additive equivalence.-/
def homValAddEquiv (i j : ShiftedObjects φ) : (i ⟶ j) ≃+ ((φ i.as).1 ⟶ (φ j.as).1) :=
  AddEquiv.refl _

/--
@isnad1 id=eq.0h7v.s9.446570f4d4e4 from=translated src=- shape=4fd02e3e vocab=9c29ae86
-/
@[simp] theorem homVal_add {i j : ShiftedObjects φ} (f g : i ⟶ j) :
    homVal (f + g) = homVal f + homVal g := rfl
/--
@isnad1 id=eq.0h5v.s8.ee29d963f028 from=translated src=- shape=455f2015 vocab=b9727d8a
-/
@[simp] theorem homVal_zero (i j : ShiftedObjects φ) : homVal (0 : i ⟶ j) = 0 := rfl
/--
@isnad1 id=eq.0h6v.s8.5fa52ad1b11b from=translated src=- shape=debe06bf vocab=137adfb3
-/
@[simp] theorem homVal_neg {i j : ShiftedObjects φ} (f : i ⟶ j) : homVal (-f) = -homVal f := rfl
/--
@isnad1 id=eq.0h7v.s8.719d4e50d188 from=translated src=- shape=4fd02e3e vocab=f54ae4c5
-/
@[simp] theorem homVal_sub {i j : ShiftedObjects φ} (f g : i ⟶ j) :
    homVal (f - g) = homVal f - homVal g := rfl
/--
@isnad1 id=eq.0h7v.s8.87c3b59f0746 from=translated src=- shape=39811657 vocab=a3766dae
-/
@[simp] theorem homVal_zsmul {i j : ShiftedObjects φ} (n : ℤ) (f : i ⟶ j) :
    homVal (n • f) = n • homVal f := rfl
/--
@isnad1 id=eq.0h7v.s9.7d455db61671 from=translated src=- shape=bd4b8107 vocab=0c8e51c9
-/
@[simp] theorem homVal_units_smul {i j : ShiftedObjects φ} (n : ℤˣ) (f : i ⟶ j) :
    homVal (n • f) = n • homVal f := rfl

/--
@isnad1 id=eq.0h7v.s9.98cc454638bb from=translated src=- shape=26632fe7 vocab=f7ce7cbe
-/
@[simp] theorem homMk_add {i j : ShiftedObjects φ} (f g : (φ i.as).1 ⟶ (φ j.as).1) :
    homMk (i := i) (j := j) (f + g) = homMk f + homMk g := rfl

instance preadditive : Preadditive (ShiftedObjects φ) where
  add_comp _ _ _ f f' g := hom_ext (by
    rw [homVal_comp, homVal_add, homVal_add, homVal_comp, homVal_comp]
    exact Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ f g g' := hom_ext (by
    rw [homVal_comp, homVal_add, homVal_add, homVal_comp, homVal_comp]
    exact Preadditive.comp_add _ _ _ _ _ _)

variable [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

instance instDGAddCommGroupHom (i j : ShiftedObjects φ) : DGAddCommGroup (i ⟶ j) :=
  inferInstanceAs
    (DGAddCommGroup (ShiftedHom (φ i.as).2 (φ j.as).2 ((φ i.as).1 ⟶ (φ j.as).1)))

/--
@isnad1 id=iff.0h7v.s9.f4b9cf6e99a2 from=translated src=- shape=8b6d8820 vocab=e0806284
-/
theorem mem_grading_iff {i j : ShiftedObjects φ} {n : ℤ} {f : i ⟶ j} :
    f ∈ grading n ↔ homVal f ∈ grading (n + ((φ j.as).2 - (φ i.as).2)) :=
  Iff.rfl

/--
@isnad1 id=eq.0h6v.s10.60fd6e88c3b6 from=translated src=- shape=1872d37b vocab=d33fe2b3
-/
theorem homVal_d {i j : ShiftedObjects φ} (f : i ⟶ j) :
    homVal (d f) = koszulSign (φ j.as).2 • d (homVal f) :=
  rfl

variable [DGCategory C]

/-! ### Functors -/

section Functors

variable (φ) in
/-- For `ψ : κ → ι`, the dg functor `ShiftedObjects (φ ∘ ψ) ⥤ ShiftedObjects φ`, `k ↦ ψ k`, the
identity on Hom complexes.-/
@[simps obj]
def reindexFunctor {κ : Type*} (ψ : κ → ι) : ShiftedObjects (φ ∘ ψ) ⥤ ShiftedObjects φ where
  obj k := ⟨ψ k.as⟩
  map f := homMk (homVal f)
  map_id _ := rfl
  map_comp _ _ := rfl

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] in
/--
@isnad1 id=eq.0h8v.s8.a004e73feecc from=translated src=- shape=730e009f vocab=d4af7535
-/
@[simp]
theorem homVal_reindexFunctor_map {κ : Type*} (ψ : κ → ι) {k l : ShiftedObjects (φ ∘ ψ)}
    (f : k ⟶ l) : homVal ((reindexFunctor φ ψ).map f) = homVal f :=
  rfl

variable (C) in
/-- The dg functor `C ⥤ ShiftedObjects (id : C × ℤ → C × ℤ)`, `X ↦ (X, 0)`, the identity on Hom
complexes.-/
@[simps obj]
def toClosure : C ⥤ ShiftedObjects (id : C × ℤ → C × ℤ) where
  obj X := ⟨(X, 0)⟩
  map f := homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] in
/--
@isnad1 id=eq.0h4v.s7.ce0a7298ec12 from=translated src=- shape=17cb31b3 vocab=93615dc3
-/
@[simp]
theorem homVal_toClosure_map {X Y : C} (f : X ⟶ Y) : homVal ((toClosure C).map f) = f :=
  rfl

/-- The dg functor `ShiftedObjects φ ⥤ ShiftedObjects (Prod.map F.obj id ∘ φ)`, `(X, m) ↦ (F X, m)`,
induced by a dg functor `F : C ⥤ D`.-/
@[simps obj]
def mapFunctor {D : Type*} [Category D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
    (F : C ⥤ D) (φ : ι → C × ℤ) :
    ShiftedObjects φ ⥤ ShiftedObjects (Prod.map F.obj id ∘ φ) where
  obj i := ⟨i.as⟩
  map f := homMk (F.map (homVal f))
  map_id _ := F.map_id _
  map_comp _ _ := F.map_comp _ _

section MapFunctor

variable {D : Type*} [Category D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] [F.Additive]
  [F.IsDGFunctor] in
/--
@isnad1 id=eq.0h8v.s9.999cefcd4275 from=translated src=- shape=618b5400 vocab=151e5192
-/
@[simp]
theorem homVal_mapFunctor_map {i j : ShiftedObjects φ} (f : i ⟶ j) :
    homVal ((mapFunctor F φ).map f) = F.map (homVal f) :=
  rfl

end MapFunctor

/-! ### Shifting an object -/

/-- The identity of `X` as a morphism `i ⟶ j` of `ShiftedObjects φ` between objects with the same
underlying object `X` of `C`; it is a cocycle of degree `mᵢ - mⱼ`.-/
def shiftHom {i j : ShiftedObjects φ} (h : (φ i.as).1 = (φ j.as).1) : i ⟶ j :=
  homMk (eqToHom h)

end Functors

end ShiftedObjects

end DG
